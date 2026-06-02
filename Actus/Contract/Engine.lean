/-
## Schedule generation & shared execution engine

`genSchedule` builds the event `Schedule` from a contract's dictionary terms;
`runSchedule` (Actus.Execution) threads a contract's `stf`/`pof` over it.  This module is the type-agnostic core: schedule generation and the shared
cash-flow helpers.  Each contract family's executable cash-flow builders live in
its own module (`Lending`, `Position`, `Derivative`, `Swap`, `CreditEnh`, …).
-/

import Actus.Protocol
import Actus.Execution
import Actus.Util.Schedule
import Actus.Contract.Common

namespace Actus.Contract.Execution

open Actus.Protocol
open Actus.Util
open Actus.Contract

/-- Map a calendar date to the `Time` axis. -/
def toTime (d : LocalTime) : Time := Schedule.toTime d

/-- Cyclic schedule for one event family, as `Time`s.

    * no cycle and no anchor ⇒ the event is not scheduled (`[]`);
    * no cycle but an explicit anchor ⇒ a single occurrence at the anchor;
    * a cycle ⇒ the cyclic times up to `md`, with the anchor defaulting to
      `IED + cycle` when not given. -/

def cyclicTimes (cfg : ScheduleConfig) (anchor : Option LocalTime)
    (cyc : Option Cycle) (ied md : Option LocalTime) (includeEnd : Bool := true) :
    List Time :=
  match cyc with
  | none =>
    match anchor with
    | some a => [toTime a]
    | none   => []
  | some c =>
    let start? : Option LocalTime :=
      match anchor with
      | some a => some a
      | none   => ied.map (fun i => Date.addCycle i c)
    match start?, md with
    | some a, some tEnd => (Schedule.schedule cfg a (some c) tEnd includeEnd).map toTime
    | _, _ => []

/-- Maturity date: the explicit `maturityDate`, or — for amortizers that omit it
    — the redemption-count-derived `t⁻ + ⌈NT/PRNXT⌉·PRCL` (§7.2 `Md` init),
    where `t⁻` is the principal-redemption anchor (or `IED + PRCL`).  This is the
    LAM formula; NAM/ANN's interest-adjusted period count is approximated by it. -/
def maturityOf (ct : Terms Float) : Option LocalTime :=
  match ct.maturityDate with
  | some d => some d
  | none =>
  match ct.amortizationDate with    -- ANN amortizes to AMD when MD is absent
  | some d => some d
  | none =>
    match ct.cycleOfPrincipalRedemption, ct.notionalPrincipal,
          ct.nextPrincipalRedemptionPayment with
    | some c, some nt, some prnxt =>
      if prnxt == 0.0 then none
      else
        let tMinus :=
          match ct.cycleAnchorDateOfPrincipalRedemption with
          | some a => some a
          | none   => ct.initialExchangeDate.map (Date.addCycle · c)
        tMinus.map fun t0 =>
          -- k redemptions clear the notional; the last falls at
          -- anchor + (k-1)·PRCL, which is the maturity date.  For NAM the
          -- instalment pays interest first, so each period reduces principal by
          -- only `PRNXT − NT·Y·IPNR` → more periods (§7.4).  Apply the same
          -- EOM/BDC conventions the schedule uses.
          let firstYf := yf ct (toTime t0) (toTime (Date.addCycle t0 c))
          let ipnr    := ct.nominalInterestRate.getD 0.0
          let denom   := match ct.contractType with
            -- NAM/ANN instalments pay interest first, so each period reduces
            -- principal by only `PRNXT − NT·Y·IPNR` ⇒ more periods (§7.4/7.5).
            | .NAM | .ANN => Float.abs prnxt - Float.abs nt * firstYf * Float.abs ipnr
            | _           => Float.abs prnxt
          let k := (Float.ceil (Float.abs nt / denom)).toUInt64.toNat
          let raw := Date.addPeriod t0 ((k - 1) * c.n) c.period
          Conventions.applyConventions ct.scheduleConfig t0
            (Date.monthsOfUnit c.period).isSome raw
    | _, _, _ => none

/-- Build the full event schedule for a lending contract.  `includePR` adds the
    principal-redemption cycle (LAM/NAM/ANN).  `mEOD`/`tEOD` mark the maturity /
    termination as end-of-day (`23:59:59`): the structure uses the written date,
    but those settlement events are rolled to the next midnight. -/
def genSchedule (ct : Terms Float) (includePR : Bool)
    (mEOD : Bool := false) (tEOD : Bool := false) : Schedule :=
  let cfg := ct.scheduleConfig
  let ied := ct.initialExchangeDate
  let md  := maturityOf ct
  let single (d : Option LocalTime) (e : EventType) : List Event :=
    (d.map (fun x => [(toTime x, e)])).getD []
  let cyclic (anchor : Option LocalTime) (cyc : Option Cycle) (e : EventType)
      (incEnd : Bool := true) : List Event :=
    (cyclicTimes cfg anchor cyc ied md incEnd).map (fun t => (t, e))
  -- Rate resets: when `nextResetRate` (RRNXT) is set, the first reset is a
  -- *fixed* reset `RRF` using RRNXT; the rest are market-driven `RR` (§7.1).
  let rrEvents : List Event :=
    let ts := cyclicTimes cfg ct.cycleAnchorDateOfRateReset ct.cycleOfRateReset ied md
    match ct.nextResetRate, ts with
    | some _, first :: rest => (first, .RRF) :: rest.map (fun t => (t, .RR))
    | _,      _             => ts.map (fun t => (t, .RR))
  -- Interest: cycle dates up to the capitalization end date (`IPCED`) capitalize
  -- (`IPCI`: interest is added to the notional, no cash); later dates pay (`IP`).
  let ipTimes := cyclicTimes cfg ct.cycleAnchorDateOfInterestPayment
                   ct.cycleOfInterestPayment ied md
  let ipEvents : List Event :=
    match ct.capitalizationEndDate with
    | some ipced =>
      let c := toTime ipced
      let capit := ipTimes.filter (fun t => Nat.ble t c)
      let capit := if capit.contains c then capit else capit ++ [c]
      let pay   := ipTimes.filter (fun t => Nat.blt c t)
      capit.map (fun t => (t, .IPCI)) ++ pay.map (fun t => (t, .IP))
    | none => ipTimes.map (fun t => (t, .IP))
  let events : List Event :=
    single ied .IED ++
    single md  .MD ++
    single ct.purchaseDate .PRD ++       -- purchase: buyer acquires the contract
    single ct.terminationDate .TD ++     -- termination: contract sold/closed early
    ipEvents ++
    cyclic ct.cycleAnchorDateOfFee ct.cycleOfFee .FP ++
    -- interest-calculation-base fixings re-set Ipcb to the current notional;
    -- like PR, the schedule excludes the maturity endpoint (so the long-stub
    -- merge applies and there is no fixing at maturity)
    cyclic ct.cycleAnchorDateOfInterestCalculationBase
      ct.cycleOfInterestCalculationBase .IPCB false ++
    -- scaling-index fixings update Nsc/Isc
    cyclic ct.cycleAnchorDateOfScalingIndex ct.cycleOfScalingIndex .SC ++
    rrEvents ++
    -- Principal redemption excludes the maturity endpoint: `S(s,PRCL,T^MD,F)`
    -- (§7.2).  The remaining principal is cleared by the MD event instead.
    (if includePR then
        cyclic ct.cycleAnchorDateOfPrincipalRedemption ct.cycleOfPrincipalRedemption .PR false
     else [])
  -- termination ends the contract: drop everything after the termination date.
  let events := match ct.terminationDate with
    | some td => let tdT := toTime td; events.filter (fun (e : Event) => Nat.ble e.1 tdT)
    | none    => events
  -- events before the status date are historical (their effect is in the init
  -- state); the analysis — and the first interest accrual — starts at SD.
  let events := let sdT := toTime ct.statusDate; events.filter (fun (e : Event) => Nat.ble sdT e.1)
  -- end-of-day roll: maturity events (all at MD) and the TD event move to the
  -- next midnight; the schedule structure above kept the written date.
  let events := if mEOD then
      match md.map toTime with
      | some mdT => events.map fun e => if e.1 == mdT then (mdT + 1, e.2) else e
      | none     => events
    else events
  let events := if tEOD then
      match ct.terminationDate.map toTime with
      | some tdT => events.map fun e =>
          if e.1 == tdT && eventTypePriority e.2 == eventTypePriority .TD
          then (tdT + 1, e.2) else e
      | none     => events
    else events
  -- order by event time, breaking ties by event-type priority
  let lt := fun (a b : Event) =>
    if a.1 == b.1 then Nat.blt (eventTypePriority a.2) (eventTypePriority b.2)
    else Nat.blt a.1 b.1
  (events.toArray.qsort lt).toList

/-- Maturity date on the `Time` axis (0 if it cannot be determined). -/
def mdTime (ct : Terms Float) : Time := ((maturityOf ct).map toTime).getD 0

/-- Status date on the `Time` axis. -/
def sdTime (ct : Terms Float) : Time := toTime ct.statusDate

/-- Stamp each cash flow on its business-day settlement date.  For `CS*`
    conventions the schedule (and hence all accruals) used the unshifted date;
    this applies the deferred shift to the event timestamp only.  Identity for
    `SC*`/`NULL`. -/
def remapSettlement (cfg : ScheduleConfig) (cfs : Cashflows) : Cashflows :=
  cfs.map fun ((t, e), p) =>
    ((toTime (Conventions.settlementDate cfg (Date.ofEpochDay t)), e), p)

/-- When the contract is purchased mid-life, the analyzing party's cash flows
    start at the purchase date: drop everything strictly before it (the state
    still evolved through those events, but they belong to the seller). -/
def afterPurchase (ct : Terms Float) (cfs : Cashflows) : Cashflows :=
  match ct.purchaseDate with
  | some pd =>
    let p := toTime pd
    -- keep events strictly after purchase, plus the PRD event itself; any other
    -- event coinciding with the purchase date is folded into the clean price.
    cfs.filter fun ((t, e), _) =>
      Nat.blt p t || (t == p && eventTypePriority e == eventTypePriority .PRD)
  | none    => cfs

/-- Number of `PR` events in a schedule. -/
def numPR (sched : Schedule) : Nat :=
  sched.countP fun e => eventTypePriority e.2 == eventTypePriority .PR

/-- Shift a date onto a business day per the contract's business-day convention
    and calendar (identity when no convention is set). -/
def bdcShift (cfg : ScheduleConfig) (d : LocalTime) : LocalTime :=
  match cfg.businessDayConvention with
  | some bdc => Conventions.applyBDC bdc cfg.calendar d
  | none     => d

/-- Order a cashflow list by (time, event-type priority). -/
def sortCF (cfs : Cashflows) : Cashflows :=
  let lt := fun (a b : Cashflow) =>
    if a.1.1 == b.1.1 then Nat.blt (eventTypePriority a.1.2) (eventTypePriority b.1.2)
    else Nat.blt a.1.1 b.1.1
  (cfs.toArray.qsort lt).toList

end Actus.Contract.Execution
