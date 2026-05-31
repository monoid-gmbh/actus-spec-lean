/-
## Schedule generation & end-to-end execution (lending family)

`genSchedule` builds the event `Schedule` for a PAM/LAM/NAM/ANN contract from
its dictionary terms, following the Contract-Schedule tables (§7.1–7.5):

* `IED` at the initial exchange date, `MD` at maturity;
* cyclic `IP` (interest), `FP` (fee), `RR` (rate reset) schedules; and
* a cyclic `PR` (principal redemption) schedule for the amortizers
  (`includePR`).

Cyclic anchors default to `IED + cycle` when the explicit anchor is absent, per
the tables.  Times are produced with EOM/BDC conventions applied (via
`Util.Schedule`), mapped onto the `Time` axis, then ordered by
`(time, eventTypePriority)`.

`genCashflows` then runs a contract's functional `stf`/`pof` over that schedule
with `Execution.runSchedule`, giving the full executable pipeline.
-/

import Actus.Protocol
import Actus.Execution
import Actus.Util.Schedule
import Actus.Contract.Common
import Actus.Contract.PAM
import Actus.Contract.LAM
import Actus.Contract.NAM
import Actus.Contract.ANN
import Actus.Contract.CLM

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
            | .NAM => Float.abs prnxt - Float.abs nt * firstYf * Float.abs ipnr
            | _    => Float.abs prnxt
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

-- ---------------------------------------------------------------------------
-- End-to-end cashflow generation, per contract
-- ---------------------------------------------------------------------------

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

def pamCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }   -- supply the day-count year fraction
  remapSettlement ct.scheduleConfig <| afterPurchase ct <|
    Execution.runSchedule (PAM.stf ct rf) (PAM.pof ct rf)
      (PAM.init ct (mdTime ct) (sdTime ct)) (genSchedule ct false rf.maturityEOD rf.terminationEOD)

/-- Number of `PR` events in a schedule. -/
private def numPR (sched : Schedule) : Nat :=
  sched.countP fun e => eventTypePriority e.2 == eventTypePriority .PR

/-- Initial LAM state.  Applies the contract-role sign to `Prnxt`, and when
    `PRNXT` is absent sizes the linear instalment as `NT / (#PR + 1)` (the `+1`
    for the maturity redemption). -/
def lamInit (ct : Terms Float) : State Float :=
  let s0   := LAM.init ct (mdTime ct) (sdTime ct)
  let base := match ct.nextPrincipalRedemptionPayment with
    | some _ => Terms.prnxt ct
    | none   => Terms.nt ct / Float.ofNat (numPR (genSchedule ct true) + 1)
  { s0 with prnxt := Conventions.sign (Terms.cntrl ct) * base }

def lamCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }
  remapSettlement ct.scheduleConfig <| afterPurchase ct <|
    Execution.runSchedule (LAM.stf ct rf) (LAM.pof ct rf)
      (lamInit ct) (genSchedule ct true rf.maturityEOD rf.terminationEOD)

def namCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }
  remapSettlement ct.scheduleConfig <| afterPurchase ct <|
    Execution.runSchedule (NAM.stf ct rf) (NAM.pof ct rf)
      (NAM.init ct (mdTime ct) (sdTime ct)) (genSchedule ct true rf.maturityEOD rf.terminationEOD)

/-- The annuity amortization horizon: the `amortizationDate` if given, else the
    maturity.  The instalment amortizes to here even when an earlier
    `maturityDate` ends the contract with a balloon. -/
def annHorizon (ct : Terms Float) : Option LocalTime :=
  ct.amortizationDate.orElse fun _ => maturityOf ct

def annHorizonT (ct : Terms Float) : Time := ((annHorizon ct).map toTime).getD (mdTime ct)

def annInit (ct : Terms Float) (rf : RiskFactorEnv Float) : State Float :=
  let s0 := ANN.init ct (mdTime ct) (sdTime ct)
  match ct.nextPrincipalRedemptionPayment with
  | some _ => s0
  | none =>
    let prTimes := cyclicTimes ct.scheduleConfig ct.cycleAnchorDateOfPrincipalRedemption
                     ct.cycleOfPrincipalRedemption ct.initialExchangeDate (annHorizon ct) false
    -- Notional at the start of redemption: run the events before the first PR
    -- (`IED`, any `IPCI` capitalizations) so the annuity amortizes the *grown*
    -- notional rather than `NT`.
    let sched   := genSchedule ct true
    let firstPR := ((sched.find? fun e => eventTypePriority e.2 == eventTypePriority .PR).map
                     (·.1)).getD (annHorizonT ct)
    let grown   := (sched.filter fun e => Nat.blt e.1 firstPR).foldl
      (fun s (e : Event) => ANN.stf ct rf e.2 e.1 s) s0
    -- the annuity's first period runs from one redemption cycle before the
    -- first redemption (PRANX − PRCL), but never before IED.
    let iedT  := (ct.initialExchangeDate.map toTime).getD (sdTime ct)
    let first := match ct.cycleAnchorDateOfPrincipalRedemption,
                       ct.cycleOfPrincipalRedemption with
      | some a, some c => Nat.max iedT (toTime (Date.subPeriod a c.n c.period))
      | _, _           => iedT
    -- the annuity amortizes to the horizon; an end-of-day amortization date
    -- extends the final period to the next midnight.
    let horizonT := annHorizonT ct + (if rf.maturityEOD then 1 else 0)
    let bounds := (first :: prTimes) ++ [horizonT]
    let yfs    := (bounds.zip bounds.tail).map fun p => yf ct p.1 p.2
    let a      := Conventions.sign (Terms.cntrl ct) *
                    Schedule.annuity (Float.abs grown.nt) (Float.abs grown.ipac) (Terms.ipnr ct) yfs
    { s0 with prnxt := a }

/-- ANN execution runner: like `runSchedule`, but after each rate reset
    (`RR`/`RRF`) it re-amortizes — recomputing `Prnxt` as the annuity over the
    *remaining* redemption schedule (the `PR` dates after the reset, then `MD`)
    at the new rate, so total instalments stay constant within each rate regime. -/
def annRun (ct : Terms Float) (rf : RiskFactorEnv Float) (mdT : Time) :
    State Float → Schedule → Cashflows
  | _, []             => []
  | s, (t, e) :: rest =>
    let cf : Cashflow := ((t, e), ANN.pof ct rf e t s)
    let s' := ANN.stf ct rf e t s
    let s'' :=
      if eventTypePriority e == eventTypePriority .RR
         || eventTypePriority e == eventTypePriority .RRF then
        let prRem := rest.filterMap fun ev =>
          if eventTypePriority ev.2 == eventTypePriority .PR then some ev.1 else none
        let bounds := (t :: prRem) ++ [mdT]
        let yfs    := (bounds.zip bounds.tail).map fun p => yf ct p.1 p.2
        -- amortize the *magnitude* then re-apply the contract-role sign (as in
        -- `annInit`); using the already-signed `s'.nt` would double the sign and
        -- flip `Prnxt` for a liability (RPL) leg.
        { s' with prnxt := Conventions.sign (Terms.cntrl ct) *
                    Schedule.annuity (Float.abs s'.nt) (Float.abs s'.ipac) s'.ipnr yfs }
      else s'
    cf :: annRun ct rf mdT s'' rest

def annCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }
  remapSettlement ct.scheduleConfig <| afterPurchase ct <|
    annRun ct rf (annHorizonT ct) (annInit ct rf) (genSchedule ct true rf.maturityEOD rf.terminationEOD)

-- ---------------------------------------------------------------------------
-- CLM — Call Money: PAM transitions, but interest capitalizes (IPCI) on the
-- interest cycle until maturity, where a final IP (stub) is paid and the grown
-- principal redeemed (MD).  (Open-maturity / call cases — XD/STD — TODO.)
-- ---------------------------------------------------------------------------

/-- CLM event schedule for a defined-maturity contract: IED, interest-cycle
    `IPCI` strictly before MD, rate resets, then the final `IP` and `MD` at
    maturity. -/
def genScheduleCLM (ct : Terms Float) (mEOD : Bool := false) : Schedule :=
  let cfg := ct.scheduleConfig
  let ied := ct.initialExchangeDate
  match ct.maturityDate with
  | none        => []   -- open-maturity (call) CLM not yet handled
  | some mdDate =>
    let md  := some mdDate
    let mdT := toTime mdDate
    let single (d : Option LocalTime) (e : EventType) : List Event :=
      (d.map (fun x => [(toTime x, e)])).getD []
    -- interest-cycle points; those strictly before maturity capitalize (IPCI)
    let ipciEvents : List Event :=
      (cyclicTimes cfg ct.cycleAnchorDateOfInterestPayment ct.cycleOfInterestPayment ied md false
        |>.filter (fun t => Nat.blt t mdT)).map (fun t => (t, EventType.IPCI))
    -- rate resets strictly before maturity (first is RRF when RRNXT is set)
    let rrEvents : List Event :=
      let ts := (cyclicTimes cfg ct.cycleAnchorDateOfRateReset ct.cycleOfRateReset ied md false
        |>.filter (fun t => Nat.blt t mdT))
      match ct.nextResetRate, ts with
      | some _, first :: rest => (first, .RRF) :: rest.map (fun t => (t, .RR))
      | _,      _             => ts.map (fun t => (t, .RR))
    let events : List Event :=
      single ied .IED ++ ipciEvents ++ rrEvents ++ [(mdT, EventType.IP), (mdT, EventType.MD)]
    -- keep only events strictly after the status date (the initial exchange at
    -- the status date is historical — already reflected in the init state)
    let events := let sdT := toTime ct.statusDate; events.filter (fun (e : Event) => Nat.blt sdT e.1)
    -- end-of-day roll of the maturity events
    let events := if mEOD then events.map (fun e => if e.1 == mdT then (mdT + 1, e.2) else e) else events
    let lt := fun (a b : Event) =>
      if a.1 == b.1 then Nat.blt (eventTypePriority a.2) (eventTypePriority b.2)
      else Nat.blt a.1 b.1
    (events.toArray.qsort lt).toList

def clmCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }
  remapSettlement ct.scheduleConfig <| afterPurchase ct <|
    Execution.runSchedule (CLM.stf ct rf) (CLM.pof ct rf)
      (CLM.init ct (mdTime ct) (sdTime ct)) (genScheduleCLM ct rf.maturityEOD)

-- ---------------------------------------------------------------------------
-- COM (Commodity) / STK (Stock) — position contracts: buy (PRD), sell (TD),
-- and, for STK, dividends (DV) from the observed dividend stream.
-- ---------------------------------------------------------------------------

/-- Shift a date onto a business day per the contract's business-day convention
    and calendar (identity when no convention is set). -/
private def bdcShift (cfg : ScheduleConfig) (d : LocalTime) : LocalTime :=
  match cfg.businessDayConvention with
  | some bdc => Conventions.applyBDC bdc cfg.calendar d
  | none     => d

/-- Order a cashflow list by (time, event-type priority). -/
private def sortCF (cfs : Cashflows) : Cashflows :=
  let lt := fun (a b : Cashflow) =>
    if a.1.1 == b.1.1 then Nat.blt (eventTypePriority a.1.2) (eventTypePriority b.1.2)
    else Nat.blt a.1.1 b.1.1
  (cfs.toArray.qsort lt).toList

/-- COM: a commodity position.  Purchase pays `−R·quantity·priceAtPurchase`;
    termination receives `R·quantity·priceAtTermination`. -/
def comCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let s   := Conventions.sign (α := Float) ct.contractRole
  let qty := ct.quantity.getD 0
  let tdRoll := if rf.terminationEOD then 1 else 0   -- 23:59:59 settles next midnight
  let prd := (ct.purchaseDate.map fun d =>
                [((toTime d, EventType.PRD), -s * qty * Terms.pprd ct)]).getD []
  let td  := (ct.terminationDate.map fun d =>
                [((toTime d + tdRoll, EventType.TD), s * qty * Terms.ptd ct)]).getD []
  let sdT := toTime ct.statusDate
  sortCF ((prd ++ td).filter (fun c => Nat.ble sdT c.1.1))

/-- STK: an equity position.  Purchase pays `−R·priceAtPurchase`; termination
    receives `R·priceAtTermination`; each observed dividend pays `R·amount`. -/
def stkCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let s   := Conventions.sign (α := Float) ct.contractRole
  let prd := (ct.purchaseDate.map fun d =>
                [((toTime d, EventType.PRD), -s * Terms.pprd ct)]).getD []
  let td  := (ct.terminationDate.map fun d =>
                [((toTime d + (if rf.terminationEOD then 1 else 0), EventType.TD), s * Terms.ptd ct)]).getD []
  let dv  := rf.dividends.map fun (t, v) =>
               ((toTime (bdcShift ct.scheduleConfig (Date.ofEpochDay t)), EventType.DV), s * v)
  let sdT := toTime ct.statusDate
  sortCF ((prd ++ dv ++ td).filter (fun c => Nat.ble sdT c.1.1))

/-- OPTNS — a European, cash-settled option on an underlying.  Premium paid at
    `PRD`; at maturity the intrinsic value settles (`STD`): `max(S−K, 0)` for a
    call, `max(K−S, 0)` for a put, where `S` is the underlying's observed price
    (the `UDL` market-object code) at maturity and `K = optionStrike1`.  The
    zero-valued `MD`/`XD` markers are dropped by the cash filter. -/
def optnsCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let s   := Conventions.sign (α := Float) ct.contractRole
  let prd := (ct.purchaseDate.map fun d =>
                [((toTime d, EventType.PRD), -s * Terms.pprd ct)]).getD []
  let std := match ct.maturityDate with
    | none    => []
    | some md =>
      let mdT := toTime md
      let k   := ct.optionStrike1.getD 0
      let moc := (ct.contractStructure.getD []).findSome? fun
        | .mk (.referenceId m) .UDL _ => some m
        | _                            => none
      let sT  := match moc with | some m => rf.marketRateOf m mdT | none => 0
      let intrinsic := match ct.optionType with
        | some "P" => max (k - sT) 0      -- put
        | _        => max (sT - k) 0      -- call (default)
      -- settlement happens `settlementPeriod` after exercise/maturity
      let stdT := match ct.settlementPeriod with
        | some c => toTime (bdcShift ct.scheduleConfig (Date.addPeriod md c.n c.period))
        | none   => mdT
      [((stdT, EventType.STD), s * intrinsic)]
  let sdT := toTime ct.statusDate
  sortCF ((prd ++ std).filter (fun c => Nat.ble sdT c.1.1))

/-- FUTUR — a cash-settled future on an underlying.  Premium/price paid at
    `PRD`; at maturity the linear payoff settles (`STD`): `sign·(S − F)`, where
    `S` is the underlying's observed price (the `UDL` market-object code) at
    maturity and `F = futuresPrice`.  Like OPTNS but with a linear (not
    max-clamped) payoff; settlement honours `settlementPeriod` + the BDC. -/
def futurCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let s   := Conventions.sign (α := Float) ct.contractRole
  let prd := (ct.purchaseDate.map fun d =>
                [((toTime d, EventType.PRD), -s * Terms.pprd ct)]).getD []
  let std := match ct.maturityDate with
    | none    => []
    | some md =>
      let mdT := toTime md
      let f   := ct.futuresPrice.getD 0
      let moc := (ct.contractStructure.getD []).findSome? fun
        | .mk (.referenceId m) .UDL _ => some m
        | _                            => none
      let sT  := match moc with | some m => rf.marketRateOf m mdT | none => 0
      let stdT := match ct.settlementPeriod with
        | some c => toTime (bdcShift ct.scheduleConfig (Date.addPeriod md c.n c.period))
        | none   => mdT
      [((stdT, EventType.STD), s * (sT - f))]
  let sdT := toTime ct.statusDate
  sortCF ((prd ++ std).filter (fun c => Nat.ble sdT c.1.1))

/-- FXOUT — an FX outright (forward exchange of two currency notionals).
    *Delivery* (`deliverySettlement ≠ "S"`): at maturity exchange the two
    notionals — `MD` flows `sign·Nt1` and `−sign·Nt2`.  *Cash* (`"S"`): a single
    net `STD = sign·(Nt1 − fx·Nt2)` at maturity + `settlementPeriod`, where `fx`
    is the observed `currency2/currency` rate at maturity. -/
def fxoutCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  match ct.maturityDate with
  | none    => []
  | some md =>
    let s    := Conventions.sign (α := Float) ct.contractRole
    let mdT  := toTime md + (if rf.maturityEOD then 1 else 0)
    let nt1  := Terms.nt ct
    let nt2  := ct.notionalPrincipal2.getD 0
    let base := match ct.deliverySettlement with
      | some "S" =>
        let fxMOC := (ct.currency2.getD "") ++ "/" ++ (ct.currency.getD "")
        let rate  := rf.marketRateOf fxMOC (toTime md)
        -- settlement runs `settlementPeriod` after the (EOD-rolled) maturity
        let stdT  := match ct.settlementPeriod with
          | some c => toTime (bdcShift ct.scheduleConfig (Date.addPeriod (Date.ofEpochDay mdT) c.n c.period))
          | none   => mdT
        [((stdT, EventType.STD), s * (nt1 - rate * nt2))]
      | _ =>
        [((mdT, EventType.MD), s * nt1), ((mdT, EventType.MD), -s * nt2)]
    -- termination ends the contract early: drop the maturity exchange, settle TD
    -- (the termination price is received regardless of contract role)
    let flows := match ct.terminationDate with
      | some td => let tdT := toTime td + (if rf.terminationEOD then 1 else 0)
                   (base.filter (fun c => Nat.ble c.1.1 tdT)) ++ [((tdT, EventType.TD), Terms.ptd ct)]
      | none    => base
    -- purchase mid-life: drop pre-purchase flows, settle PRD
    let flows := match ct.purchaseDate with
      | some pd => let pT := toTime pd + (if rf.purchaseEOD then 1 else 0)
                   afterPurchase ct (((pT, EventType.PRD), -s * Terms.pprd ct) :: flows)
      | none    => flows
    let sdT := toTime ct.statusDate
    sortCF (flows.filter (fun c => Nat.ble sdT c.1.1))

-- ---------------------------------------------------------------------------
-- SWAPS — a composite of two child legs; its cash flows are the legs'.
-- ---------------------------------------------------------------------------

/-- Cash flows of a single (child) contract, dispatched on its type. -/
def legCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  match ct.contractType with
  | .PAM => pamCashflows ct rf
  | .LAM => lamCashflows ct rf
  | .NAM => namCashflows ct rf
  | .ANN => annCashflows ct rf
  | .CLM => clmCashflows ct rf
  | _    => []

/-- SWAPS — a parent contract over two legs (`contractStructure`).  The `FIL`
    leg runs in the parent's role direction, the `SEL` leg in the opposite one;
    each leg is generated by the ordinary engine and the cash flows combined:
    gross/delivery (`deliverySettlement = D`) emits both legs' flows, while net
    (`S`) sums same-`(date, event-type)` flows.  A parent `terminationDate`
    truncates the combined flows and settles `TD`; a parent `purchaseDate` drops
    pre-purchase flows and settles `PRD` (both at the parent's clean price). -/
def swapsCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  match ct.contractStructure with
  | some legs =>
    let s : Float := Conventions.sign (α := Float) ct.contractRole
    let parentPos : Bool := s > 0
    let legCf : ContractStructure Float → Cashflows
      | .mk (.referenceTerms child) role _ =>
        let pos := match role with
          | .SEL => !parentPos
          | _    => parentPos            -- FIL (and default): parent direction
        -- each leg resolves its own rate-reset series by market-object code
        let legRf := { rf with marketRate :=
          match child.marketObjectCodeOfRateReset with
          | some m => rf.marketRateOf m
          | none   => rf.marketRate }
        legCashflows { child with contractRole := if pos then .CR_RPA else .CR_RPL } legRf
      | .mk (.referenceId _) _ _ => []
    let sorted := sortCF (legs.map legCf).flatten
    -- net (cash) settlement sums same-(date, event-type) leg flows into one;
    -- gross (delivery) keeps both legs' flows
    let combined := match ct.deliverySettlement with
      | some "S" =>
        sorted.foldr (fun (c : Cashflow) acc =>
          match acc with
          | a :: rest =>
            if c.1.1 == a.1.1 && eventTypePriority c.1.2 == eventTypePriority a.1.2
            then (c.1, c.2 + a.2) :: rest else c :: acc
          | [] => [c]) []
      | _ => sorted
    -- parent termination: drop flows after the termination date, settle `TD`
    let combined := match ct.terminationDate with
      | some td => let tdT := toTime td
                   (combined.filter (fun c => Nat.ble c.1.1 tdT)) ++ [((tdT, EventType.TD), s * Terms.ptd ct)]
      | none    => combined
    -- parent purchase: drop pre-purchase flows, settle `PRD` at the clean price
    let combined := match ct.purchaseDate with
      | some pd =>
        let pT := toTime pd + (if rf.purchaseEOD then 1 else 0)   -- 23:59:59 settles next midnight
        afterPurchase ct (((pT, EventType.PRD), s * Terms.pprd ct) :: combined)
      | none    => combined
    sortCF combined
  | none => []

end Actus.Contract.Execution
