/- ## Swap contracts: SWPPV (plain-vanilla IRS) and SWAPS (composite of legs). -/

import Actus.Protocol
import Actus.Abstract
import Actus.Closures
import Actus.Contract.Engine
import Actus.Contract.Lending
import Actus.Util.Conventions

-- ---------------------------------------------------------------------------
-- SWPPV — relational + functional model (plain-vanilla interest-rate swap)
-- ---------------------------------------------------------------------------

namespace Actus.Contract.SWPPV

open Actus.Protocol
open Actus.Abstract
open Actus.Closures
open Actus.Contract
open Actus.Util.Conventions (sign)
open Actus (Amount)

variable {α : Type} [Amount α]

/- A plain-vanilla interest-rate swap.  Each interest period pays two legs: a
    fixed leg `IPFX = sign·N·fixedRate·Y` and a floating leg
    `IPFL = −sign·N·floatRate·Y`, where `fixedRate = nominalInterestRate`,
    `floatRate` starts at `nominalInterestRate2` and is reset by `RR` events to
    `clamp_{[lifeFloor,lifeCap]}(Oʳᶠ(RRMO)·RRMLT + RRSP)`.

    The state carries the signed notional `Nt`, the current floating rate `Ipnr`
    and the period-start `Sd` (advanced by the floating leg `IPFL`, which fires
    last among a period's two legs).  Because `IPFL` advances `Sd` while `IPFX`
    leaves it untouched, both legs of a period see the same `Y(Sd, t)`; an `RR`
    fires *after* both legs at a shared timestamp, so it only affects later
    periods (matching the spec's "latest reset strictly before `t`"). -/

/-- Rate reset: install the clamped market floating rate. -/
def stf_RR (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  { s with ipnr := clampHi ct.lifeCap (clampLo ct.lifeFloor
                     (rf.marketRate t * Terms.rrmlt ct + Terms.rrsp ct)) }

/-- STF dispatcher.  The floating leg advances the period boundary `Sd`; the
    fixed leg (and any other event) leaves the state untouched. -/
def stf (ct : Terms α) (rf : RiskFactorEnv α) (e : EventType) (t : Time) (s : State α) : State α :=
  match e with
  | .IPFL => { s with sd := t }
  | .RR   => stf_RR ct rf t s
  | _     => s

def pof_IPFX (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  s.nt * Terms.ipnr ct * rf.yf s.sd t

def pof_IPFL (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  (-1) * s.nt * s.ipnr * rf.yf s.sd t

def pof (ct : Terms α) (rf : RiskFactorEnv α) (e : EventType) (t : Time) (s : State α) : α :=
  match e with
  | .IPFX => pof_IPFX ct rf t s
  | .IPFL => pof_IPFL rf t s
  | _     => 0   -- RR / clock ticks

/-- Initial state: signed notional, floating rate at `nominalInterestRate2`,
    period start at `IED`. -/
def init (ct : Terms α) (iedT : Time) : State α :=
  { md    := 0
    nt    := sign (Terms.cntrl ct) * Terms.nt ct
    ipnr  := ct.nominalInterestRate2.getD 0
    ipac  := 0
    feac  := 0
    nsc   := 1
    isc   := 1
    prnxt := 0
    ipcb  := 0
    prf   := ct.contractPerformance.getD .PRF_PF
    sd    := iedT }

-- ---------------------------------------------------------------------------
-- Relational model
-- ---------------------------------------------------------------------------

/-- One-step SWPPV transition.  `t` is explicit (a period may emit two legs at
    the same `t`, so the cash-flow time is taken from `t` rather than `Sd`). -/
inductive Step (ct : Terms α) (rf : RiskFactorEnv α) : State α → State α → Type where
  | ev : ∀ {s : State α} (e : EventType) (t : Time), s.sd ≤ t →
         Step ct rf s (stf ct rf e t s)

abbrev Trace (ct : Terms α) (rf : RiskFactorEnv α) := Star (Step ct rf)

def getCashflow (ct : Terms α) (rf : RiskFactorEnv α) {s s' : State α}
    (h : Step ct rf s s') : Event × α :=
  match h with
  | .ev e t _ => ((t, e), pof ct rf e t s)

def getCashflows (ct : Terms α) (rf : RiskFactorEnv α) :
    ∀ {s s' : State α}, Trace ct rf s s' → List (Event × α)
  | _, _, .refl        => []
  | _, _, .step h rest => getCashflow ct rf h :: getCashflows ct rf rest

def SWPPV_contract : ActusContract := { Terms := Terms Float, State := State Float }

def SWPPV_impl (ct : Terms Float) (rf : RiskFactorEnv Float) (s₀ : State Float) :
    StateTransition SWPPV_contract :=
  { s₀ := s₀, rel := Step ct rf
    getCashflow := fun h r => let _ := r; getCashflow ct rf h }

end Actus.Contract.SWPPV

-- ---------------------------------------------------------------------------
-- Executable builders
-- ---------------------------------------------------------------------------

namespace Actus.Contract.Execution

open Actus.Protocol
open Actus.Util
open Actus.Contract

/-- SWPPV cash flows.  Each interest period emits a fixed (`IPFX`) and floating
    (`IPFL`) leg; rate resets (`RR`) update the floating rate.  The events are
    folded through `SWPPV.stf`/`SWPPV.pof`; at a shared timestamp they are
    ordered `IPFX`, `IPFL`, then `RR`, so both legs read the pre-reset rate and
    the same period year-fraction.  Gross (`D`) keeps both legs; net (`S`) sums
    them per period into one `IP`. -/
def swppvCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }
  match ct.initialExchangeDate, ct.maturityDate with
  | some ied, some md =>
    let s    := Conventions.sign (α := Float) ct.contractRole
    let cfg  := ct.scheduleConfig
    let iedT := toTime ied
    -- interest-payment dates (anchored cycle, up to & incl. maturity)
    let ipDates := (cyclicTimes cfg ct.cycleAnchorDateOfInterestPayment
                      ct.cycleOfInterestPayment ct.initialExchangeDate (some md) true).filter
                      (fun t => Nat.blt iedT t)
    -- rate-reset dates
    let rrDates := cyclicTimes cfg ct.cycleAnchorDateOfRateReset
                     ct.cycleOfRateReset ct.initialExchangeDate (some md) false
    -- events: each payment date emits both legs; each reset date an RR
    let legEvs : List Event := ipDates.flatMap (fun t => [(t, EventType.IPFX), (t, EventType.IPFL)])
    let rrEvs  : List Event := rrDates.map (fun t => (t, EventType.RR))
    -- order chronologically; at a shared time, both legs before the reset so the
    -- legs read the pre-reset rate (`r < t`) and share the period year-fraction
    let ord : EventType → Nat := fun e => match e with
      | .IPFX => 0 | .IPFL => 1 | .RR => 2 | _ => 3
    let evs := ((legEvs ++ rrEvs).toArray.qsort (fun a b =>
      if a.1 == b.1 then Nat.blt (ord a.2) (ord b.2) else Nat.blt a.1 b.1)).toList
    let flows := Execution.runSchedule (SWPPV.stf ct rf) (SWPPV.pof ct rf) (SWPPV.init ct iedT) evs
    -- RR carries no cash flow
    let flows := flows.filter (fun c => eventTypePriority c.1.2 != eventTypePriority .RR)
    -- net (cash) settlement sums the two legs of each period into one flow
    let flows := match ct.deliverySettlement with
      | some "S" =>
        (sortCF flows).foldr (fun (c : Cashflow) (acc : Cashflows) =>
          match acc with
          | a :: rest => if c.1.1 == a.1.1 then ((c.1.1, EventType.IP), c.2 + a.2) :: rest
                         else c :: acc
          | [] => [c]) ([] : Cashflows)
      | _ => flows
    -- parent termination: drop interest after the termination date, settle TD
    let flows := match ct.terminationDate with
      | some td => let tdT := toTime td + (if rf.terminationEOD then 1 else 0)
                   (flows.filter (fun c => Nat.ble c.1.1 tdT)) ++ [((tdT, EventType.TD), Terms.ptd ct)]
      | none    => flows
    -- parent purchase: drop pre-purchase flows, settle PRD
    let flows := match ct.purchaseDate with
      | some pd => let pT := toTime pd + (if rf.purchaseEOD then 1 else 0)
                   afterPurchase ct (((pT, EventType.PRD), -s * Terms.pprd ct) :: flows)
      | none    => flows
    let sdT := toTime ct.statusDate
    sortCF (flows.filter (fun c => Nat.ble sdT c.1.1))
  | _, _ => []

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
