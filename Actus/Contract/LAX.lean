/-
## LAX — exotic amortizer with piecewise (array) principal/interest schedules

An exotic amortizer whose principal-redemption, interest and rate-reset
schedules are given piecewise by *array* attributes.  Each principal segment
redeems (`DEC` → `PR`) or draws (`INC` → `PI`) its own amount on its own cycle;
the notional accrues interest (`IP`) the LAM way, capitalized across
redemptions; the contract matures (`MD`, paying the residual notional) at the
explicit `maturityDate` or when the final segment exhausts the notional.  Rate
resets come from the `arrayRate`/`arrayFixedVariable` arrays (`FIX` → `RRF` to
the given rate, `VAR` → `RR` to the market rate).

Like the lending family, LAX carries **two models**, generic over the amount
type `α`:

* a *functional* model — the `stf_*`/`pof_*` per-event functions and the
  dispatchers `stf`/`pof`;
* a *relational* model — the inductive `Step`, proven to be the graph of `stf`
  in `Actus.Contract.Agree`.

Because the per-event amount (for `PR`/`PI`) and the new rate (for `RR`/`RRF`)
come from the array schedules rather than the state, the `stf`/`pof` signatures
carry one extra **payload** `x : α` (amount or rate — they never co-occur); this
generalizes the lending family's amount-from-state.  The executable builder
`laxCashflows` (below) builds the array-derived event list `(t, e, x)` and folds
the same `stf`/`pof` over it via `laxRun`, so the relational spec certifies the
engine.
-/

import Actus.Protocol
import Actus.Abstract
import Actus.Closures
import Actus.Contract.Common
import Actus.Contract.Engine
import Actus.Util.Conventions

namespace Actus.Contract.LAX

open Actus.Protocol
open Actus.Abstract
open Actus.Closures
open Actus.Contract
open Actus.Util.Conventions (sign)
open Actus (Amount)

variable {α : Type} [Amount α]

/-- Interest accrued over `[Sd, t]` on the current notional. -/
def accr (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  s.ipac + s.nt * s.ipnr * rf.yf s.sd t

-- ---------------------------------------------------------------------------
-- State Transition Functions  (payload `x` = redemption amount / new rate)
-- ---------------------------------------------------------------------------

/-- Initial exchange: take on the signed notional and the nominal rate. -/
def stf_IED (ct : Terms α) (t : Time) (s : State α) : State α :=
  { s with nt := sign (Terms.cntrl ct) * Terms.nt ct
           ipac := 0, ipnr := Terms.ipnr ct, sd := t }

/-- Interest payment: pay the accrued interest, reset the accrual. -/
def stf_IP (t : Time) (s : State α) : State α :=
  { s with ipac := 0, sd := t }

/-- Principal redemption: reduce the notional by the (signed) instalment `x`,
    capitalizing the interest accrued so far. -/
def stf_PR (ct : Terms α) (rf : RiskFactorEnv α) (x : α) (t : Time) (s : State α) : State α :=
  { s with nt := s.nt - sign (Terms.cntrl ct) * x, ipac := accr rf t s, sd := t }

/-- Principal increase (draw): grow the notional by the (signed) draw `x`. -/
def stf_PI (ct : Terms α) (rf : RiskFactorEnv α) (x : α) (t : Time) (s : State α) : State α :=
  { s with nt := s.nt + sign (Terms.cntrl ct) * x, ipac := accr rf t s, sd := t }

/-- Maturity: pay out the residual notional. -/
def stf_MD (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  { s with nt := 0, ipac := accr rf t s, sd := t }

/-- Rate reset (`RR`/`RRF`): set the rate to the payload `x` (already resolved
    by schedule generation: the fixed rate for `RRF`, the observed market rate
    for `RR`). -/
def stf_reset (rf : RiskFactorEnv α) (x : α) (t : Time) (s : State α) : State α :=
  { s with ipnr := x, ipac := accr rf t s, sd := t }

/-- STF dispatcher.  Out-of-schedule events accrue and advance the clock. -/
def stf (ct : Terms α) (rf : RiskFactorEnv α) (e : EventType) (x : α) (t : Time) (s : State α) : State α :=
  match e with
  | .IED => stf_IED ct t s
  | .IP  => stf_IP t s
  | .PR  => stf_PR ct rf x t s
  | .PI  => stf_PI ct rf x t s
  | .MD  => stf_MD rf t s
  | .RRF => stf_reset rf x t s
  | .RR  => stf_reset rf x t s
  | _    => { s with ipac := accr rf t s, sd := t }

-- ---------------------------------------------------------------------------
-- Payoff Functions
-- ---------------------------------------------------------------------------

def pof_IED (ct : Terms α) : α :=
  sign (Terms.cntrl ct) * (-1) * (Terms.nt ct + ct.premiumDiscountAtIED.getD 0)

def pof_IP (rf : RiskFactorEnv α) (t : Time) (s : State α) : α := accr rf t s

def pof_PR (ct : Terms α) (x : α) : α := sign (Terms.cntrl ct) * x

def pof_PI (ct : Terms α) (x : α) : α := sign (Terms.cntrl ct) * (-1) * x

def pof_MD (s : State α) : α := s.nt

def pof (ct : Terms α) (rf : RiskFactorEnv α) (e : EventType) (x : α) (t : Time) (s : State α) : α :=
  match e with
  | .IED => pof_IED ct
  | .IP  => pof_IP rf t s
  | .PR  => pof_PR ct x
  | .PI  => pof_PI ct x
  | .MD  => pof_MD s
  | _    => 0   -- RR / RRF / clock ticks

-- ---------------------------------------------------------------------------
-- Initialization
-- ---------------------------------------------------------------------------

/-- State just before the `IED` event (which `stf_IED` re-establishes). -/
def init (ct : Terms α) (iedT : Time) : State α :=
  { md    := 0
    nt    := sign (Terms.cntrl ct) * Terms.nt ct
    ipnr  := Terms.ipnr ct
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

/-- One-step LAX transition.  The constructor carries the event `e` and its
    schedule payload `x`, and targets the dispatcher `stf`. -/
inductive Step (ct : Terms α) (rf : RiskFactorEnv α) : State α → State α → Type where
  | ev : ∀ {s : State α} (e : EventType) (x : α) {t : Time}, s.sd ≤ t →
         Step ct rf s (stf ct rf e x t s)

abbrev Trace (ct : Terms α) (rf : RiskFactorEnv α) := Star (Step ct rf)

def getCashflow (ct : Terms α) (rf : RiskFactorEnv α) {s s' : State α}
    (h : Step ct rf s s') : Event × α :=
  match h with
  | .ev e x _ => ((s'.sd, e), pof ct rf e x s'.sd s)

def getCashflows (ct : Terms α) (rf : RiskFactorEnv α) :
    ∀ {s s' : State α}, Trace ct rf s s' → List (Event × α)
  | _, _, .refl        => []
  | _, _, .step h rest => getCashflow ct rf h :: getCashflows ct rf rest

def LAX_contract : ActusContract := { Terms := Terms Float, State := State Float }

def LAX_impl (ct : Terms Float) (rf : RiskFactorEnv Float) (s₀ : State Float) :
    StateTransition LAX_contract :=
  { s₀ := s₀, rel := Step ct rf
    getCashflow := fun h r => let _ := r; getCashflow ct rf h }

end Actus.Contract.LAX

-- ---------------------------------------------------------------------------
-- Executable builder
-- ---------------------------------------------------------------------------

namespace Actus.Contract.Execution

open Actus.Protocol
open Actus.Util
open Actus.Contract

/-- Indexed lookup with a default. -/
def getI {α : Type} (l : List α) (i : Nat) (d : α) : α := (l[i]?).getD d

/-- Fold `LAX.stf`/`LAX.pof` over a payloaded event list `(time, event, x)`,
    where `x` is the redemption amount (`PR`/`PI`) or new rate (`RR`/`RRF`). -/
def laxRun (ct : Terms Float) (rf : RiskFactorEnv Float) :
    State Float → List (Time × EventType × Float) → Cashflows
  | _, []                => []
  | s, (t, e, x) :: rest => ((t, e), LAX.pof ct rf e x t s) :: laxRun ct rf (LAX.stf ct rf e x t s) rest

/-- LAX — build the array-derived event list (principal segments, interest
    cycle, rate resets) and fold `LAX.stf`/`LAX.pof` over it. -/
def laxCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }
  match ct.initialExchangeDate with
  | none     => []
  | some ied =>
    let n    := Terms.nt ct
    let cfg  := ct.scheduleConfig
    let rate0 := Terms.ipnr ct
    let iedT := toTime ied
    -- principal segments
    let prAnchors := ct.arrayCycleAnchorDateOfPrincipalRedemption.getD []
    let prCycles  := ct.arrayCycleOfPrincipalRedemption.getD []
    let prAmts    := ct.arrayNextPrincipalRedemptionPayment.getD []
    let prDirs    := ct.arrayIncreaseDecrease.getD []
    let nseg := prAnchors.length
    -- build principal events (date, isInc, amount); thread the running notional
    -- so the last `DEC` segment can derive maturity by notional exhaustion.
    let rec buildPrin (i : Nat) (run : Float) :
        List (Time × Bool × Float) × Option LocalTime :=
      if h : i < nseg then
        let anchor := getI prAnchors i ied
        let cyc    := getI prCycles i none
        let amt    := getI prAmts i 0
        let isInc  := getI prDirs i "DEC" == "INC"
        let isLast := i + 1 == nseg
        if isLast then
          -- last segment: end at the explicit maturity, else exhaust notional
          match ct.maturityDate with
          | some md =>
            let dates := Schedule.schedule cfg anchor cyc md false
            (dates.map (fun d => (toTime d, isInc, amt)), some md)
          | none =>
            -- number of redemptions to clear the notional (≥1)
            let k := if isInc || amt == 0 then 1
                     else max 1 (Float.toUInt64 (Float.ceil (run / amt))).toNat
            let dates := (List.range k).map (fun j =>
              match cyc with
              | some c => Date.addPeriod anchor (j * c.n) c.period
              | none   => anchor)
            (dates.map (fun d => (toTime d, isInc, amt)), dates.getLast?)
        else
          let nextA := getI prAnchors (i+1) ied
          let dates := Schedule.schedule cfg anchor cyc nextA false
          let run'  := dates.foldl (fun r _ => if isInc then r + amt else r - amt) run
          let (rest, mat) := buildPrin (i+1) run'
          (dates.map (fun d => (toTime d, isInc, amt)) ++ rest, mat)
      else ([], none)
    let (prinRaw, matDateOpt) := buildPrin 0 n
    let matDate := matDateOpt.getD ied
    let matT    := toTime matDate
    -- principal events: the redemption coinciding with maturity becomes `MD`
    let prin : List (Time × EventType × Float) := prinRaw.map fun (t, isInc, amt) =>
      if t == matT then (t, EventType.MD, amt)
      else if isInc then (t, EventType.PI, amt) else (t, EventType.PR, amt)
    let prin := if prin.any (fun e => e.1 == matT && eventTypePriority e.2.1 == eventTypePriority .MD)
                then prin else prin ++ [(matT, EventType.MD, 0)]
    -- interest events (array schedule up to & including maturity)
    let ipAnchors := ct.arrayCycleAnchorDateOfInterestPayment.getD []
    let ipCycles  := ct.arrayCycleOfInterestPayment.getD []
    let ipPairs   := (List.range ipAnchors.length).map fun i =>
      (getI ipAnchors i ied, getI ipCycles i none)
    let ipDates := (Schedule.arraySchedule cfg ipPairs matDate).map toTime
    let ipEv : List (Time × EventType × Float) :=
      (ipDates.filter (fun t => Nat.blt iedT t)).map (fun t => (t, EventType.IP, 0))
    -- rate resets from the rate arrays
    let rrAnchors := ct.arrayCycleAnchorDateOfRateReset.getD []
    let rrRates   := ct.arrayRate.getD []
    let rrFixVar  := ct.arrayFixedVariable.getD []
    let rrEv : List (Time × EventType × Float) := (List.range rrAnchors.length).map fun i =>
      let t   := toTime (getI rrAnchors i ied)
      let fix := getI rrFixVar i "FIX" == "FIX"
      -- FIX: the array rate is the new fixed rate.  VAR: it is the spread over
      -- the observed market rate.
      if fix then (t, EventType.RRF, getI rrRates i rate0)
      else (t, EventType.RR, rf.marketRate t * Terms.rrmlt ct + getI rrRates i 0)
    -- IED + everything, sorted by (time, priority)
    let iedEv : Time × EventType × Float := (iedT, EventType.IED, 0)
    let evs := (iedEv :: prin ++ ipEv ++ rrEv)
    let evs := evs.toArray.qsort (fun a b =>
      if a.1 == b.1 then Nat.blt (eventTypePriority a.2.1) (eventTypePriority b.2.1)
      else Nat.blt a.1 b.1) |>.toList
    let flows := laxRun ct rf (LAX.init ct iedT) evs
    let sdT := toTime ct.statusDate
    sortCF (flows.filter (fun c => Nat.ble sdT c.1.1))

end Actus.Contract.Execution
