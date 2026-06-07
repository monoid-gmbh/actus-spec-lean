/-
## UMP — undefined-maturity profile (non-maturity deposit)

A non-maturity deposit / savings account.  Principal is exchanged at `IED`
(`−sign·N`); interest *capitalizes* (`IPCI`, no cash) on the interest cycle,
compounding the notional `Nt ← Nt·(1 + rate·Y)`.  On termination, `TD` settles
at the agreed buy-back price plus the interest accrued since the last
capitalization: `sign·(PTD + Ipac)`, where `Ipac = Nt^cap·rate·Y(t^cap, t^TD)`
on the capitalized notional (so with a negative rate the accrual reduces the
price).

Like the lending family, UMP carries **two models**, generic over the amount
type `α`:

* a *functional* model — the `stf_*`/`pof_*` per-event functions and the
  dispatchers `stf`/`pof`;
* a *relational* model — the inductive `Step`, proven to be the graph of `stf`
  in `Actus.Contract.Agree`.

The executable builder `umpCashflows` (below, in `Actus.Contract.Execution`)
folds the same `stf`/`pof` over the generated schedule, so the relational spec
certifies the engine.  `IPCI` is a *non-cash* capitalization, so its (zero)
payoff is dropped from the reported cash flows.
-/

import Actus.Protocol
import Actus.Abstract
import Actus.Closures
import Actus.Contract.Common
import Actus.Contract.Engine
import Actus.Util.Conventions

namespace Actus.Contract.UMP

open Actus.Protocol
open Actus.Abstract
open Actus.Closures
open Actus.Contract
open Actus.Util.Conventions (sign)
open Actus (Amount)

variable {α : Type} [Amount α]

-- ---------------------------------------------------------------------------
-- State Transition Functions
-- ---------------------------------------------------------------------------

/-- Initial exchange: take on the (unsigned) notional and the nominal rate. -/
def stf_IED (ct : Terms α) (t : Time) (s : State α) : State α :=
  { s with nt := Terms.nt ct, ipnr := Terms.ipnr ct, ipac := 0, sd := t }

/-- Interest capitalization (no cash): compound the notional by the interest
    accrued over `[Sd, t]`, then reset the accrual. -/
def stf_IPCI (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  { s with nt := s.nt + s.nt * s.ipnr * rf.yf s.sd t, ipac := 0, sd := t }

/-- Termination: record the interest accrued on the capitalized notional since
    the last capitalization (settled by `pof_TD`). -/
def stf_TD (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  { s with ipac := s.ipac + s.nt * s.ipnr * rf.yf s.sd t, sd := t }

/-- STF dispatcher (events outside the UMP schedule just advance the clock). -/
def stf (ct : Terms α) (rf : RiskFactorEnv α) (ev : EventType) (t : Time) (s : State α) : State α :=
  match ev with
  | .IED  => stf_IED ct t s
  | .IPCI => stf_IPCI rf t s
  | .TD   => stf_TD rf t s
  | _     => { s with sd := t }

-- ---------------------------------------------------------------------------
-- Payoff Functions
-- ---------------------------------------------------------------------------

def pof_IED (ct : Terms α) : α := sign (Terms.cntrl ct) * (-1) * Terms.nt ct

/-- Termination payoff: buy-back price plus interest accrued since the last
    capitalization, on the capitalized notional. -/
def pof_TD (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  sign (Terms.cntrl ct) * (Terms.ptd ct + s.ipac + s.nt * s.ipnr * rf.yf s.sd t)

def pof (ct : Terms α) (rf : RiskFactorEnv α) (ev : EventType) (t : Time) (s : State α) : α :=
  match ev with
  | .IED => pof_IED ct
  | .TD  => pof_TD ct rf t s
  | _    => 0   -- IPCI (non-cash) and clock ticks

-- ---------------------------------------------------------------------------
-- Initialization
-- ---------------------------------------------------------------------------

/-- Pre-`IED` state at `t₀`; `stf_IED` overwrites the monetary fields. -/
def init (ct : Terms α) (t₀ : Time) : State α :=
  { md    := 0
    nt    := Terms.nt ct
    ipnr  := Terms.ipnr ct
    ipac  := 0
    feac  := 0
    nsc   := 1
    isc   := 1
    prnxt := 0
    ipcb  := 0
    prf   := ct.contractPerformance.getD .PRF_PF
    sd    := t₀ }

-- ---------------------------------------------------------------------------
-- Relational model
-- ---------------------------------------------------------------------------

/-- One-step UMP transition.  The constructor targets the dispatcher `stf`. -/
inductive Step (ct : Terms α) (rf : RiskFactorEnv α) : State α → State α → Type where
  | ev : ∀ {s : State α} (e : EventType) {t : Time}, s.sd ≤ t →
         Step ct rf s (stf ct rf e t s)

abbrev Trace (ct : Terms α) (rf : RiskFactorEnv α) := Star (Step ct rf)

def getCashflow (ct : Terms α) (rf : RiskFactorEnv α) {s s' : State α}
    (h : Step ct rf s s') : Event × α :=
  match h with
  | .ev e _ => ((s'.sd, e), pof ct rf e s'.sd s)

def getCashflows (ct : Terms α) (rf : RiskFactorEnv α) :
    ∀ {s s' : State α}, Trace ct rf s s' → List (Event × α)
  | _, _, .refl        => []
  | _, _, .step h rest => getCashflow ct rf h :: getCashflows ct rf rest

def UMP_contract : ActusContract := { Terms := Terms Float, State := State Float }

def UMP_impl (ct : Terms Float) (rf : RiskFactorEnv Float) (s₀ : State Float) :
    StateTransition UMP_contract :=
  { s₀ := s₀, rel := Step ct rf
    getCashflow := fun h r => let _ := r; getCashflow ct rf h }

end Actus.Contract.UMP

-- ---------------------------------------------------------------------------
-- Executable builder
-- ---------------------------------------------------------------------------

namespace Actus.Contract.Execution

open Actus.Protocol
open Actus.Util
open Actus.Contract

/-- UMP cash flows: thread `UMP.stf`/`UMP.pof` over the schedule `IED`, the
    capitalization (`IPCI`) cycle strictly before termination, then `TD`.
    `IPCI` is a non-cash capitalization, so its zero payoff is not reported. -/
def umpCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }
  match ct.initialExchangeDate with
  | none     => []
  | some ied =>
    let cfg  := ct.scheduleConfig
    let iedT := toTime ied
    let sched : Schedule := match ct.terminationDate with
      | none    => [(iedT, EventType.IED)]
      | some td =>
        let tdT := toTime td + (if rf.terminationEOD then 1 else 0)
        let ipciDates := (cyclicTimes cfg ct.cycleAnchorDateOfInterestPayment
                            ct.cycleOfInterestPayment ct.initialExchangeDate (some td) false).filter
                            (fun t => Nat.blt iedT t && Nat.blt t tdT)
        (iedT, EventType.IED) :: ipciDates.map (fun t => (t, EventType.IPCI))
          ++ [(tdT, EventType.TD)]
    let flows := Execution.runSchedule (UMP.stf ct rf) (UMP.pof ct rf) (UMP.init ct iedT) sched
    -- IPCI is non-cash: drop it from the reported flows
    let flows := flows.filter (fun c => eventTypePriority c.1.2 != eventTypePriority .IPCI)
    let sdT := toTime ct.statusDate
    sortCF (flows.filter (fun c => Nat.ble sdT c.1.1))

end Actus.Contract.Execution
