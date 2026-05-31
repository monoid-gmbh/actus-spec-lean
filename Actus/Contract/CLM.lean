/-
## CLM — Call Money  (§7.x)

A money-market loan: principal exchanged at `IED`, interest accruing on the
notional and **capitalizing** (`IPCI`) on the interest cycle, with the final
interest paid (`IP`) and the (grown) principal redeemed (`MD`) at maturity.
Rate resets (`RR`) reprice it like PAM.

The state transitions are *exactly* PAM's — CLM differs only in its **contract
schedule** (interest capitalizes until maturity instead of being paid each
period), which lives in `Actus.Contract.Execution`.  This module is the
thin per-contract view (relational `Step`, cashflow extraction) over the shared
PAM `stf`/`pof`.
-/

import Actus.Protocol
import Actus.Abstract
import Actus.Closures
import Actus.Contract.Common
import Actus.Contract.PAM

namespace Actus.Contract.CLM

open Actus.Protocol
open Actus.Abstract
open Actus.Closures
open Actus.Contract
open Actus (Amount)

variable {α : Type} [Amount α]

/-- CLM state transition = PAM's (the call-money specifics are in the schedule). -/
def stf (ct : Terms α) (rf : RiskFactorEnv α) (ev : EventType) (t : Time) (s : State α) : State α :=
  PAM.stf ct rf ev t s

/-- CLM payoff = PAM's. -/
def pof (ct : Terms α) (rf : RiskFactorEnv α) (ev : EventType) (t : Time) (s : State α) : α :=
  PAM.pof ct rf ev t s

/-- CLM initial state = PAM's. -/
def init (ct : Terms α) (md t₀ : Time) : State α := PAM.init ct md t₀

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

def CLM_contract : ActusContract := { Terms := Terms Float, State := State Float }

def CLM_impl (ct : Terms Float) (rf : RiskFactorEnv Float) (s₀ : State Float) :
    StateTransition CLM_contract :=
  { s₀ := s₀, rel := Step ct rf
    getCashflow := fun h r => let _ := r; getCashflow ct rf h }

end Actus.Contract.CLM
