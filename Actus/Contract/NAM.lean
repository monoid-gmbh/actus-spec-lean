/-
## NAM — Negative Amortizer  (§7.4)

Like LAM, but the fixed instalment `Prnxt` is applied *interest-first*: the
interest portion is paid out of the instalment and only the remainder reduces
principal (so the notional can grow when interest exceeds the instalment —
hence "negative amortizer").

§7.4 defines NAM as LAM with two changes:

* the **PR** event has its own payoff/STF (`POF_PR_NAM` / `STF_PR_NAM`);
* `Prnxt` initializes to `R(CNTRL)·PRNXT` and `Md` to a redemption-count-derived
  date (supplied here via `genSchedule`).

Everything else delegates to LAM.  Generic over the amount type `α`.
-/

import Actus.Protocol
import Actus.Abstract
import Actus.Closures
import Actus.Contract.Lending.Common
import Actus.Contract.LAM
import Actus.Util.Conventions

namespace Actus.Contract.NAM

open Actus.Protocol
open Actus.Abstract
open Actus.Closures
open Actus.Contract.Lending
open Actus.Util.Conventions (sign)
open Actus (Amount)

variable {α : Type} [Amount α] [DecidableLE α]

/-- Negative-amortizer principal redemption: the instalment covers accrued
    interest first; the remainder `Prnxt − Ipac_{t+}` reduces `Nt`. -/
def stf_PR (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  let accr := LAM.ipacAccrIpcb rf t s            -- Ipac_{t+}
  -- principal portion of the instalment, capped at the remaining notional
  let nt'  := s.nt - LAM.redeemed s.nt (s.prnxt - accr)
  { s with ipac := accr, feac := PAM.feacNext ct rf t s
           nt   := nt'
           ipcb := match ct.interestCalculationBase with
                   | some .IPCB_NTL => s.ipcb   -- NTL: base fixed (stepped at IPCB)
                   | _              => nt'      -- NT / NTIED / none track the notional
           sd   := t }

def pof_PR (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  rf.curs t * s.nsc * LAM.redeemed s.nt (s.prnxt - s.ipac - rf.yf s.sd t * s.ipnr * s.ipcb)

def stf (ct : Terms α) (rf : RiskFactorEnv α) (ev : EventType) (t : Time) (s : State α) : State α :=
  match ev with
  | .PR => stf_PR ct rf t s
  | _   => LAM.stf ct rf ev t s

def pof (ct : Terms α) (rf : RiskFactorEnv α) (ev : EventType) (t : Time) (s : State α) : α :=
  match ev with
  | .PR => pof_PR rf t s
  | _   => LAM.pof ct rf ev t s

/-- Initial state: as LAM but `Prnxt = R(CNTRL)·PRNXT` (§7.4). -/
def init (ct : Terms α) (md t₀ : Time) : State α :=
  { LAM.init ct md t₀ with prnxt := sign (Terms.cntrl ct) * Terms.prnxt ct }

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

def NAM_contract : ActusContract := { Terms := Terms Float, State := State Float }

def NAM_impl (ct : Terms Float) (rf : RiskFactorEnv Float) (s₀ : State Float) :
    StateTransition NAM_contract :=
  { s₀ := s₀, rel := Step ct rf
    getCashflow := fun h r => let _ := r; getCashflow ct rf h }

end Actus.Contract.NAM
