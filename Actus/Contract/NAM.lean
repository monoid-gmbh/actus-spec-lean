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

Everything else delegates to LAM.
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

abbrev Terms := Lending.Terms
abbrev State := Lending.State

/-- Negative-amortizer principal redemption: the instalment covers accrued
    interest first; the remainder `Prnxt − Ipac_{t+}` reduces `Nt`. -/
def stf_PR (ct : Terms) (t : Time) (s : State) : State :=
  let accr := LAM.ipacAccrIpcb ct t s            -- Ipac_{t+}
  -- principal portion of the instalment, capped at the remaining notional
  let nt'  := s.nt - LAM.redeemed s.nt (s.prnxt - accr)
  { s with ipac := accr, feac := PAM.feacNext ct t s
           nt   := nt'
           ipcb := match ct.interestCalculationBase with
                   | some .IPCB_NTL => s.ipcb   -- NTL: base fixed (stepped at IPCB)
                   | _              => nt'      -- NT / NTIED / none track the notional
           sd   := t }

def pof_PR (ct : Terms) (rf : RiskFactorEnv) (t : Time) (s : State) : Payoff :=
  rf.curs t * s.nsc * LAM.redeemed s.nt (s.prnxt - s.ipac - yf ct s.sd t * s.ipnr * s.ipcb)

def stf (ct : Terms) (rf : RiskFactorEnv) (ev : EventType) (t : Time) (s : State) : State :=
  match ev with
  | .PR => stf_PR ct t s
  | _   => LAM.stf ct rf ev t s

def pof (ct : Terms) (rf : RiskFactorEnv) (ev : EventType) (t : Time) (s : State) : Payoff :=
  match ev with
  | .PR => pof_PR ct rf t s
  | _   => LAM.pof ct rf ev t s

/-- Initial state: as LAM but `Prnxt = R(CNTRL)·PRNXT` (§7.4). -/
def init (ct : Terms) (md t₀ : Time) : State :=
  { LAM.init ct md t₀ with prnxt := sign (Terms.cntrl ct) * Terms.prnxt ct }

inductive Step (ct : Terms) (rf : RiskFactorEnv) : State → State → Type where
  | ev : ∀ {s : State} (e : EventType) {t : Time}, s.sd ≤ t →
         Step ct rf s (stf ct rf e t s)

abbrev Trace (ct : Terms) (rf : RiskFactorEnv) := Star (Step ct rf)

def getCashflow (ct : Terms) (rf : RiskFactorEnv) {s s' : State}
    (h : Step ct rf s s') : Cashflow :=
  match h with
  | .ev e _ => ((s'.sd, e), pof ct rf e s'.sd s)

def getCashflows (ct : Terms) (rf : RiskFactorEnv) :
    ∀ {s s' : State}, Trace ct rf s s' → Cashflows
  | _, _, .refl        => []
  | _, _, .step h rest => getCashflow ct rf h :: getCashflows ct rf rest

def NAM_contract : ActusContract := { Terms := Terms, State := State }

def NAM_impl (ct : Terms) (rf : RiskFactorEnv) (s₀ : State) :
    StateTransition NAM_contract :=
  { s₀ := s₀, rel := Step ct rf
    getCashflow := fun h r => let _ := r; getCashflow ct rf h }

end Actus.Contract.NAM
