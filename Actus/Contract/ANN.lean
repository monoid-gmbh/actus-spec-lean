/-
## ANN — Annuity  (§7.5)

A loan repaid in *constant total instalments*: each `PR` payment combines an
interest portion and a principal portion sized so the notional is fully repaid
by maturity.  §7.5 builds ANN from NAM/LAM/PAM with one defining twist: on a
rate reset (`RR`/`RRF`) the next instalment `Prnxt` is recomputed from the
**Annuity Amount function** `A` (§3.8) so the contract stays fully amortizing
after the rate change.

* `PR` reuses NAM (`STF_PR_NAM` / `POF_PR_NAM`).
* `RR`/`RRF` accrue interest, reset the rate, then set
  `Prnxt = A(t, Md, Nt, Ipac, Ipnr)`.
* everything else delegates to NAM (hence LAM, hence PAM).

The remaining-period year fractions feeding `A` come from
`RiskFactorEnv.annuityYfs` (external schedule context).
-/

import Actus.Protocol
import Actus.Abstract
import Actus.Closures
import Actus.Contract.Lending.Common
import Actus.Contract.NAM
import Actus.Util.Schedule

namespace Actus.Contract.ANN

open Actus.Protocol
open Actus.Abstract
open Actus.Closures
open Actus.Contract.Lending
open Actus.Util

abbrev Terms := Lending.Terms
abbrev State := Lending.State

/-- Annuity amount `A(t, Md, Nt, Ipac, Ipnr)` for the post-reset state. -/
def annuityAmount (rf : RiskFactorEnv) (t : Time) (nt ipac ipnr : Float) : Float :=
  Schedule.annuity nt ipac ipnr (rf.annuityYfs t)

/-- Rate reset: PAM rate logic, interest accrued on `Ipcb`, then `Prnxt`
    recomputed as the annuity amount. -/
def stf_RR (ct : Terms) (rf : RiskFactorEnv) (t : Time) (s : State) : State :=
  let b     := PAM.stf_RR ct rf t s             -- new Ipnr + Sd
  let ipac' := LAM.ipacAccrIpcb ct t s
  { b with ipac := ipac', prnxt := annuityAmount rf t b.nt ipac' b.ipnr }

/-- Fixed-rate reset variant: `Ipnr := RRNXT`, then recompute `Prnxt`. -/
def stf_RRF (ct : Terms) (rf : RiskFactorEnv) (t : Time) (s : State) : State :=
  let b     := PAM.stf_RRF ct t s
  let ipac' := LAM.ipacAccrIpcb ct t s
  { b with ipac := ipac', prnxt := annuityAmount rf t b.nt ipac' b.ipnr }

def stf (ct : Terms) (rf : RiskFactorEnv) (ev : EventType) (t : Time) (s : State) : State :=
  match ev with
  | .RR  => stf_RR ct rf t s
  | .RRF => stf_RRF ct rf t s
  | _    => NAM.stf ct rf ev t s

/-- Payoffs are exactly NAM's (RR/RRF pay nothing; PR uses `POF_PR_NAM`). -/
def pof (ct : Terms) (rf : RiskFactorEnv) (ev : EventType) (t : Time) (s : State) : Payoff :=
  NAM.pof ct rf ev t s

/-- Initial state: as NAM (`Prnxt = R(CNTRL)·PRNXT`; the annuity-derived
    fallback for an absent `PRNXT` is recomputed on the first reset). -/
def init (ct : Terms) (md t₀ : Time) : State := NAM.init ct md t₀

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

def ANN_contract : ActusContract := { Terms := Terms, State := State }

def ANN_impl (ct : Terms) (rf : RiskFactorEnv) (s₀ : State) :
    StateTransition ANN_contract :=
  { s₀ := s₀, rel := Step ct rf
    getCashflow := fun h r => let _ := r; getCashflow ct rf h }

end Actus.Contract.ANN
