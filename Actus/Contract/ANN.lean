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
`RiskFactorEnv.annuityYfs` (external schedule context).  Generic over `α`; the
annuity present value needs a decidable equality (zero-denominator guard).
-/

import Actus.Protocol
import Actus.Abstract
import Actus.Closures
import Actus.Contract.Common
import Actus.Contract.NAM
import Actus.Util.Schedule

namespace Actus.Contract.ANN

open Actus.Protocol
open Actus.Abstract
open Actus.Closures
open Actus.Contract
open Actus.Util
open Actus (Amount)

variable {α : Type} [Amount α] [DecidableLE α]

/-- Annuity amount `A(t, Md, Nt, Ipac, Ipnr)` for the post-reset state. -/
def annuityAmount (rf : RiskFactorEnv α) (t : Time) (nt ipac ipnr : α) : α :=
  Schedule.annuity nt ipac ipnr (rf.annuityYfs t)

/-- Rate reset: PAM rate logic, interest accrued on `Ipcb`, then `Prnxt`
    recomputed as the annuity amount. -/
def stf_RR (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  let b     := PAM.stf_RR ct rf t s             -- new Ipnr + Sd
  let ipac' := LAM.ipacAccrIpcb rf t s
  { b with ipac := ipac', prnxt := annuityAmount rf t b.nt ipac' b.ipnr }

/-- Fixed-rate reset variant: `Ipnr := RRNXT`, then recompute `Prnxt`. -/
def stf_RRF (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  let b     := PAM.stf_RRF ct rf t s
  let ipac' := LAM.ipacAccrIpcb rf t s
  { b with ipac := ipac', prnxt := annuityAmount rf t b.nt ipac' b.ipnr }

def stf (ct : Terms α) (rf : RiskFactorEnv α) (ev : EventType) (t : Time) (s : State α) : State α :=
  match ev with
  | .RR  => stf_RR ct rf t s
  | .RRF => stf_RRF ct rf t s
  | _    => NAM.stf ct rf ev t s

/-- Payoffs are exactly NAM's (RR/RRF pay nothing; PR uses `POF_PR_NAM`). -/
def pof (ct : Terms α) (rf : RiskFactorEnv α) (ev : EventType) (t : Time) (s : State α) : α :=
  NAM.pof ct rf ev t s

/-- Initial state: as NAM (`Prnxt = R(CNTRL)·PRNXT`; the annuity-derived
    fallback for an absent `PRNXT` is recomputed on the first reset). -/
def init (ct : Terms α) (md t₀ : Time) : State α := NAM.init ct md t₀

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

def ANN_contract : ActusContract := { Terms := Terms Float, State := State Float }

def ANN_impl (ct : Terms Float) (rf : RiskFactorEnv Float) (s₀ : State Float) :
    StateTransition ANN_contract :=
  { s₀ := s₀, rel := Step ct rf
    getCashflow := fun h r => let _ := r; getCashflow ct rf h }

end Actus.Contract.ANN
