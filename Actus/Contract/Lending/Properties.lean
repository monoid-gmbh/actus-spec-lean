/-
## Metatheorems (lending family)

Structural properties proved without Float arithmetic (which is not
kernel-reducible), relying instead on the *shape* of the state transitions:

* **Status-date advance** (`*_stf_sd`): every event sets `Sd` to its event time.
* **Monotonicity** (`*_step_mono`, `*_trace_mono`): because each step requires
  `Sd ≤ t` and then sets `Sd := t`, status dates are non-decreasing along any
  execution trace — the relation is a well-formed timeline.
* **Maturity / termination** (`*_md_*`, `*_td_*`): `MD` zeroes notional, accrued
  interest and fees; `TD` additionally zeroes the rate.  These hold definitionally.
* **IED notional** (`pam_ied_nt`): the initial exchange sets the signed notional.
* **Determinism**: `step_to_fun` (in `Agree`) plus the fact that `stf` is a
  function means the post-state is uniquely determined by the event and time.
-/

import Actus.Contract.Lending.Agree
import Actus.Closures

namespace Actus.Contract.Lending.Properties

open Actus.Protocol
open Actus.Closures
open Actus.Contract.Lending
open Actus.Util.Conventions (sign)

variable {ct : Lending.Terms} {rf : RiskFactorEnv}

-- ---------------------------------------------------------------------------
-- Every event advances the status date to its event time
-- ---------------------------------------------------------------------------

theorem pam_stf_sd (e : EventType) (t : Time) (s : State) :
    (PAM.stf ct rf e t s).sd = t := by cases e <;> rfl

theorem lam_stf_sd (e : EventType) (t : Time) (s : State) :
    (LAM.stf ct rf e t s).sd = t := by cases e <;> rfl

theorem nam_stf_sd (e : EventType) (t : Time) (s : State) :
    (NAM.stf ct rf e t s).sd = t := by cases e <;> rfl

theorem ann_stf_sd (e : EventType) (t : Time) (s : State) :
    (ANN.stf ct rf e t s).sd = t := by cases e <;> rfl

-- ---------------------------------------------------------------------------
-- Status-date monotonicity:  one step
-- ---------------------------------------------------------------------------

theorem pam_step_mono {s s' : State} (h : PAM.Step ct rf s s') : s.sd ≤ s'.sd := by
  cases h <;> assumption   -- each constructor's guard `s.sd ≤ t` and `s'.sd ≡ t`

theorem lam_step_mono {s s' : State} (h : LAM.Step ct rf s s') : s.sd ≤ s'.sd := by
  cases h with | ev e ht => rw [lam_stf_sd]; exact ht

theorem nam_step_mono {s s' : State} (h : NAM.Step ct rf s s') : s.sd ≤ s'.sd := by
  cases h with | ev e ht => rw [nam_stf_sd]; exact ht

theorem ann_step_mono {s s' : State} (h : ANN.Step ct rf s s') : s.sd ≤ s'.sd := by
  cases h with | ev e ht => rw [ann_stf_sd]; exact ht

-- ---------------------------------------------------------------------------
-- Status-date monotonicity:  whole trace
-- ---------------------------------------------------------------------------

theorem pam_trace_mono {s s' : State} (tr : PAM.Trace ct rf s s') : s.sd ≤ s'.sd := by
  induction tr with
  | refl => exact Nat.le_refl _
  | step h _ ih => exact Nat.le_trans (pam_step_mono h) ih

theorem lam_trace_mono {s s' : State} (tr : LAM.Trace ct rf s s') : s.sd ≤ s'.sd := by
  induction tr with
  | refl => exact Nat.le_refl _
  | step h _ ih => exact Nat.le_trans (lam_step_mono h) ih

theorem nam_trace_mono {s s' : State} (tr : NAM.Trace ct rf s s') : s.sd ≤ s'.sd := by
  induction tr with
  | refl => exact Nat.le_refl _
  | step h _ ih => exact Nat.le_trans (nam_step_mono h) ih

theorem ann_trace_mono {s s' : State} (tr : ANN.Trace ct rf s s') : s.sd ≤ s'.sd := by
  induction tr with
  | refl => exact Nat.le_refl _
  | step h _ ih => exact Nat.le_trans (ann_step_mono h) ih

-- ---------------------------------------------------------------------------
-- Maturity and termination zero out principal/interest/fees
-- ---------------------------------------------------------------------------

theorem pam_md_nt   (t : Time) (s : State) : (PAM.stf_MD ct t s).nt   = 0.0 := rfl
theorem pam_md_ipac (t : Time) (s : State) : (PAM.stf_MD ct t s).ipac = 0.0 := rfl
theorem pam_md_feac (t : Time) (s : State) : (PAM.stf_MD ct t s).feac = 0.0 := rfl

theorem pam_td_nt   (t : Time) (s : State) : (PAM.stf_TD ct t s).nt   = 0.0 := rfl
theorem pam_td_ipac (t : Time) (s : State) : (PAM.stf_TD ct t s).ipac = 0.0 := rfl
theorem pam_td_ipnr (t : Time) (s : State) : (PAM.stf_TD ct t s).ipnr = 0.0 := rfl

/-- The maturity event of a *trace step* zeroes the notional. -/
theorem pam_md_step_zero {s s' : State} (he : s' = PAM.stf_MD ct t s) : s'.nt = 0.0 := by
  subst he; rfl

-- ---------------------------------------------------------------------------
-- Initial exchange sets the signed notional
-- ---------------------------------------------------------------------------

theorem pam_ied_nt (t : Time) (s : State) :
    (PAM.stf_IED ct t s).nt = sign (Terms.cntrl ct) * Terms.nt ct := rfl

-- ---------------------------------------------------------------------------
-- Determinism: the post-state is a function of the event and time
-- ---------------------------------------------------------------------------

/-- Determinism, as a corollary of relational↔functional agreement: any two LAM
    steps out of `s` that land on the functional image of the *same* event and
    time necessarily coincide.  (The relation was defined as the graph of the
    function `stf`, so the successor is determined once the event/time are
    fixed; see `Agree.lam_step_to_fun`.) -/
theorem lam_step_det {s s₁ s₂ : State} {e : EventType} {t : Time}
    (he₁ : s₁ = LAM.stf ct rf e t s) (he₂ : s₂ = LAM.stf ct rf e t s) : s₁ = s₂ :=
  he₁.trans he₂.symm

end Actus.Contract.Lending.Properties
