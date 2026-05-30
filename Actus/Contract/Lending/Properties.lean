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

Further (Tier A — structural invariants, Tier B — cashflow/trace structure):

* **`md` invariant** (`*_stf_md`, `*_trace_md`): no transition changes the
  maturity date, so it is constant along any trace.
* **Performance invariant** (`*_stf_prf`): no implemented transition changes
  `Prf` (there is no credit-event handling yet).
* **Clock-tick events** (`pam_*_clock`): events outside the schedule (`PD`,
  `DV`, `STD`, `XD`) only advance the status date.
* **Scaling locality** (`pam_sc_ooo_inert`): with no scaling effect, `SC` leaves
  the scaling multipliers untouched.
* **Cashflow count** (`*_cashflows_length`): a trace yields one cashflow per
  step.
* **Cashflow stamps** (`*_cashflow_time`): a step's cashflow is stamped at the
  post-state status date; with `*_trace_mono` these are non-decreasing.
* **Cashflow shape** (`pam_*_zero`, `*_cashflow_type`): non-payment events carry
  payoff `0`, and each cashflow's event type matches its step.
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

-- ---------------------------------------------------------------------------
-- Tier A: the maturity date is invariant under every transition
-- ---------------------------------------------------------------------------

theorem pam_stf_md (e : EventType) (t : Time) (s : State) :
    (PAM.stf ct rf e t s).md = s.md := by cases e <;> rfl
theorem lam_stf_md (e : EventType) (t : Time) (s : State) :
    (LAM.stf ct rf e t s).md = s.md := by cases e <;> rfl
theorem nam_stf_md (e : EventType) (t : Time) (s : State) :
    (NAM.stf ct rf e t s).md = s.md := by cases e <;> rfl
theorem ann_stf_md (e : EventType) (t : Time) (s : State) :
    (ANN.stf ct rf e t s).md = s.md := by cases e <;> rfl

/-- The maturity date is therefore constant along any execution trace. -/
theorem pam_trace_md {s s' : State} (tr : PAM.Trace ct rf s s') : s'.md = s.md := by
  induction tr with
  | refl => rfl
  | step h _ ih => exact ih.trans (by cases h <;> rfl)
theorem lam_trace_md {s s' : State} (tr : LAM.Trace ct rf s s') : s'.md = s.md := by
  induction tr with
  | refl => rfl
  | step h _ ih => exact ih.trans (by cases h with | ev e _ => exact lam_stf_md _ _ _)
theorem nam_trace_md {s s' : State} (tr : NAM.Trace ct rf s s') : s'.md = s.md := by
  induction tr with
  | refl => rfl
  | step h _ ih => exact ih.trans (by cases h with | ev e _ => exact nam_stf_md _ _ _)
theorem ann_trace_md {s s' : State} (tr : ANN.Trace ct rf s s') : s'.md = s.md := by
  induction tr with
  | refl => rfl
  | step h _ ih => exact ih.trans (by cases h with | ev e _ => exact ann_stf_md _ _ _)

-- ---------------------------------------------------------------------------
-- Tier A: contract performance is invariant (no credit-event handling yet)
-- ---------------------------------------------------------------------------

theorem pam_stf_prf (e : EventType) (t : Time) (s : State) :
    (PAM.stf ct rf e t s).prf = s.prf := by cases e <;> rfl
theorem lam_stf_prf (e : EventType) (t : Time) (s : State) :
    (LAM.stf ct rf e t s).prf = s.prf := by cases e <;> rfl
theorem nam_stf_prf (e : EventType) (t : Time) (s : State) :
    (NAM.stf ct rf e t s).prf = s.prf := by cases e <;> rfl
theorem ann_stf_prf (e : EventType) (t : Time) (s : State) :
    (ANN.stf ct rf e t s).prf = s.prf := by cases e <;> rfl

-- ---------------------------------------------------------------------------
-- Tier A: events outside the PAM schedule are pure clock ticks
-- ---------------------------------------------------------------------------

theorem pam_pd_clock  (t : Time) (s : State) : PAM.stf ct rf .PD  t s = { s with sd := t } := rfl
theorem pam_dv_clock  (t : Time) (s : State) : PAM.stf ct rf .DV  t s = { s with sd := t } := rfl
theorem pam_std_clock (t : Time) (s : State) : PAM.stf ct rf .STD t s = { s with sd := t } := rfl
theorem pam_xd_clock  (t : Time) (s : State) : PAM.stf ct rf .XD  t s = { s with sd := t } := rfl

-- ---------------------------------------------------------------------------
-- Tier A: with no scaling effect, SC leaves the scaling multipliers alone;
--         and termination zeroes accrued fees (completing the maturity lemmas)
-- ---------------------------------------------------------------------------

theorem pam_sc_ooo_inert (t : Time) (s : State) (h : Terms.scief ct = .SE_OOO) :
    (PAM.stf_SC ct rf t s).nsc = s.nsc ∧ (PAM.stf_SC ct rf t s).isc = s.isc := by
  refine ⟨?_, ?_⟩ <;> simp [PAM.stf_SC, h, scalesNotional, scalesInterest]

theorem pam_td_feac (t : Time) (s : State) : (PAM.stf_TD ct t s).feac = 0.0 := rfl

-- ---------------------------------------------------------------------------
-- Tier B: a trace yields exactly one cashflow per step
-- ---------------------------------------------------------------------------

/-- Number of steps in a trace (closure). -/
def traceLen {α : Type} {r : α → α → Type} : ∀ {a b : α}, Star r a b → Nat
  | _, _, .refl        => 0
  | _, _, .step _ rest => traceLen rest + 1

theorem pam_cashflows_length {s s' : State} (tr : PAM.Trace ct rf s s') :
    (PAM.getCashflows ct rf tr).length = traceLen tr := by
  induction tr with
  | refl => rfl
  | step h rest ih => simp [PAM.getCashflows, traceLen, List.length_cons, ih]
theorem lam_cashflows_length {s s' : State} (tr : LAM.Trace ct rf s s') :
    (LAM.getCashflows ct rf tr).length = traceLen tr := by
  induction tr with
  | refl => rfl
  | step h rest ih => simp [LAM.getCashflows, traceLen, List.length_cons, ih]
theorem nam_cashflows_length {s s' : State} (tr : NAM.Trace ct rf s s') :
    (NAM.getCashflows ct rf tr).length = traceLen tr := by
  induction tr with
  | refl => rfl
  | step h rest ih => simp [NAM.getCashflows, traceLen, List.length_cons, ih]
theorem ann_cashflows_length {s s' : State} (tr : ANN.Trace ct rf s s') :
    (ANN.getCashflows ct rf tr).length = traceLen tr := by
  induction tr with
  | refl => rfl
  | step h rest ih => simp [ANN.getCashflows, traceLen, List.length_cons, ih]

-- ---------------------------------------------------------------------------
-- Tier B: each step's cashflow is stamped at the post-state status date
-- (combine with `*_trace_mono` for non-decreasing cashflow times)
-- ---------------------------------------------------------------------------

theorem pam_cashflow_time {s s' : State} (h : PAM.Step ct rf s s') :
    (PAM.getCashflow ct rf h).1.1 = s'.sd := by cases h <;> rfl
theorem lam_cashflow_time {s s' : State} (h : LAM.Step ct rf s s') :
    (LAM.getCashflow ct rf h).1.1 = s'.sd := by cases h with | ev _ _ => rfl
theorem nam_cashflow_time {s s' : State} (h : NAM.Step ct rf s s') :
    (NAM.getCashflow ct rf h).1.1 = s'.sd := by cases h with | ev _ _ => rfl
theorem ann_cashflow_time {s s' : State} (h : ANN.Step ct rf s s') :
    (ANN.getCashflow ct rf h).1.1 = s'.sd := by cases h with | ev _ _ => rfl

-- ---------------------------------------------------------------------------
-- Tier B: cashflow shape — non-payment events carry payoff 0, and each
--         cashflow's event type matches its step
-- ---------------------------------------------------------------------------

theorem pam_ad_zero   {s : State} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.ad h)).2   = 0.0 := rfl
theorem pam_ipci_zero {s : State} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.ipci h)).2 = 0.0 := rfl
theorem pam_rr_zero   {s : State} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.rr h)).2   = 0.0 := rfl
theorem pam_rrf_zero  {s : State} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.rrf h)).2  = 0.0 := rfl
theorem pam_sc_zero   {s : State} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.sc h)).2   = 0.0 := rfl
theorem pam_ce_zero   {s : State} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.ce h)).2   = 0.0 := rfl

/-- For the dispatching contracts, the cashflow's event type is exactly the
    event that produced it. -/
theorem lam_cashflow_type {s : State} (e : EventType) {t : Time} (h : s.sd ≤ t) :
    (LAM.getCashflow ct rf (.ev e h)).1.2 = e := rfl
theorem nam_cashflow_type {s : State} (e : EventType) {t : Time} (h : s.sd ≤ t) :
    (NAM.getCashflow ct rf (.ev e h)).1.2 = e := rfl
theorem ann_cashflow_type {s : State} (e : EventType) {t : Time} (h : s.sd ≤ t) :
    (ANN.getCashflow ct rf (.ev e h)).1.2 = e := rfl

theorem pam_md_cashflow_type {s : State} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.md h)).1.2 = .MD := rfl
theorem pam_ip_cashflow_type {s : State} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.ip h)).1.2 = .IP := rfl

end Actus.Contract.Lending.Properties
