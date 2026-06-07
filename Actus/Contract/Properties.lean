/-
## Metatheorems (lending family)

Two kinds of metatheorem live here:

**Structural** properties (generic over the amount type `α`) — proved from the
*shape* of the transitions, no arithmetic:

* **Status-date advance** (`*_stf_sd`): every event sets `Sd` to its event time.
* **Monotonicity** (`*_step_mono`, `*_trace_mono`): status dates are
  non-decreasing along any execution trace.
* **Maturity / termination** (`*_md_*`, `*_td_*`): `MD` zeroes notional, accrued
  interest and fees; `TD` additionally zeroes the rate.
* **`md` / `prf` invariants**, **clock-tick events**, **scaling locality**,
  **cashflow count / stamps / shape** (Tiers A–B).

**Quantitative** bounds (Tier C) — proved over `ℝ`, the relational
specification's amount type.  These are exactly the properties that *cannot* be
stated over `Float` (a single `NaN` falsifies `a ≤ a`, `min a b ≤ b`, …), and
are genuine theorems over the ordered field `ℝ`:

* **Rate cap/floor bound** (`pam_rr_rate_mem`, `ann_rr_rate_mem`): after a rate
  reset the nominal rate lies within the life floor/cap `[RRLF, RRLC]`.
* **Redemption non-overshoot** (`redeemed_no_overshoot`, `lam_pr_nt_mem`): a
  principal redemption never drives the (sign-normalised) notional below `0` or
  above its previous magnitude — the notional stays in `[0, Nt]`.
-/

import Actus.Contract.Agree
import Actus.Closures
import Mathlib.Tactic.Ring

namespace Actus.Contract.Properties

open Actus.Protocol
open Actus.Closures
open Actus.Contract
open Actus.Util.Conventions (sign)
open Actus (Amount)

set_option linter.unusedSectionVars false

variable {α : Type} [Amount α] [DecidableLE α]
variable {ct : Terms α} {rf : RiskFactorEnv α} {t : Time}

-- ---------------------------------------------------------------------------
-- Every event advances the status date to its event time
-- ---------------------------------------------------------------------------

theorem pam_stf_sd (e : EventType) (t : Time) (s : State α) :
    (PAM.stf ct rf e t s).sd = t := by cases e <;> rfl

theorem lam_stf_sd (e : EventType) (t : Time) (s : State α) :
    (LAM.stf ct rf e t s).sd = t := by cases e <;> rfl

theorem nam_stf_sd (e : EventType) (t : Time) (s : State α) :
    (NAM.stf ct rf e t s).sd = t := by cases e <;> rfl

theorem ann_stf_sd (e : EventType) (t : Time) (s : State α) :
    (ANN.stf ct rf e t s).sd = t := by cases e <;> rfl

-- ---------------------------------------------------------------------------
-- Status-date monotonicity:  one step
-- ---------------------------------------------------------------------------

theorem pam_step_mono {s s' : State α} (h : PAM.Step ct rf s s') : s.sd ≤ s'.sd := by
  cases h <;> assumption

theorem lam_step_mono {s s' : State α} (h : LAM.Step ct rf s s') : s.sd ≤ s'.sd := by
  cases h with | ev e ht => rw [lam_stf_sd]; exact ht

theorem nam_step_mono {s s' : State α} (h : NAM.Step ct rf s s') : s.sd ≤ s'.sd := by
  cases h with | ev e ht => rw [nam_stf_sd]; exact ht

theorem ann_step_mono {s s' : State α} (h : ANN.Step ct rf s s') : s.sd ≤ s'.sd := by
  cases h with | ev e ht => rw [ann_stf_sd]; exact ht

-- ---------------------------------------------------------------------------
-- Status-date monotonicity:  whole trace
-- ---------------------------------------------------------------------------

theorem pam_trace_mono {s s' : State α} (tr : PAM.Trace ct rf s s') : s.sd ≤ s'.sd := by
  induction tr with
  | refl => exact Nat.le_refl _
  | step h _ ih => exact Nat.le_trans (pam_step_mono h) ih

theorem lam_trace_mono {s s' : State α} (tr : LAM.Trace ct rf s s') : s.sd ≤ s'.sd := by
  induction tr with
  | refl => exact Nat.le_refl _
  | step h _ ih => exact Nat.le_trans (lam_step_mono h) ih

theorem nam_trace_mono {s s' : State α} (tr : NAM.Trace ct rf s s') : s.sd ≤ s'.sd := by
  induction tr with
  | refl => exact Nat.le_refl _
  | step h _ ih => exact Nat.le_trans (nam_step_mono h) ih

theorem ann_trace_mono {s s' : State α} (tr : ANN.Trace ct rf s s') : s.sd ≤ s'.sd := by
  induction tr with
  | refl => exact Nat.le_refl _
  | step h _ ih => exact Nat.le_trans (ann_step_mono h) ih

-- ---------------------------------------------------------------------------
-- Maturity and termination zero out principal/interest/fees
-- ---------------------------------------------------------------------------

theorem pam_md_nt   (t : Time) (s : State α) : (PAM.stf_MD t s).nt   = (0 : α) := rfl
theorem pam_md_ipac (t : Time) (s : State α) : (PAM.stf_MD t s).ipac = (0 : α) := rfl
theorem pam_md_feac (t : Time) (s : State α) : (PAM.stf_MD t s).feac = (0 : α) := rfl

theorem pam_td_nt   (t : Time) (s : State α) : (PAM.stf_TD t s).nt   = (0 : α) := rfl
theorem pam_td_ipac (t : Time) (s : State α) : (PAM.stf_TD t s).ipac = (0 : α) := rfl
theorem pam_td_ipnr (t : Time) (s : State α) : (PAM.stf_TD t s).ipnr = (0 : α) := rfl
theorem pam_td_feac (t : Time) (s : State α) : (PAM.stf_TD t s).feac = (0 : α) := rfl

/-- The maturity event of a *trace step* zeroes the notional. -/
theorem pam_md_step_zero {s s' : State α} (he : s' = PAM.stf_MD t s) : s'.nt = (0 : α) := by
  subst he; rfl

-- ---------------------------------------------------------------------------
-- Initial exchange sets the signed notional
-- ---------------------------------------------------------------------------

theorem pam_ied_nt (t : Time) (s : State α) :
    (PAM.stf_IED ct t s).nt = sign (Terms.cntrl ct) * Terms.nt ct := rfl

-- ---------------------------------------------------------------------------
-- Determinism: the post-state is a function of the event and time
-- ---------------------------------------------------------------------------

/-- Determinism, as a corollary of relational↔functional agreement: any two LAM
    steps out of `s` on the functional image of the *same* event and time
    coincide.  (`Step` is the graph of the function `stf`.) -/
theorem lam_step_det {s s₁ s₂ : State α} {e : EventType} {t : Time}
    (he₁ : s₁ = LAM.stf ct rf e t s) (he₂ : s₂ = LAM.stf ct rf e t s) : s₁ = s₂ :=
  he₁.trans he₂.symm

-- ---------------------------------------------------------------------------
-- Tier A: the maturity date is invariant under every transition
-- ---------------------------------------------------------------------------

theorem pam_stf_md (e : EventType) (t : Time) (s : State α) :
    (PAM.stf ct rf e t s).md = s.md := by cases e <;> rfl
theorem lam_stf_md (e : EventType) (t : Time) (s : State α) :
    (LAM.stf ct rf e t s).md = s.md := by cases e <;> rfl
theorem nam_stf_md (e : EventType) (t : Time) (s : State α) :
    (NAM.stf ct rf e t s).md = s.md := by cases e <;> rfl
theorem ann_stf_md (e : EventType) (t : Time) (s : State α) :
    (ANN.stf ct rf e t s).md = s.md := by cases e <;> rfl

/-- The maturity date is therefore constant along any execution trace. -/
theorem pam_trace_md {s s' : State α} (tr : PAM.Trace ct rf s s') : s'.md = s.md := by
  induction tr with
  | refl => rfl
  | step h _ ih => exact ih.trans (by cases h <;> rfl)
theorem lam_trace_md {s s' : State α} (tr : LAM.Trace ct rf s s') : s'.md = s.md := by
  induction tr with
  | refl => rfl
  | step h _ ih => exact ih.trans (by cases h with | ev e _ => exact lam_stf_md _ _ _)
theorem nam_trace_md {s s' : State α} (tr : NAM.Trace ct rf s s') : s'.md = s.md := by
  induction tr with
  | refl => rfl
  | step h _ ih => exact ih.trans (by cases h with | ev e _ => exact nam_stf_md _ _ _)
theorem ann_trace_md {s s' : State α} (tr : ANN.Trace ct rf s s') : s'.md = s.md := by
  induction tr with
  | refl => rfl
  | step h _ ih => exact ih.trans (by cases h with | ev e _ => exact ann_stf_md _ _ _)

-- ---------------------------------------------------------------------------
-- Tier A: contract performance is invariant (no credit-event handling yet)
-- ---------------------------------------------------------------------------

theorem pam_stf_prf (e : EventType) (t : Time) (s : State α) :
    (PAM.stf ct rf e t s).prf = s.prf := by cases e <;> rfl
theorem lam_stf_prf (e : EventType) (t : Time) (s : State α) :
    (LAM.stf ct rf e t s).prf = s.prf := by cases e <;> rfl
theorem nam_stf_prf (e : EventType) (t : Time) (s : State α) :
    (NAM.stf ct rf e t s).prf = s.prf := by cases e <;> rfl
theorem ann_stf_prf (e : EventType) (t : Time) (s : State α) :
    (ANN.stf ct rf e t s).prf = s.prf := by cases e <;> rfl

-- ---------------------------------------------------------------------------
-- Tier A: events outside the PAM schedule are pure clock ticks
-- ---------------------------------------------------------------------------

theorem pam_pd_clock  (t : Time) (s : State α) : PAM.stf ct rf .PD  t s = { s with sd := t } := rfl
theorem pam_dv_clock  (t : Time) (s : State α) : PAM.stf ct rf .DV  t s = { s with sd := t } := rfl
theorem pam_std_clock (t : Time) (s : State α) : PAM.stf ct rf .STD t s = { s with sd := t } := rfl
theorem pam_xd_clock  (t : Time) (s : State α) : PAM.stf ct rf .XD  t s = { s with sd := t } := rfl

-- ---------------------------------------------------------------------------
-- Tier A: with no scaling effect, SC leaves the scaling multipliers alone
-- ---------------------------------------------------------------------------

theorem pam_sc_ooo_inert (t : Time) (s : State α) (h : Terms.scief ct = .SE_OOO) :
    (PAM.stf_SC ct rf t s).nsc = s.nsc ∧ (PAM.stf_SC ct rf t s).isc = s.isc := by
  refine ⟨?_, ?_⟩ <;> simp [PAM.stf_SC, h, scalesNotional, scalesInterest]

-- ---------------------------------------------------------------------------
-- Tier B: a trace yields exactly one cashflow per step
-- ---------------------------------------------------------------------------

/-- Number of steps in a trace (closure). -/
def traceLen {β : Type} {r : β → β → Type} : ∀ {a b : β}, Star r a b → Nat
  | _, _, .refl        => 0
  | _, _, .step _ rest => traceLen rest + 1

theorem pam_cashflows_length {s s' : State α} (tr : PAM.Trace ct rf s s') :
    (PAM.getCashflows ct rf tr).length = traceLen tr := by
  induction tr with
  | refl => rfl
  | step h rest ih => simp [PAM.getCashflows, traceLen, List.length_cons, ih]
theorem lam_cashflows_length {s s' : State α} (tr : LAM.Trace ct rf s s') :
    (LAM.getCashflows ct rf tr).length = traceLen tr := by
  induction tr with
  | refl => rfl
  | step h rest ih => simp [LAM.getCashflows, traceLen, List.length_cons, ih]
theorem nam_cashflows_length {s s' : State α} (tr : NAM.Trace ct rf s s') :
    (NAM.getCashflows ct rf tr).length = traceLen tr := by
  induction tr with
  | refl => rfl
  | step h rest ih => simp [NAM.getCashflows, traceLen, List.length_cons, ih]
theorem ann_cashflows_length {s s' : State α} (tr : ANN.Trace ct rf s s') :
    (ANN.getCashflows ct rf tr).length = traceLen tr := by
  induction tr with
  | refl => rfl
  | step h rest ih => simp [ANN.getCashflows, traceLen, List.length_cons, ih]

-- ---------------------------------------------------------------------------
-- Tier B: each step's cashflow is stamped at the post-state status date
-- ---------------------------------------------------------------------------

theorem pam_cashflow_time {s s' : State α} (h : PAM.Step ct rf s s') :
    (PAM.getCashflow ct rf h).1.1 = s'.sd := by cases h <;> rfl
theorem lam_cashflow_time {s s' : State α} (h : LAM.Step ct rf s s') :
    (LAM.getCashflow ct rf h).1.1 = s'.sd := by cases h with | ev _ _ => rfl
theorem nam_cashflow_time {s s' : State α} (h : NAM.Step ct rf s s') :
    (NAM.getCashflow ct rf h).1.1 = s'.sd := by cases h with | ev _ _ => rfl
theorem ann_cashflow_time {s s' : State α} (h : ANN.Step ct rf s s') :
    (ANN.getCashflow ct rf h).1.1 = s'.sd := by cases h with | ev _ _ => rfl

-- ---------------------------------------------------------------------------
-- Tier B: cashflow shape — non-payment events carry payoff 0, and each
--         cashflow's event type matches its step
-- ---------------------------------------------------------------------------

theorem pam_ad_zero   {s : State α} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.ad h)).2   = (0 : α) := rfl
theorem pam_ipci_zero {s : State α} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.ipci h)).2 = (0 : α) := rfl
theorem pam_rr_zero   {s : State α} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.rr h)).2   = (0 : α) := rfl
theorem pam_rrf_zero  {s : State α} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.rrf h)).2  = (0 : α) := rfl
theorem pam_sc_zero   {s : State α} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.sc h)).2   = (0 : α) := rfl
theorem pam_ce_zero   {s : State α} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.ce h)).2   = (0 : α) := rfl

/-- For the dispatching contracts, the cashflow's event type is exactly the
    event that produced it. -/
theorem lam_cashflow_type {s : State α} (e : EventType) {t : Time} (h : s.sd ≤ t) :
    (LAM.getCashflow ct rf (.ev e h)).1.2 = e := rfl
theorem nam_cashflow_type {s : State α} (e : EventType) {t : Time} (h : s.sd ≤ t) :
    (NAM.getCashflow ct rf (.ev e h)).1.2 = e := rfl
theorem ann_cashflow_type {s : State α} (e : EventType) {t : Time} (h : s.sd ≤ t) :
    (ANN.getCashflow ct rf (.ev e h)).1.2 = e := rfl

theorem pam_md_cashflow_type {s : State α} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.md h)).1.2 = .MD := rfl
theorem pam_ip_cashflow_type {s : State α} {t : Time} (h : s.sd ≤ t) :
    (PAM.getCashflow ct rf (.ip h)).1.2 = .IP := rfl

-- ---------------------------------------------------------------------------
-- Tier C (over ℝ): quantitative bounds that Float cannot support
-- ---------------------------------------------------------------------------

/-- A two-sided clamp `min (max x lf) lc` lands in `[lf, lc]` whenever the floor
    does not exceed the cap.  The order lemmas come from Mathlib's `ℝ`. -/
theorem clamp_mem (lf lc x : ℝ) (h : lf ≤ lc) :
    lf ≤ min (max x lf) lc ∧ min (max x lf) lc ≤ lc :=
  ⟨le_min (le_max_right x lf) h, min_le_right _ _⟩

/-- **Rate cap/floor bound (PAM).**  After a rate reset the nominal rate lies
    within the life floor/cap window `[RRLF, RRLC]` (when both are present and
    well-ordered).  Unprovable over `Float`; a theorem over `ℝ`. -/
theorem pam_rr_rate_mem (ct : Terms ℝ) (rf : RiskFactorEnv ℝ) (t : Time) (s : State ℝ)
    {lf lc : ℝ} (hf : ct.lifeFloor = some lf) (hc : ct.lifeCap = some lc) (h : lf ≤ lc) :
    lf ≤ (PAM.stf_RR ct rf t s).ipnr ∧ (PAM.stf_RR ct rf t s).ipnr ≤ lc := by
  simp only [PAM.stf_RR, clampHi, clampLo, hf, hc]
  exact clamp_mem lf lc _ h

/-- **Rate cap/floor bound (ANN).**  ANN's rate reset reuses PAM's rate logic, so
    the same window bound holds. -/
theorem ann_rr_rate_mem (ct : Terms ℝ) (rf : RiskFactorEnv ℝ) (t : Time) (s : State ℝ)
    {lf lc : ℝ} (hf : ct.lifeFloor = some lf) (hc : ct.lifeCap = some lc) (h : lf ≤ lc) :
    lf ≤ (ANN.stf_RR ct rf t s).ipnr ∧ (ANN.stf_RR ct rf t s).ipnr ≤ lc := by
  -- `ANN.stf_RR` keeps PAM's `ipnr`; only `ipac`/`prnxt` differ.
  simpa [ANN.stf_RR] using pam_rr_rate_mem ct rf t s hf hc h

/-- **Redemption non-overshoot (core).**  When the notional and instalment are
    both nonnegative (the sign-normalised case), the post-redemption notional
    `Nt − redeemed Nt Prnxt` stays in `[0, Nt]`: a redemption never overshoots
    `0`, nor increases the magnitude.  Needs a total order — `ℝ`, not `Float`. -/
theorem redeemed_no_overshoot (nt prnxt : ℝ) (hnt : 0 ≤ nt) (hp : 0 ≤ prnxt) :
    0 ≤ nt - LAM.redeemed nt prnxt ∧ nt - LAM.redeemed nt prnxt ≤ nt := by
  unfold LAM.redeemed
  simp only [Amount.abs_real, abs_of_nonneg hnt, abs_of_nonneg hp]
  split
  · -- nt ≤ prnxt ⇒ redeem the whole notional, leaving 0
    simp only [sub_self]
    exact ⟨le_rfl, hnt⟩
  · -- prnxt < nt ⇒ leave the positive remainder nt − prnxt
    rename_i hcon
    have hlt : prnxt < nt := not_le.mp hcon
    exact ⟨sub_nonneg.mpr (le_of_lt hlt), sub_le_self nt hp⟩

/-- **Redemption non-overshoot (LAM `PR` step).**  Specialised to the actual
    `STF_PR_LAM` next-state: the notional after a principal redemption stays in
    `[0, Nt]`. -/
theorem lam_pr_nt_mem (ct : Terms ℝ) (rf : RiskFactorEnv ℝ) (t : Time) (s : State ℝ)
    (hnt : 0 ≤ s.nt) (hp : 0 ≤ s.prnxt) :
    0 ≤ (LAM.stf_PR ct rf t s).nt ∧ (LAM.stf_PR ct rf t s).nt ≤ s.nt := by
  simpa [LAM.stf_PR] using redeemed_no_overshoot s.nt s.prnxt hnt hp

-- ---------------------------------------------------------------------------
-- Tier D: which state variables each event touches (structural, generic)
-- ---------------------------------------------------------------------------

/-- A rate reset never moves principal — only the rate (and accruals/`Sd`). -/
theorem pam_rr_preserves_nt (t : Time) (s : State α) :
    (PAM.stf_RR ct rf t s).nt = s.nt := rfl

/-- Prepayment reduces the notional by exactly the observed prepayment amount. -/
theorem pam_pp_nt (t : Time) (s : State α) :
    (PAM.stf_PP ct rf t s).nt = s.nt - rf.prepayment t := rfl

/-- Interest capitalization (`IPCI`) moves the accrued interest into the
    notional and resets accrued interest to `0` — value is conserved, not
    created.  Holds definitionally at any amount type. -/
theorem pam_ipci_capitalizes (t : Time) (s : State α) :
    (PAM.stf_IPCI ct rf t s).nt = s.nt + PAM.ipacAccr rf t s
    ∧ (PAM.stf_IPCI ct rf t s).ipac = 0 := ⟨rfl, rfl⟩

-- ---------------------------------------------------------------------------
-- Tier D: redemption cap, full vs. partial (generic shape; ℝ for the amounts)
-- ---------------------------------------------------------------------------

/-- When the instalment covers the whole (sign-normalised) notional, the entire
    notional is redeemed. -/
theorem lam_redeemed_full {nt prnxt : α} (h : Amount.abs nt ≤ Amount.abs prnxt) :
    LAM.redeemed nt prnxt = nt := by
  unfold LAM.redeemed; exact if_pos h

/-- Otherwise exactly the instalment is redeemed. -/
theorem lam_redeemed_partial {nt prnxt : α} (h : ¬ Amount.abs nt ≤ Amount.abs prnxt) :
    LAM.redeemed nt prnxt = prnxt := by
  unfold LAM.redeemed; exact if_neg h

/-- **Redeemed amount is bounded by the notional magnitude** (sign-free): a
    redemption never pays out more than the outstanding notional. Over `ℝ`. -/
theorem redeemed_abs_le (nt prnxt : ℝ) : |LAM.redeemed nt prnxt| ≤ |nt| := by
  unfold LAM.redeemed
  simp only [Amount.abs_real]
  split
  · exact le_rfl
  · rename_i h; exact le_of_lt (not_le.mp h)

/-- **Full repayment empties the notional.**  Once the instalment reaches the
    outstanding notional, the `PR` step drives it to exactly `0`. Over `ℝ`. -/
theorem lam_pr_full_repay (ct : Terms ℝ) (rf : RiskFactorEnv ℝ) (t : Time) (s : State ℝ)
    (h : |s.nt| ≤ |s.prnxt|) : (LAM.stf_PR ct rf t s).nt = 0 := by
  have hr : LAM.redeemed s.nt s.prnxt = s.nt := lam_redeemed_full (by simpa [Amount.abs_real])
  simp only [LAM.stf_PR, hr, sub_self]

/-- **Strict amortization.**  With a strictly positive notional and instalment,
    a `PR` step strictly decreases the notional (progress toward repayment).
    Over `ℝ`. -/
theorem lam_pr_nt_lt (ct : Terms ℝ) (rf : RiskFactorEnv ℝ) (t : Time) (s : State ℝ)
    (hnt : 0 < s.nt) (hp : 0 < s.prnxt) : (LAM.stf_PR ct rf t s).nt < s.nt := by
  simp only [LAM.stf_PR]
  unfold LAM.redeemed
  simp only [Amount.abs_real, abs_of_nonneg (le_of_lt hnt), abs_of_nonneg (le_of_lt hp)]
  split
  · rw [sub_self]; exact hnt
  · exact sub_lt_self _ hp

-- ---------------------------------------------------------------------------
-- Tier D: the rate reset with no caps is the raw repricing target (over ℝ)
-- ---------------------------------------------------------------------------

/-- With every cap/floor absent, a rate reset sets the rate to the raw market
    target `Oʳᶠ(RRMO,t)·RRMLT + RRSP` (the previous rate cancels). -/
theorem pam_rr_uncapped (ct : Terms ℝ) (rf : RiskFactorEnv ℝ) (t : Time) (s : State ℝ)
    (hpc : ct.periodCap = none) (hpf : ct.periodFloor = none)
    (hlc : ct.lifeCap = none) (hlf : ct.lifeFloor = none) :
    (PAM.stf_RR ct rf t s).ipnr = rf.marketRate t * Terms.rrmlt ct + Terms.rrsp ct := by
  simp only [PAM.stf_RR, clampHi, clampLo, hpc, hpf, hlc, hlf]
  ring

-- ---------------------------------------------------------------------------
-- Tier E (over ℝ): trace-level conservation of the notional under redemption
-- ---------------------------------------------------------------------------

/-- A **principal-redemption trace**: zero or more `PR` steps (each admissible,
    `Sd ≤ t`).  This is the sub-relation of `LAM.Trace` that only redeems
    principal — exactly the regime in which the notional should be conserved
    (other events like `IED`/`IPCI` reset or grow it). -/
inductive PRTrace (ct : Terms ℝ) (rf : RiskFactorEnv ℝ) : State ℝ → State ℝ → Prop
  | refl {s : State ℝ} : PRTrace ct rf s s
  | step {s : State ℝ} {t : Time} {s' : State ℝ} (ht : s.sd ≤ t)
      (rest : PRTrace ct rf (LAM.stf_PR ct rf t s) s') : PRTrace ct rf s s'

/-- **Trace-level conservation.**  Along a whole principal-redemption trace, the
    notional stays in `[0, Nt₀]`: it never goes negative (no overshoot past `0`)
    and never exceeds its starting value (monotone repayment).  Proved by
    induction on the trace from the single-step bound `lam_pr_nt_mem`; the
    instalment `Prnxt` is preserved by `PR`, so its nonnegativity propagates. -/
theorem prTrace_nt_mem {ct : Terms ℝ} {rf : RiskFactorEnv ℝ} {s s' : State ℝ}
    (h : PRTrace ct rf s s') : 0 ≤ s.nt → 0 ≤ s.prnxt → 0 ≤ s'.nt ∧ s'.nt ≤ s.nt := by
  induction h with
  | refl => exact fun hnt _ => ⟨hnt, le_rfl⟩
  | @step s t s' ht rest ih =>
      refine fun hnt hp => ?_
      have hstep := lam_pr_nt_mem ct rf t s hnt hp        -- 0 ≤ (PR s).nt ∧ (PR s).nt ≤ s.nt
      have hrec  := ih hstep.1 hp                         -- (Prnxt is preserved by PR, defeq)
      exact ⟨hrec.1, le_trans hrec.2 hstep.2⟩

/-- Magnitude form: a redemption trace never increases the notional's magnitude
    (`|Nt'| ≤ |Nt₀|`), given the sign-normalised nonnegative starting state. -/
theorem prTrace_abs_le {ct : Terms ℝ} {rf : RiskFactorEnv ℝ} {s s' : State ℝ}
    (h : PRTrace ct rf s s') (hnt : 0 ≤ s.nt) (hp : 0 ≤ s.prnxt) : |s'.nt| ≤ |s.nt| := by
  obtain ⟨h0, h1⟩ := prTrace_nt_mem h hnt hp
  rw [abs_of_nonneg h0, abs_of_nonneg hnt]; exact h1

/-- A `PRTrace` is a genuine `LAM` execution trace (each `PR` step is the
    `LAM.Step` for event `.PR`), so the conservation above is a statement about
    real executions, not a separate toy relation. -/
theorem prTrace_isTrace {ct : Terms ℝ} {rf : RiskFactorEnv ℝ} {s s' : State ℝ}
    (h : PRTrace ct rf s s') : Nonempty (LAM.Trace ct rf s s') := by
  induction h with
  | refl => exact ⟨.refl⟩
  | @step s t s' ht rest ih =>
      obtain ⟨tr⟩ := ih
      exact ⟨.step (LAM.Step.ev .PR ht) tr⟩

-- ---------------------------------------------------------------------------
-- Tier F (over ℝ): payoff bounds for the derivative & credit-enhancement
-- families (CAPFL / OPTNS / FUTUR / FXOUT / SWPPV / CEG / CEC / LAX).  Their
-- executable engines build cash flows over `Float`; these are the underlying
-- mathematical bounds the payoff kernels obey, stated over `ℝ`.
-- ---------------------------------------------------------------------------

/-- **Cap/floor intrinsic is non-negative.**  CAPFL pays
    `N·Y·(max(rate−cap,0) + max(floor−rate,0))` per period; the rate-excess kernel
    is always ≥ 0, so a long cap/floor never has a negative leg. -/
theorem capfl_intrinsic_nonneg (rate cap flr : ℝ) :
    0 ≤ max (rate - cap) 0 + max (flr - rate) 0 :=
  add_nonneg (le_max_right _ _) (le_max_right _ _)

/-- A cap pays nothing while the rate is at or below the cap. -/
theorem capfl_cap_inactive (rate cap : ℝ) (h : rate ≤ cap) : max (rate - cap) 0 = 0 :=
  max_eq_right (sub_nonpos.mpr h)

/-- A floor pays nothing while the rate is at or above the floor. -/
theorem capfl_floor_inactive (rate flr : ℝ) (h : flr ≤ rate) : max (flr - rate) 0 = 0 :=
  max_eq_right (sub_nonpos.mpr h)

/-- **Option intrinsic value is non-negative** — a European call (`max(S−K,0)`)
    and put (`max(K−S,0)`) never settle negative; the holder's payoff is ≥ 0. -/
theorem option_call_intrinsic_nonneg (s k : ℝ) : 0 ≤ max (s - k) 0 := le_max_right _ _
theorem option_put_intrinsic_nonneg  (s k : ℝ) : 0 ≤ max (k - s) 0 := le_max_right _ _

/-- A call is in the money exactly when the underlying exceeds the strike. -/
theorem option_call_pos_iff (s k : ℝ) : 0 < max (s - k) 0 ↔ k < s := by
  rw [lt_max_iff, sub_pos]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (lt_irrefl 0)
  · intro h; exact Or.inl h

/-- **Future/forward payoff is linear** — the settlement `S − F` carries no
    optional floor; gains and losses are symmetric. -/
theorem futur_payoff_linear (s f : ℝ) : (s - f) + (f - s) = 0 := by ring

/-- **FX delivery conservation.**  An FXOUT *delivery* settles the two notionals
    as `sign·Nt₁` and `−sign·Nt₂`; at a unit FX rate the two legs net to the
    par-difference `sign·(Nt₁ − Nt₂)`. -/
theorem fxout_delivery_sum (sgn nt1 nt2 : ℝ) :
    sgn * nt1 + (-(sgn * nt2)) = sgn * (nt1 - nt2) := by ring

/-- **Swap net settlement equals the leg sum.**  A plain-vanilla swap's per-period
    fixed leg `sign·N·fix·Y` and floating leg `−sign·N·flt·Y` net to the single
    cash flow `sign·N·(fix−flt)·Y` — exactly what the `deliverySettlement = "S"`
    fold computes from the two `D` legs. -/
theorem swppv_net_eq_legs (sgn n fix flt y : ℝ) :
    sgn * n * fix * y + (-(sgn * n * flt * y)) = sgn * n * (fix - flt) * y := by ring

/-- **Collateral cap.**  CEC settles `min(coverage·exposure, collateralValue)`, so
    the payout never exceeds the posted collateral … -/
theorem cec_payout_le_value (claim value : ℝ) : min claim value ≤ value := min_le_right _ _
/-- … nor the covered claim. -/
theorem cec_payout_le_claim (claim value : ℝ) : min claim value ≤ claim := min_le_left _ _

/-- A non-negative accumulator stays non-negative when folding in non-negative
    summands — the kernel behind exposure/notional aggregation. -/
theorem foldl_add_nonneg : ∀ (xs : List ℝ) (a : ℝ), 0 ≤ a →
    (∀ x ∈ xs, 0 ≤ x) → 0 ≤ xs.foldl (· + ·) a
  | [],      _, ha, _ => ha
  | x :: xs, a, ha, h =>
      foldl_add_nonneg xs (a + x) (add_nonneg ha (h x (List.mem_cons_self ..)))
        (fun y hy => h y (List.mem_cons_of_mem x hy))

/-- **Credit-enhancement exposure is non-negative.**  A guarantee's covered
    exposure is a sum of per-leg magnitudes (`|Nt| + accrued`); aggregating
    non-negative legs keeps it ≥ 0, hence the payout `coverage·exposure` has the
    contract-role sign and never flips. -/
theorem ceg_exposure_nonneg (legs : List ℝ) (h : ∀ x ∈ legs, 0 ≤ x) :
    0 ≤ legs.foldl (· + ·) 0 :=
  foldl_add_nonneg legs 0 le_rfl h

-- ===========================================================================
-- Metatheorems for the newly relational contracts: UMP, LAX, SWPPV
--
-- These now carry a `Step` model proven (in `Agree`) to be the graph of their
-- `stf`, so the same structural and quantitative metatheory the lending family
-- enjoys applies to them.  UMP and LAX use the standard dispatcher signature
-- (LAX with an extra schedule payload `x`); SWPPV emits two legs per period, so
-- its `IPFX`/`RR` events leave `Sd` untouched and only `IPFL` advances it.
-- ===========================================================================

-- --- Status-date advance (UMP, LAX) ---------------------------------------
-- Every UMP/LAX event sets `Sd` to its event time.  (SWPPV's fixed leg / reset
-- deliberately do *not* advance `Sd`; see `swppv_step_mono` instead.)

theorem ump_stf_sd (e : EventType) (t : Time) (s : State α) :
    (UMP.stf ct rf e t s).sd = t := by cases e <;> rfl

theorem lax_stf_sd (e : EventType) (x : α) (t : Time) (s : State α) :
    (LAX.stf ct rf e x t s).sd = t := by cases e <;> rfl

-- --- Status-date monotonicity (one step, then whole trace) ----------------

theorem ump_step_mono {s s' : State α} (h : UMP.Step ct rf s s') : s.sd ≤ s'.sd := by
  cases h with | ev e ht => rw [ump_stf_sd]; exact ht

theorem lax_step_mono {s s' : State α} (h : LAX.Step ct rf s s') : s.sd ≤ s'.sd := by
  cases h with | ev e x ht => rw [lax_stf_sd]; exact ht

/-- SWPPV monotonicity holds even though `IPFX`/`RR` keep `Sd`: a step either
    leaves `Sd` unchanged or advances it to the (admissible) event time. -/
theorem swppv_step_mono {s s' : State α} (h : SWPPV.Step ct rf s s') : s.sd ≤ s'.sd := by
  cases h with | ev e t ht => cases e <;> first | exact ht | exact Nat.le_refl _

theorem ump_trace_mono {s s' : State α} (tr : UMP.Trace ct rf s s') : s.sd ≤ s'.sd := by
  induction tr with
  | refl => exact Nat.le_refl _
  | step h _ ih => exact Nat.le_trans (ump_step_mono h) ih

theorem lax_trace_mono {s s' : State α} (tr : LAX.Trace ct rf s s') : s.sd ≤ s'.sd := by
  induction tr with
  | refl => exact Nat.le_refl _
  | step h _ ih => exact Nat.le_trans (lax_step_mono h) ih

theorem swppv_trace_mono {s s' : State α} (tr : SWPPV.Trace ct rf s s') : s.sd ≤ s'.sd := by
  induction tr with
  | refl => exact Nat.le_refl _
  | step h _ ih => exact Nat.le_trans (swppv_step_mono h) ih

-- --- Maturity-date and performance invariants -----------------------------

theorem ump_stf_md (e : EventType) (t : Time) (s : State α) :
    (UMP.stf ct rf e t s).md = s.md := by cases e <;> rfl
theorem lax_stf_md (e : EventType) (x : α) (t : Time) (s : State α) :
    (LAX.stf ct rf e x t s).md = s.md := by cases e <;> rfl
theorem swppv_stf_md (e : EventType) (t : Time) (s : State α) :
    (SWPPV.stf ct rf e t s).md = s.md := by cases e <;> rfl

theorem ump_stf_prf (e : EventType) (t : Time) (s : State α) :
    (UMP.stf ct rf e t s).prf = s.prf := by cases e <;> rfl
theorem lax_stf_prf (e : EventType) (x : α) (t : Time) (s : State α) :
    (LAX.stf ct rf e x t s).prf = s.prf := by cases e <;> rfl
theorem swppv_stf_prf (e : EventType) (t : Time) (s : State α) :
    (SWPPV.stf ct rf e t s).prf = s.prf := by cases e <;> rfl

/-- **Swap notional is never exchanged.**  No SWPPV event moves the notional —
    only the period boundary `Sd` (via `IPFL`) and the floating rate (via `RR`)
    change.  A swap exchanges interest, not principal. -/
theorem swppv_stf_nt (e : EventType) (t : Time) (s : State α) :
    (SWPPV.stf ct rf e t s).nt = s.nt := by cases e <;> rfl

-- --- Determinism (corollary of relational ↔ functional agreement) ---------

theorem ump_step_det {s s₁ s₂ : State α} {e : EventType} {t : Time}
    (he₁ : s₁ = UMP.stf ct rf e t s) (he₂ : s₂ = UMP.stf ct rf e t s) : s₁ = s₂ :=
  he₁.trans he₂.symm
theorem lax_step_det {s s₁ s₂ : State α} {e : EventType} {x : α} {t : Time}
    (he₁ : s₁ = LAX.stf ct rf e x t s) (he₂ : s₂ = LAX.stf ct rf e x t s) : s₁ = s₂ :=
  he₁.trans he₂.symm
theorem swppv_step_det {s s₁ s₂ : State α} {e : EventType} {t : Time}
    (he₁ : s₁ = SWPPV.stf ct rf e t s) (he₂ : s₂ = SWPPV.stf ct rf e t s) : s₁ = s₂ :=
  he₁.trans he₂.symm

-- --- One cashflow per step ------------------------------------------------

theorem ump_cashflows_length {s s' : State α} (tr : UMP.Trace ct rf s s') :
    (UMP.getCashflows ct rf tr).length = traceLen tr := by
  induction tr with
  | refl => rfl
  | step h rest ih => simp [UMP.getCashflows, traceLen, List.length_cons, ih]
theorem lax_cashflows_length {s s' : State α} (tr : LAX.Trace ct rf s s') :
    (LAX.getCashflows ct rf tr).length = traceLen tr := by
  induction tr with
  | refl => rfl
  | step h rest ih => simp [LAX.getCashflows, traceLen, List.length_cons, ih]
theorem swppv_cashflows_length {s s' : State α} (tr : SWPPV.Trace ct rf s s') :
    (SWPPV.getCashflows ct rf tr).length = traceLen tr := by
  induction tr with
  | refl => rfl
  | step h rest ih => simp [SWPPV.getCashflows, traceLen, List.length_cons, ih]

-- --- Cashflow stamp and type ----------------------------------------------
-- UMP/LAX stamp at the post-state status date (`= t`); SWPPV stamps at the
-- event time `t` directly (a period's two legs share one timestamp).

theorem ump_cashflow_time {s s' : State α} (h : UMP.Step ct rf s s') :
    (UMP.getCashflow ct rf h).1.1 = s'.sd := by cases h with | ev _ _ => rfl
theorem lax_cashflow_time {s s' : State α} (h : LAX.Step ct rf s s') :
    (LAX.getCashflow ct rf h).1.1 = s'.sd := by cases h with | ev _ _ _ => rfl
theorem swppv_cashflow_time {s : State α} (e : EventType) (t : Time) (h : s.sd ≤ t) :
    (SWPPV.getCashflow ct rf (.ev e t h)).1.1 = t := rfl

theorem ump_cashflow_type {s : State α} (e : EventType) {t : Time} (h : s.sd ≤ t) :
    (UMP.getCashflow ct rf (.ev e h)).1.2 = e := rfl
theorem lax_cashflow_type {s : State α} (e : EventType) (x : α) {t : Time} (h : s.sd ≤ t) :
    (LAX.getCashflow ct rf (.ev e x h)).1.2 = e := rfl
theorem swppv_cashflow_type {s : State α} (e : EventType) (t : Time) (h : s.sd ≤ t) :
    (SWPPV.getCashflow ct rf (.ev e t h)).1.2 = e := rfl

-- --- LAX principal moves: redemption / draw / maturity --------------------

/-- A LAX redemption reduces the notional by exactly the (signed) instalment. -/
theorem lax_pr_nt (x : α) (t : Time) (s : State α) :
    (LAX.stf_PR ct rf x t s).nt = s.nt - sign (Terms.cntrl ct) * x := rfl
/-- A LAX draw increases the notional by exactly the (signed) draw. -/
theorem lax_pi_nt (x : α) (t : Time) (s : State α) :
    (LAX.stf_PI ct rf x t s).nt = s.nt + sign (Terms.cntrl ct) * x := rfl
/-- LAX maturity pays out and zeroes the residual notional. -/
theorem lax_md_nt (t : Time) (s : State α) : (LAX.stf_MD rf t s).nt = (0 : α) := rfl

-- --- UMP capitalization conserves value -----------------------------------

/-- **UMP capitalization is value-conserving.**  An `IPCI` event grows the
    notional by the interest accrued over the period and resets the accrual; no
    cash leaves the contract (`pof = 0`). -/
theorem ump_ipci_value (t : Time) (s : State α) :
    (UMP.stf_IPCI rf t s).nt = s.nt + s.nt * s.ipnr * rf.yf s.sd t
    ∧ (UMP.stf_IPCI rf t s).ipac = 0 := ⟨rfl, rfl⟩

-- --- Tier C (over ℝ): quantitative bounds for SWPPV and UMP ----------------

/-- **Rate cap/floor bound (SWPPV).**  After a floating-rate reset the rate lies
    within the life floor/cap window `[lifeFloor, lifeCap]` (both present and
    well-ordered).  The swap analogue of `pam_rr_rate_mem`; a theorem over `ℝ`. -/
theorem swppv_rr_rate_mem (ct : Terms ℝ) (rf : RiskFactorEnv ℝ) (t : Time) (s : State ℝ)
    {lf lc : ℝ} (hf : ct.lifeFloor = some lf) (hc : ct.lifeCap = some lc) (h : lf ≤ lc) :
    lf ≤ (SWPPV.stf_RR ct rf t s).ipnr ∧ (SWPPV.stf_RR ct rf t s).ipnr ≤ lc := by
  simp only [SWPPV.stf_RR, clampHi, clampLo, hf, hc]
  exact clamp_mem lf lc _ h

/-- **Swap leg netting (kernel-level).**  A period's fixed leg `pof_IPFX` and
    floating leg `pof_IPFL` sum to `N·(fixedRate − floatRate)·Y` — exactly the
    single cash flow the `deliverySettlement = "S"` fold produces from the two
    gross legs.  Now stated on the *actual* `SWPPV.pof_*`, not abstract terms. -/
theorem swppv_pof_net (ct : Terms ℝ) (rf : RiskFactorEnv ℝ) (t : Time) (s : State ℝ) :
    SWPPV.pof_IPFX ct rf t s + SWPPV.pof_IPFL rf t s
      = s.nt * (Terms.ipnr ct - s.ipnr) * rf.yf s.sd t := by
  simp only [SWPPV.pof_IPFX, SWPPV.pof_IPFL]; ring

/-- **UMP compounding never shrinks the deposit.**  With a non-negative notional,
    rate and year fraction, an `IPCI` capitalization leaves the notional no
    smaller (interest only ever adds to a positive-rate deposit). Over `ℝ`. -/
theorem ump_ipci_nondecr (rf : RiskFactorEnv ℝ) (t : Time) (s : State ℝ)
    (hnt : 0 ≤ s.nt) (hr : 0 ≤ s.ipnr) (hy : 0 ≤ rf.yf s.sd t) :
    s.nt ≤ (UMP.stf_IPCI rf t s).nt := by
  simp only [UMP.stf_IPCI]
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hnt hr) hy)

-- --- SWPPV float-rate locality (generic) ----------------------------------

/-- **Only a rate reset moves the floating rate.**  Every non-`RR` SWPPV event
    (the two legs, clock ticks) leaves `Ipnr` untouched; the floating rate is
    changed exclusively by `RR`. -/
theorem swppv_ipnr_only_rr (e : EventType) (t : Time) (s : State α) (h : e ≠ .RR) :
    (SWPPV.stf ct rf e t s).ipnr = s.ipnr := by
  cases e <;> first | rfl | exact absurd rfl h

-- --- SWPPV par / leg symmetry (over ℝ) ------------------------------------

/-- **At par the legs cancel.**  When the fixed and floating rates coincide
    (`fixedRate = Ipnr`), the fixed leg is exactly the negation of the floating
    leg — so the two legs are sign-opposite. -/
theorem swppv_legs_opposite (ct : Terms ℝ) (rf : RiskFactorEnv ℝ) (t : Time) (s : State ℝ)
    (h : Terms.ipnr ct = s.ipnr) :
    SWPPV.pof_IPFX ct rf t s = - SWPPV.pof_IPFL rf t s := by
  simp only [SWPPV.pof_IPFX, SWPPV.pof_IPFL, h]; ring

/-- **At par the net settlement is zero.**  Hence the `deliverySettlement = "S"`
    netted period flow vanishes when the swap is at par. -/
theorem swppv_par_net_zero (ct : Terms ℝ) (rf : RiskFactorEnv ℝ) (t : Time) (s : State ℝ)
    (h : Terms.ipnr ct = s.ipnr) :
    SWPPV.pof_IPFX ct rf t s + SWPPV.pof_IPFL rf t s = 0 := by
  rw [swppv_pof_net, h]; ring

-- --- UMP compound-growth closed form (over ℝ) -----------------------------

/-- A **capitalization trace**: zero or more `IPCI` steps (each admissible,
    `Sd ≤ t`).  Lives in `Type` so the multiplicative growth factor below can be
    extracted from it. -/
inductive IPCITrace (rf : RiskFactorEnv ℝ) : State ℝ → State ℝ → Type
  | refl {s : State ℝ} : IPCITrace rf s s
  | step {s : State ℝ} {t : Time} {s' : State ℝ} (ht : s.sd ≤ t)
      (rest : IPCITrace rf (UMP.stf_IPCI rf t s) s') : IPCITrace rf s s'

/-- The compound growth factor `∏ᵢ (1 + rateᵢ·Yᵢ)` accumulated along a
    capitalization trace (`rateᵢ`/`Yᵢ` read from the running state at step `i`). -/
noncomputable def ipciFactor (rf : RiskFactorEnv ℝ) :
    ∀ {s s' : State ℝ}, IPCITrace rf s s' → ℝ
  | _, _, .refl              => 1
  | s, _, .step (t := t) _ rest => (1 + s.ipnr * rf.yf s.sd t) * ipciFactor rf rest

/-- **The nominal rate is constant under capitalization.**  `IPCI` never touches
    `Ipnr`, so it is the same throughout the trace — justifying the single
    `rate` in the closed form below. -/
theorem ipciTrace_ipnr (rf : RiskFactorEnv ℝ) {s s' : State ℝ} (tr : IPCITrace rf s s') :
    s'.ipnr = s.ipnr := by
  induction tr with
  | refl => rfl
  | @step s t s' ht rest ih => rw [ih]; rfl

/-- **UMP compound-growth closed form.**  After a capitalization trace the
    notional is the initial notional times the product of the per-period growth
    factors: `Nt' = Nt₀ · ∏ᵢ (1 + rate·Yᵢ)`.  Proved by induction on the trace —
    each `IPCI` multiplies the notional by its `(1 + rate·Y)` factor. -/
theorem ump_ipci_closed_form (rf : RiskFactorEnv ℝ) {s s' : State ℝ} (tr : IPCITrace rf s s') :
    s'.nt = s.nt * ipciFactor rf tr := by
  induction tr with
  | refl => simp [ipciFactor]
  | @step s t s' ht rest ih =>
      rw [ih]
      simp only [ipciFactor, UMP.stf_IPCI]
      ring

-- --- LAX amortization: monotone notional under DEC redemptions (over ℝ) ----

/-- A single LAX redemption with a non-negative instalment, on the long
    (`sign ≥ 0`) side, does not increase the notional.  Unlike LAM's capped
    `redeemed`, `STF_PR_LAX` subtracts the raw (signed) instalment, so this is a
    one-sided (monotone) bound rather than a `[0, Nt]` window. -/
theorem lax_pr_nt_le (ct : Terms ℝ) (rf : RiskFactorEnv ℝ) (x : ℝ) (t : Time) (s : State ℝ)
    (hx : 0 ≤ x) (hsign : (0 : ℝ) ≤ sign (Terms.cntrl ct)) :
    (LAX.stf_PR ct rf x t s).nt ≤ s.nt := by
  show s.nt - sign (Terms.cntrl ct) * x ≤ s.nt
  exact sub_le_self s.nt (mul_nonneg hsign hx)

/-- A **redemption (`PR`) trace** for LAX: zero or more `DEC` redemptions, each
    with a non-negative instalment `x` at an admissible time. -/
inductive LAXPRTrace (ct : Terms ℝ) (rf : RiskFactorEnv ℝ) : State ℝ → State ℝ → Prop
  | refl {s : State ℝ} : LAXPRTrace ct rf s s
  | step {s : State ℝ} {x : ℝ} {t : Time} {s' : State ℝ} (hx : 0 ≤ x) (ht : s.sd ≤ t)
      (rest : LAXPRTrace ct rf (LAX.stf_PR ct rf x t s) s') : LAXPRTrace ct rf s s'

/-- **Monotone amortization.**  Along a whole LAX redemption trace, the notional
    never increases: `Nt' ≤ Nt₀` (the long-side, non-negative-instalment case).
    Proved by induction from the single-step bound `lax_pr_nt_le`. -/
theorem laxPRTrace_nt_le {ct : Terms ℝ} {rf : RiskFactorEnv ℝ} {s s' : State ℝ}
    (h : LAXPRTrace ct rf s s') (hsign : (0 : ℝ) ≤ sign (Terms.cntrl ct)) : s'.nt ≤ s.nt := by
  induction h with
  | refl => exact le_rfl
  | @step s x t s' hx ht rest ih => exact le_trans ih (lax_pr_nt_le ct rf x t s hx hsign)

/-- A `LAXPRTrace` is a genuine `LAX` execution trace (each step is the `LAX.Step`
    for event `.PR` with payload `x`), so the bound above is about real
    executions, not a separate toy relation. -/
theorem laxPRTrace_isTrace {ct : Terms ℝ} {rf : RiskFactorEnv ℝ} {s s' : State ℝ}
    (h : LAXPRTrace ct rf s s') : Nonempty (LAX.Trace ct rf s s') := by
  induction h with
  | refl => exact ⟨.refl⟩
  | @step s x t s' hx ht rest ih =>
      obtain ⟨tr⟩ := ih
      exact ⟨.step (LAX.Step.ev .PR x ht) tr⟩

end Actus.Contract.Properties
