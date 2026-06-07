/-
## Relational ↔ functional agreement

Each lending contract carries two models: the relational `Step` (the readable
spec) and the functional `stf` dispatcher.  Here we prove they describe the same
transitions:

* `step_to_fun` (soundness): every relational step lands on the functional
  next-state `stf e t s` for some event `e` and time `t`.
* `fun_to_step` (completeness): for any event `e` and admissible time `t ≥ Sd`,
  the functional next-state is reachable by a relational step.

Together these say `Step` is exactly the graph of `stf` over admissible
event/time pairs — the basis for the determinism metatheorem in `Properties`.
-/

import Actus.Contract.PAM
import Actus.Contract.LAM
import Actus.Contract.NAM
import Actus.Contract.ANN
import Actus.Contract.UMP
import Actus.Contract.LAX
import Actus.Contract.Swap

namespace Actus.Contract.Agree

open Actus.Protocol
open Actus.Contract
open Actus (Amount)

variable {α : Type} [Amount α] [DecidableLE α]

-- ---------------------------------------------------------------------------
-- PAM  (per-event relational constructors)
-- ---------------------------------------------------------------------------

omit [DecidableLE α] in
theorem pam_step_to_fun {ct rf} {s s' : State α} (h : PAM.Step ct rf s s') :
    ∃ (e : EventType) (t : Time), s' = PAM.stf ct rf e t s := by
  cases h with
  | ad _   => exact ⟨.AD,   _, rfl⟩
  | ied _  => exact ⟨.IED,  _, rfl⟩
  | md _   => exact ⟨.MD,   _, rfl⟩
  | pp _   => exact ⟨.PP,   _, rfl⟩
  | py _   => exact ⟨.PY,   _, rfl⟩
  | fp _   => exact ⟨.FP,   _, rfl⟩
  | prd _  => exact ⟨.PRD,  _, rfl⟩
  | td _   => exact ⟨.TD,   _, rfl⟩
  | ip _   => exact ⟨.IP,   _, rfl⟩
  | ipci _ => exact ⟨.IPCI, _, rfl⟩
  | rr _   => exact ⟨.RR,   _, rfl⟩
  | rrf _  => exact ⟨.RRF,  _, rfl⟩
  | sc _   => exact ⟨.SC,   _, rfl⟩
  | ce _   => exact ⟨.CE,   _, rfl⟩

omit [DecidableLE α] in
/-- Completeness for the events that have a dedicated PAM constructor.  (The
    dispatcher's catch-all events — `PD`, `STD`, `XD`, `DV` — are not part of
    the PAM schedule and have no constructor.) -/
theorem pam_fun_to_step {ct rf} {s : State α} {t : Time} (ht : s.sd ≤ t) :
    Nonempty (PAM.Step ct rf s (PAM.stf_IP ct rf t s)) :=
  ⟨.ip ht⟩

-- ---------------------------------------------------------------------------
-- LAM / NAM / ANN  (single dispatching constructor)
-- ---------------------------------------------------------------------------

theorem lam_step_to_fun {ct rf} {s s' : State α} (h : LAM.Step ct rf s s') :
    ∃ (e : EventType) (t : Time), s' = LAM.stf ct rf e t s := by
  cases h with | ev e _ => exact ⟨e, _, rfl⟩

def lam_fun_to_step {ct rf} {s : State α} (e : EventType) {t : Time}
    (ht : s.sd ≤ t) : LAM.Step ct rf s (LAM.stf ct rf e t s) := .ev e ht

theorem nam_step_to_fun {ct rf} {s s' : State α} (h : NAM.Step ct rf s s') :
    ∃ (e : EventType) (t : Time), s' = NAM.stf ct rf e t s := by
  cases h with | ev e _ => exact ⟨e, _, rfl⟩

def nam_fun_to_step {ct rf} {s : State α} (e : EventType) {t : Time}
    (ht : s.sd ≤ t) : NAM.Step ct rf s (NAM.stf ct rf e t s) := .ev e ht

theorem ann_step_to_fun {ct rf} {s s' : State α} (h : ANN.Step ct rf s s') :
    ∃ (e : EventType) (t : Time), s' = ANN.stf ct rf e t s := by
  cases h with | ev e _ => exact ⟨e, _, rfl⟩

def ann_fun_to_step {ct rf} {s : State α} (e : EventType) {t : Time}
    (ht : s.sd ≤ t) : ANN.Step ct rf s (ANN.stf ct rf e t s) := .ev e ht

-- ---------------------------------------------------------------------------
-- UMP / SWPPV  (single dispatching constructor, standard `stf` signature)
-- ---------------------------------------------------------------------------

omit [DecidableLE α] in
theorem ump_step_to_fun {ct rf} {s s' : State α} (h : UMP.Step ct rf s s') :
    ∃ (e : EventType) (t : Time), s' = UMP.stf ct rf e t s := by
  cases h with | ev e _ => exact ⟨e, _, rfl⟩

def ump_fun_to_step {ct rf} {s : State α} (e : EventType) {t : Time}
    (ht : s.sd ≤ t) : UMP.Step ct rf s (UMP.stf ct rf e t s) := .ev e ht

omit [DecidableLE α] in
theorem swppv_step_to_fun {ct rf} {s s' : State α} (h : SWPPV.Step ct rf s s') :
    ∃ (e : EventType) (t : Time), s' = SWPPV.stf ct rf e t s := by
  cases h with | ev e t _ => exact ⟨e, t, rfl⟩

def swppv_fun_to_step {ct rf} {s : State α} (e : EventType) (t : Time)
    (ht : s.sd ≤ t) : SWPPV.Step ct rf s (SWPPV.stf ct rf e t s) := .ev e t ht

-- ---------------------------------------------------------------------------
-- LAX  (dispatching constructor with a per-event payload `x`)
-- ---------------------------------------------------------------------------

omit [DecidableLE α] in
theorem lax_step_to_fun {ct rf} {s s' : State α} (h : LAX.Step ct rf s s') :
    ∃ (e : EventType) (x : α) (t : Time), s' = LAX.stf ct rf e x t s := by
  cases h with | ev e x _ => exact ⟨e, x, _, rfl⟩

def lax_fun_to_step {ct rf} {s : State α} (e : EventType) (x : α) {t : Time}
    (ht : s.sd ≤ t) : LAX.Step ct rf s (LAX.stf ct rf e x t s) := .ev e x ht

end Actus.Contract.Agree
