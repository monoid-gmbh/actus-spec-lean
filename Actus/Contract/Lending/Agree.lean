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

namespace Actus.Contract.Lending.Agree

open Actus.Protocol
open Actus.Contract.Lending

-- ---------------------------------------------------------------------------
-- PAM  (per-event relational constructors)
-- ---------------------------------------------------------------------------

theorem pam_step_to_fun {ct rf} {s s' : State} (h : PAM.Step ct rf s s') :
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

/-- Completeness for the events that have a dedicated PAM constructor.  (The
    dispatcher's catch-all events — `PD`, `STD`, `XD`, `DV` — are not part of
    the PAM schedule and have no constructor.) -/
theorem pam_fun_to_step {ct rf} {s : State} {t : Time} (ht : s.sd ≤ t) :
    Nonempty (PAM.Step ct rf s (PAM.stf_IP ct t s)) :=
  ⟨.ip ht⟩

-- ---------------------------------------------------------------------------
-- LAM / NAM / ANN  (single dispatching constructor)
-- ---------------------------------------------------------------------------

theorem lam_step_to_fun {ct rf} {s s' : State} (h : LAM.Step ct rf s s') :
    ∃ (e : EventType) (t : Time), s' = LAM.stf ct rf e t s := by
  cases h with | ev e _ => exact ⟨e, _, rfl⟩

def lam_fun_to_step {ct rf} {s : State} (e : EventType) {t : Time}
    (ht : s.sd ≤ t) : LAM.Step ct rf s (LAM.stf ct rf e t s) := .ev e ht

theorem nam_step_to_fun {ct rf} {s s' : State} (h : NAM.Step ct rf s s') :
    ∃ (e : EventType) (t : Time), s' = NAM.stf ct rf e t s := by
  cases h with | ev e _ => exact ⟨e, _, rfl⟩

def nam_fun_to_step {ct rf} {s : State} (e : EventType) {t : Time}
    (ht : s.sd ≤ t) : NAM.Step ct rf s (NAM.stf ct rf e t s) := .ev e ht

theorem ann_step_to_fun {ct rf} {s s' : State} (h : ANN.Step ct rf s s') :
    ∃ (e : EventType) (t : Time), s' = ANN.stf ct rf e t s := by
  cases h with | ev e _ => exact ⟨e, _, rfl⟩

def ann_fun_to_step {ct rf} {s : State} (e : EventType) {t : Time}
    (ht : s.sd ≤ t) : ANN.Step ct rf s (ANN.stf ct rf e t s) := .ev e ht

end Actus.Contract.Lending.Agree
