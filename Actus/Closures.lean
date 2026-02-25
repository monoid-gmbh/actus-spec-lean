/-
## Reflexive-Transitive Closure

Provides the star (reflexive-transitive) closure of a binary relation and
the notation used in the ACTUS spec, replacing the Agda `Prelude.Closures`
import.

Notation (opened by each consumer):
  `s ↠ s'`           – `Star r s s'`
  `Star.step h rest` – prepend one step
  `Star.refl`        – empty path
-/

namespace Actus.Closures

/-- `Star r a b`: `b` is reachable from `a` in zero or more `r`-steps. -/
inductive Star {α : Type} (r : α → α → Type) : α → α → Type where
  | refl : {a : α} → Star r a a
  | step : {a b c : α} → r a b → Star r b c → Star r a c

-- namespace Star

/- Concatenate two paths (transitivity).
def trans {α : Type} {r : α → α → Prop} {a b c : α}
    (p : Star r a b) (q : Star r b c) : Star r a c :=
  match p with
  | .refl      => q
  | .step h tl => .step h (trans tl q)
termination_by p
-/

-- end Star

end Actus.Closures
