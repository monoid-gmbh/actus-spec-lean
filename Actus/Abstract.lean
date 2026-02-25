/-
## ACTUS Abstract

Defines the `ActusContract` record (bundling `Terms` and `State` types) and
the nested `StateTransition` record (initial state, one-step relation, and
cashflow extractor).

Translated from `Actus/Abstract.lagda.md` (Agda) to Lean 4.
-/

import Actus.Protocol
import Actus.Closures

namespace Actus.Abstract

open Actus.Protocol
open Actus.Closures

/-- An `ActusContract` bundles a `Terms` type with a `State` type. -/
structure ActusContract : Type 1 where
  Terms : Type
  State : Type

/-- The operational semantics of an `ActusContract`:
    an initial state, a one-step transition relation, and a cashflow extractor.

    `getCashflow` takes a proof that a single step took place and a
    `RiskFactor` instance, and returns the resulting `Cashflow`. -/
structure StateTransition (c : ActusContract) : Type 1 where
  /-- Initial state. -/
  s₀ : c.State
  /-- One-step state-transition relation. -/
  rel : c.State → c.State → Type
  /-- Extract the cashflow produced by a single transition. -/
  getCashflow : ∀ {s s' : c.State}, rel s s' → RiskFactor → Cashflow

/-!
The reflexive-transitive closure of `rel` is `Star rel`, defined in
`Actus.Closures`.  Consumers can write `Star st.rel s s'` for execution
traces, where `st : StateTransition c`.

The following helper is the analogue of the commented-out `getCashflows` in
the Agda source:
-/
/-
def getCashflows {c : ActusContract} (st : StateTransition c) (rf : RiskFactor) :
    ∀ {s s' : c.State}, Star st.rel s s' → List Cashflow
  | _, _, .refl        => []
  | _, _, .step h rest => st.getCashflow h rf :: getCashflows st rf rest
-/

end Actus.Abstract
