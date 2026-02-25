/-
## ACTUS Contract Execution

Parameterised by a concrete `ActusContract` and its `StateTransition`.
Schedule and cashflow generation are stubs (`sorry`), faithfully reflecting
the `{!!}` holes in the Agda source.

Translated from `Actus/Execution.lagda.md` (Agda) to Lean 4.
-/

import Actus.Protocol
import Actus.Abstract

namespace Actus.Execution

open Actus.Protocol
open Actus.Abstract

variable (c : ActusContract) (st : StateTransition c)

/-- Generate the event schedule from contract terms.
    Implementation is intentionally left as a `sorry` (stub). -/
def genSchedule (_ : c.Terms) : Schedule := by exact sorry

/-- Generate the cashflow stream from contract terms.
    Implementation is intentionally left as a `sorry` (stub). -/
def genCashflows (_ : c.Terms) : Cashflows := by exact sorry

end Actus.Execution
