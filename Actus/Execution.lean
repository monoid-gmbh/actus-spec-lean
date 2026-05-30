/-
## ACTUS Contract Execution (generic engine)

The executable side of the spec: given a *functional* state-transition function
and payoff function (the `stf`/`pof` dispatchers each contract provides) and an
event `Schedule`, `runSchedule` threads the state through the events in order
and collects the resulting `Cashflows`.

This replaces the previous `sorry` stubs.  Contract-specific *schedule
generation* (which events fire, and when) lives next to each contract family;
for the lending family see `Actus.Contract.Lending.Execution`.
-/

import Actus.Protocol
import Actus.Abstract

namespace Actus.Execution

open Actus.Protocol

/-- Fold a functional STF/POF over an event schedule.

    For each scheduled event `(t, e)` the payoff is computed from the *current*
    (pre-event) state, then the state is advanced by the STF. -/
def runSchedule {State : Type}
    (stf : EventType → Time → State → State)
    (pof : EventType → Time → State → Payoff)
    (s₀ : State) (sched : Schedule) : Cashflows :=
  let rec go (s : State) : Schedule → Cashflows
    | []            => []
    | (t, e) :: rest => ((t, e), pof e t s) :: go (stf e t s) rest
  go s₀ sched

/-- Final state after running the whole schedule from `s₀`. -/
def finalState {State : Type}
    (stf : EventType → Time → State → State)
    (s₀ : State) (sched : Schedule) : State :=
  sched.foldl (fun s (te : Event) => stf te.2 te.1 s) s₀

end Actus.Execution
