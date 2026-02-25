import Lean.Elab.Command
import Lean.Data.Json

/-!
# ACTUS Blueprint Dependencies

This file is processed by leanblueprint to extract declaration dependencies
and build the dependency graph.

The blueprint system will automatically:
- Extract all definitions, theorems, and lemmas
- Build a dependency graph
- Link to source code
- Track formalization progress
-/

-- Core infrastructure
#check Actus.Protocol.EventType
#check Actus.Protocol.ContractRole
#check Actus.Protocol.RiskFactor
#check Actus.Closures.Star
#check Actus.Abstract.ActusContract
#check Actus.Abstract.StateTransition

-- PAM contract
#check Actus.Contract.PAM.Terms
#check Actus.Contract.PAM.State
#check Actus.Contract.PAM.Step
#check Actus.Contract.PAM.s₀
#check Actus.Contract.PAM.getCashflow
#check Actus.Contract.PAM.getCashflows
#check Actus.Contract.PAM.PAM_impl

-- PAM tests
#check Actus.Contract.PAM.Test.pam
#check Actus.Contract.PAM.Test.s₁
#check Actus.Contract.PAM.Test.s₂
#check Actus.Contract.PAM.Test.step₁
#check Actus.Contract.PAM.Test.step₂
#check Actus.Contract.PAM.Test.trace
#check Actus.Contract.PAM.Test.test₁
#check Actus.Contract.PAM.Test.test₂
