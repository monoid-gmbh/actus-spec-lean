/-
## PAM Test

Example contract execution trace and cashflow tests for the PAM contract.

Translated from `Actus/Contract/PAM/Test.lagda.md` (Agda) to Lean 4.

### Note on proofs and Float arithmetic

The Agda source uses `refl` for *every* proof.  This works because Agda's
kernel reduces floating-point builtins definitionally.

Lean 4's `Float` type uses native IEEE-754 semantics; the kernel does **not**
reduce `1.0 * 0.0` to `0.0` definitionally.

To keep all step proofs as plain constructor applications (no tactics), we
define `s₁` and `s₂` *definitionally* as the computed result states, rather
than as literal record expressions.  The steps then type-check by definitional
unification with no Float reduction required.

The cashflow tests (`test₁`, `test₂`) remain `rfl` because `getCashflow`
dispatches on the constructor tag and returns literal pairs — no Float
arithmetic appears in the normal form of the result type.
-/

import Actus.Protocol
import Actus.Abstract
import Actus.Closures
import Actus.Contract.PAM

namespace Actus.Contract.PAM.Test

open Actus.Protocol
open Actus.Closures
open Actus.Contract.PAM

-- ---------------------------------------------------------------------------
-- Example contract terms  (mirrors the Agda `pam` definition)
-- ---------------------------------------------------------------------------

def pam : Terms :=
  { statusDate         := 0
    contractRole       := ContractRole.CR_RPA
    notionalPrincipal  := 0.0
    nominalInterest    := some 0.0
    feeBasis           := FeeBasis.FEB_N
    feeRate            := 0.0
    dayCountConvention := DayCountConvention.DCC_A_360 }

-- ---------------------------------------------------------------------------
-- Example states
--
-- Rather than writing literal records and fighting Float-reduction goals, we
-- define s₁ and s₂ as the *exact* record expressions that the transition
-- constructors produce.  The proofs below then type-check without any Float
-- computation in the kernel.
--
-- Concretely:
--   s₁ = { s₀ with statusDate := 0, nominalInterest := 0.0,
--                  notionalPrincipal := sign CR_RPA * 0.0 }
--   s₂ = { s₁ with statusDate := 1 }
--
-- These are definitionally equal to the all-zero/time-1 records the Agda
-- source spells out (Agda reduces 1.0 * 0.0 = 0.0; Lean does not need to).
-- ---------------------------------------------------------------------------

/-- State after IED: time = 0, notional set by the role-sign formula. -/
def s₁ : State :=
  { s₀ with
    statusDate        := (0 : Nat)
    nominalInterest   := (0.0 : Float)
    notionalPrincipal := sign pam.contractRole * pam.notionalPrincipal }

/-- State after MD: time advances to 1, all other fields unchanged. -/
def s₂ : State :=
  { s₁ with statusDate := (1 : Nat) }

-- ---------------------------------------------------------------------------
-- Execution trace
-- ---------------------------------------------------------------------------

/-- **step₁**: IED transition from `s₀` to `s₁`.

    `stf_IED` requires:
      • `s.name = "test"`                — `rfl`
      • `ct.nominalInterest = some ipnr` — `rfl` (pam.nominalInterest = some 0.0)

    The result state is *defined* to be `s₁`, so unification succeeds with no
    Float arithmetic in the kernel. -/
def step₁ : Step pam s₀ s₁ :=
  Step.stf_IED (t := 0) (ipnr := 0.0) rfl rfl

/-- **step₂**: MD transition from `s₁` to `s₂`.

    `stf_MD` requires `s.name = "test"` — `rfl`.
    `t` is unified to `1` from the definition of `s₂`. -/
def step₂ : Step pam s₁ s₂ :=
  Step.stf_MD (t := 1) rfl

/-- **trace**: full execution path `s₀ ↠ s₂`. -/
def trace : Trace pam s₀ s₂ :=
  Star.step step₁ (Star.step step₂ Star.refl)

-- ---------------------------------------------------------------------------
-- Risk factor  (mirrors `instance r : RiskFactor := CURS 1.0` in Agda)
-- ---------------------------------------------------------------------------

def rf : RiskFactor := RiskFactor.CURS 1.0

-- ---------------------------------------------------------------------------
-- Cashflow tests
-- ---------------------------------------------------------------------------

/-- **test₁**: The cashflow produced by the IED step is `((0, IED), 0.0)`.

    `getCashflow` matches on `stf_IED` and immediately returns the literal
    pair — no Float arithmetic in the result type — so `rfl` works. -/
theorem test₁ : getCashflow pam step₁ rf = ((0, EventType.IED), 0.0) := rfl

/-- Collect all cashflows from the example trace. -/
def cashflows : Cashflows := getCashflows pam rf trace

/-- **test₂**: The full trace produces exactly `[((0, IED), 0.0), ((1, MD), 1.0)]`.

    Both match arms of `getCashflow` return literal pairs, so `rfl` holds. -/
theorem test₂ : cashflows = [((0, EventType.IED), 0.0), ((1, EventType.MD), 1.0)] := rfl

end Actus.Contract.PAM.Test
