/-
## PAM Test

A worked PAM example: a relational execution trace, `rfl`-checked cashflow
theorems, and an end-to-end run of the executable `genSchedule`/`genCashflows`
pipeline.

### Note on `Float` and `rfl`

Lean's `Float` is native IEEE-754 and is *not* reduced by the kernel, so we do
not assert numeric literals.  Instead the cashflow theorems are stated in terms
of the *payoff-function expressions* (`PAM.pof_IED …`), so both sides unfold to
the same expression tree and `rfl` closes the goal with no Float arithmetic.
Concrete numbers are exercised with `#eval` instead (computation, not proof).
-/

import Actus.Protocol
import Actus.Closures
import Actus.Contract.Lending.Common
import Actus.Contract.Lending.Execution
import Actus.Contract.PAM

namespace Actus.Contract.PAM.Test

open Actus.Protocol
open Actus.Closures
open Actus.Contract.Lending
open Actus.Contract.PAM

-- ---------------------------------------------------------------------------
-- Example contract terms: a 1000-notional bullet loan at 10%.
-- ---------------------------------------------------------------------------

def pam : Terms Float :=
  { defaultTerms with
    contractRole         := .CR_RPA
    notionalPrincipal    := some 1000.0
    nominalInterestRate  := some 0.1
    premiumDiscountAtIED := some 0.0 }

def rf : RiskFactorEnv Float := .id

-- ---------------------------------------------------------------------------
-- Relational execution trace:  init → IED → MD
-- ---------------------------------------------------------------------------

/-- Initial state (maturity at time 10, status date 0). -/
def s0 : State Float := PAM.init pam 10 0
/-- After the Initial Exchange at time 1. -/
def s1 : State Float := PAM.stf_IED pam 1 s0
/-- After Maturity at time 2. -/
def s2 : State Float := PAM.stf_MD 2 s1

def step₁ : PAM.Step pam rf s0 s1 := .ied (by decide)
def step₂ : PAM.Step pam rf s1 s2 := .md (by decide)

/-- Full trace `s0 ↠ s2`. -/
def trace : PAM.Trace pam rf s0 s2 := .step step₁ (.step step₂ .refl)

-- ---------------------------------------------------------------------------
-- Cashflow theorems (structural, no Float arithmetic)
-- ---------------------------------------------------------------------------

/-- The IED cashflow carries the IED payoff at time 1. -/
theorem cf_ied : PAM.getCashflow pam rf step₁ = ((1, .IED), PAM.pof_IED pam rf 1) := rfl

/-- The MD cashflow carries the redemption payoff at time 2. -/
theorem cf_md : PAM.getCashflow pam rf step₂ = ((2, .MD), PAM.pof_MD rf 2 s1) := rfl

def cashflows : Cashflows := PAM.getCashflows pam rf trace

/-- The trace produces exactly the IED then MD cashflows. -/
theorem cashflows_eq :
    cashflows = [((1, .IED), PAM.pof_IED pam rf 1), ((2, .MD), PAM.pof_MD rf 2 s1)] := rfl

/-- Maturity zeroes the notional (definitional). -/
theorem md_zeroes_notional : s2.nt = 0 := rfl

-- ---------------------------------------------------------------------------
-- Executable pipeline: schedule generation + cashflow computation
-- ---------------------------------------------------------------------------

/-- A dated 1-year bullet loan paying interest semi-annually. -/
def pamDated : Terms Float :=
  { defaultTerms with
    contractRole                     := .CR_RPA
    notionalPrincipal                := some 1000.0
    nominalInterestRate              := some 0.1
    dayCountConvention               := some .DCC_A_360
    initialExchangeDate              := some { day := 1, month := 1, year := 2020 }
    maturityDate                     := some { day := 1, month := 1, year := 2021 }
    cycleOfInterestPayment           := some { n := 6, period := "M", stub := false } }

-- The generated event schedule (IED, two IP events, MD) and the cashflows.
#eval Lending.Execution.genSchedule pamDated false
#eval Lending.Execution.pamCashflows pamDated .id

end Actus.Contract.PAM.Test
