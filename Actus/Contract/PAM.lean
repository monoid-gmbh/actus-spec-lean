/-
## PAM — Principal at Maturity

#### Description
Principal payment fully at Initial Exchange Date `IED` and repaid at
Maturity Date `MD`. Fixed and variable rates.

#### Real-world Instrument Examples (but not limited to)
All kinds of bonds, term deposits, bullet loans and mortgages etc.

Translated from `Actus/Contract/PAM.lagda.md` (Agda) to Lean 4.

### Translation note on `private variable`
In the Agda source the state `s`, time `t`, and interest rate `ipnr` are
declared as `private variable`s that are implicitly generalised over each
constructor.  In Lean 4 we make them explicit implicit arguments `{s t ipnr}`
on every constructor of `Step`.
-/

import Actus.Protocol
import Actus.Abstract
import Actus.Closures

namespace Actus.Contract.PAM

open Actus.Protocol
open Actus.Abstract
open Actus.Closures

-- ---------------------------------------------------------------------------
-- Terms
-- ---------------------------------------------------------------------------

structure Terms where
  statusDate         : Nat
  contractRole       : ContractRole
  notionalPrincipal  : Float
  nominalInterest    : Option Float
  feeBasis           : FeeBasis
  feeRate            : Float
  dayCountConvention : DayCountConvention
  deriving Repr

-- ---------------------------------------------------------------------------
-- State
-- ---------------------------------------------------------------------------

structure State where
  name              : String
  statusDate        : Nat
  notionalPrincipal : Float
  nominalInterest   : Float
  accruedInterest   : Float
  accruedFees       : Float
  deriving Repr

-- ---------------------------------------------------------------------------
-- PAM as an ActusContract
-- ---------------------------------------------------------------------------

def PAM_contract : ActusContract :=
  { Terms := Terms, State := State }

-- ---------------------------------------------------------------------------
-- State-transition relation
--
-- `Step ct s s'` holds when contract `ct` can transition from state `s` to
-- state `s'` by one event.
--
-- The Agda source uses an anonymous `private variable t : Time` which gets
-- implicitly generalised into each constructor.  In Lean 4 we make it an
-- explicit implicit `{t : Time}` on each constructor that advances the clock.
-- ---------------------------------------------------------------------------

/-- One-step state-transition relation for PAM contracts. -/
inductive Step (ct : Terms) : State → State → Type where

  /-- **IED** — Initial Exchange Date.
      Requires `s.name = "test"` and `ct.nominalInterest = some ipnr`.
      Sets `statusDate := t`, `nominalInterest := ipnr`, and
      `notionalPrincipal := sign ct.contractRole * ct.notionalPrincipal`. -/
  | stf_IED :
      ∀ {s : State} {t : Time} {ipnr : Float},
      s.name = "test" →
      ct.nominalInterest = some ipnr →
      Step ct s
        { s with
          statusDate        := t
          nominalInterest   := ipnr
          notionalPrincipal := sign ct.contractRole * ct.notionalPrincipal }

  /-- **IP₁** — Interest Payment when `feeBasis = FEB_N`.
      Resets `accruedInterest` to 0 and computes `accruedFees`. -/
  | stf_IP1 :
      ∀ {s : State} {t : Time},
      ct.feeBasis = FeeBasis.FEB_N →
      Step ct s
        { s with
          statusDate      := t
          accruedInterest := 0.0
          -- timeFromLastEvent is hardcoded 0.0 in the Agda source
          accruedFees     := 0.0 * (ct.notionalPrincipal * ct.feeRate) }

  /-- **IP₂** — Interest Payment when `feeBasis ≠ FEB_N`.
      Resets accruals to 0 (full formula marked FIXME in the Agda source). -/
  | stf_IP2 :
      ∀ {s : State} {t : Time},
      ct.feeBasis ≠ FeeBasis.FEB_N →
      Step ct s
        { s with
          statusDate      := t
          accruedInterest := 0.0
          accruedFees     := 0.0 }  -- FIXME: actual formula omitted in source

  /-- **MD** — Maturity Date.
      Requires `s.name = "test"`.  Advances `statusDate` to `t`. -/
  | stf_MD :
      ∀ {s : State} {t : Time},
      s.name = "test" →
      Step ct s { s with statusDate := t }


-- TODO: ct implicit?
notation s "-[" ct "]↝" s' => Step ct s s'

-- ---------------------------------------------------------------------------
-- Closures
-- ---------------------------------------------------------------------------

/-- Execution trace: zero-or-more PAM steps from `s` to `s'`. -/
abbrev Trace (ct : Terms) := Star (Step ct)

-- ---------------------------------------------------------------------------
-- Initial state
-- ---------------------------------------------------------------------------

/-- Canonical initial state, matching the Agda `s₀`. -/
def s₀ : State :=
  { name              := "test"
    statusDate        := 0
    notionalPrincipal := 0.0
    nominalInterest   := 0.0
    accruedInterest   := 0.0
    accruedFees       := 0.0 }

-- ---------------------------------------------------------------------------
-- Cashflow extractor
-- ---------------------------------------------------------------------------

/-- Compute the cashflow produced by a single PAM transition step.

    Mirrors `getCashflow` in the Agda source, dispatching on both the
    constructor and the `RiskFactor` where needed.

    Note: `stf_IED` always returns `((0, IED), 0.0)` — this matches the Agda
    source, which hardcodes this for the zero-valued test contract. -/
def getCashflow (ct : Terms) {s s' : State} (h : Step ct s s') (rf : RiskFactor) : Cashflow :=
  match h with
  | .stf_IED _ _  => ((0, EventType.IED), 0.0)
  | @Step.stf_IP1 _ s _ _ =>
    match rf with
    | .CURS r =>
      ((s.statusDate, EventType.IP),
       r * (s.accruedInterest + s.nominalInterest * s.notionalPrincipal))
    | .XXXX _ => ((1, EventType.IP), 1.0)
  | .stf_IP2 _  => ((1, EventType.IP), 1.0)
  | .stf_MD _   => ((1, EventType.MD), 1.0)

-- ---------------------------------------------------------------------------
-- Cashflow collection over a full trace
-- ---------------------------------------------------------------------------

/-- Collect cashflows along a full execution trace. -/
def getCashflows (ct : Terms) (rf : RiskFactor) :
    ∀ {s s' : State}, Trace ct s s' → Cashflows
  | _, _, .refl        => []
  | _, _, .step h rest => getCashflow ct h rf :: getCashflows ct rf rest

-- ---------------------------------------------------------------------------
-- PAM implements StateTransition
-- ---------------------------------------------------------------------------

/-- Witness that the PAM spec satisfies `StateTransition`. -/
def PAM_impl (ct : Terms) : StateTransition PAM_contract :=
  { s₀          := s₀
    rel          := Step ct
    getCashflow  := fun h rf => getCashflow ct h rf }

end Actus.Contract.PAM
