# ACTUS Formal Specification — Lean 4

A Lean 4 formalization of the [ACTUS](https://www.actusfrf.org/) standard
(Algorithmic Contract Types Unified Standards), which represents financial
contracts as deterministic, cashflow-generating state machines.

This project formalizes the **core lending family** — PAM, LAM, NAM and ANN —
following the ACTUS technical specification. Each contract is given **two
models**:

* a **relational** model (`Step`, an inductive transition relation) — the
  readable specification; and
* a **functional** model (computable state-transition and payoff functions) —
  the executable engine,

and the two are **proven to agree**. Several further contract types are also
implemented on the same engine — **COM** (commodity), **STK** (stock), **OPTNS**
(European options), **FUTUR** (futures), **FXOUT** (FX outright), **CSH** (cash)
and **SWPPV** (plain-vanilla swap), plus partial **CLM** (call money), **SWAPS**
(swaps) and **UMP** (non-maturity deposit). The engine is validated against the
ACTUS Foundation's reference test suite: it matches **236 / 236** reference
contracts exactly across the fully-supported types (all 3155 cash flows).

The spec is **generic over the amount type**: it runs on native `Float` for the
executable engine, and on the real numbers `ℝ` (via Mathlib) for the metatheorems
that need an ordered field — e.g. the rate stays within its cap/floor and a
redemption never overshoots zero.

## Quick start

### Build

```bash
lake build
```

The Lean toolchain is pinned in `lean-toolchain`; with
[`elan`](https://github.com/leanprover/elan) installed it is fetched
automatically. The build type-checks the whole development, including the
agreement proofs and metatheorems, and runs the per-contract example tests.

### Run the conformance harness

```bash
scripts/fetch-actus-tests.sh   # download the reference test data into actus-tests/
lake exe conformance           # diff computed vs expected cashflows
```

`conformance` reads the gated `actus-tests/actus-tests-*.json` files, runs every
contract through the engine under its own observed risk factors, and reports how
many contracts and individual cash flows match. It exits `0` only when every
contract matches, so it composes in CI:

```bash
scripts/fetch-actus-tests.sh && lake build && lake exe conformance
```

The reference data is not committed; `scripts/fetch-actus-tests.sh` fetches it
from [`actusfrf/actus-tests`](https://github.com/actusfrf/actus-tests).

### Nix (optional)

A Nix dev shell with all dependencies is provided:

```bash
nix develop      # flakes
# or
nix-shell        # traditional
```

then use `lake` as above.

## What's inside

| Layer | Modules | Contents |
|---|---|---|
| Domain | `Actus/Protocol.lean` | contract & event types, conventions, the `ContractTerms` dictionary record, core aliases (`Time`, `Cashflow`, …) |
| | `Actus/Closures.lean`, `Actus/Abstract.lean` | reflexive-transitive closure `Star`; abstract `ActusContract` / `StateTransition` interface |
| Utilities | `Actus/Util/Date.lean` | proleptic-Gregorian day arithmetic (serial days, period shifts, EOM/leap helpers) |
| | `Actus/Util/DayCount.lean` | year-fraction conventions (A/360, A/365, 30E/360, A/A-ISDA, B/252) |
| | `Actus/Util/Conventions.lean` | contract-role sign, end-of-month and business-day conventions |
| | `Actus/Util/Schedule.lean` | the schedule function `S(s,c,T,B)`, stub correction, and the annuity amount `A` |
| Contracts (spec) | `Actus/Contract/PAM.lean`, `LAM.lean`, `NAM.lean`, `ANN.lean`, `CLM.lean` | the stateful lending family: per-event `stf`/`pof` functions and the relational `Step` |
| | `Actus/Contract/Common.lean` | shared `State`, terms accessors, and the `RiskFactorEnv` observer interface |
| Proofs | `Actus/Contract/Agree.lean` | relational ↔ functional agreement (`Step` is the graph of `stf`) |
| | `Actus/Contract/Properties.lean` | metatheorems: determinism, status-date monotonicity, maturity, payoff bounds |
| Execution | `Actus/Execution.lean`, `Actus/Contract/Engine.lean` | the type-agnostic core: `runSchedule`, `genSchedule`, and shared cash-flow helpers |
| | `Actus/Contract/Lending.lean` | executable wrappers for the stateful family (`pamCashflows` … `clmCashflows`) |
| | `Actus/Contract/{Position,Derivative,Swap,CreditEnh,LAX,UMP}.lean` | per-family cash-flow builders for the stateless types (positions, derivatives, swaps, credit enhancement, exotic amortizer, deposit) |
| | `Actus/Contract/Execution.lean` | façade re-exporting the engine and all builders |
| I/O | `Actus/IO/Parse.lean` | parser for the `actus-tests` JSON format (terms, risk factors, expected events) |
| | `Actus/IO/Conformance.lean` | the `conformance` executable |
| Tests | `Test/PAM.lean`, `LAM.lean`, `NAM.lean`, `ANN.lean`, `IO.lean` | worked examples with `rfl`-checked cashflow theorems and `#eval` demonstrations (a separate `Test` library target, kept out of the documented API) |

`Actus.lean` is the top-level module that imports everything.

## The two models

For each contract, the **functional** model is primitive: `stf` (state
transition) and `pof` (payoff) are computable functions, one branch per ACTUS
event type, taken directly from the specification's STF/POF tables. The
executable pipeline (`Actus.Execution.runSchedule`) folds these over a generated
event `Schedule` to produce `Cashflows`.

The **relational** model, `Step`, is an inductive relation layered on top: each
constructor's target is literally the functional next-state, with side
conditions (e.g. events do not move backwards in time) attached. `Trace` is its
reflexive-transitive closure (`Star Step`).

`Actus/Contract/Agree.lean` proves the two coincide — `Step` is exactly
the graph of `stf` over admissible event/time pairs — so the fast executable
engine and the clean relational spec cannot drift apart. Determinism then falls
out as a corollary, and `Properties.lean` proves further structural
metatheorems.

### A note on `Float` and `ℝ`

The contract logic is written once, generically over an amount type `α`, and
instantiated twice. The **executable** engine uses Lean's native `Float`: fast,
but not kernel-reducible and with no usable algebraic laws (a single `NaN`
falsifies even `a ≤ a`), so the `Float`-side cashflow theorems are stated in
*formula form* (both sides unfold to the same expression) and concrete numeric
agreement is checked empirically by the conformance harness rather than by
`rfl`. The **specification** and its quantitative metatheorems use the real
numbers `ℝ` (via Mathlib), an exact ordered field where bounds like the rate
cap/floor window and redemption non-overshoot are genuine theorems. `Float` is
deliberately *not* expected to satisfy those laws — that split is the point.

## Conformance

The `Float` engine is run against the ACTUS Foundation's reference test suite
under each contract's own observed risk factors, and every computed cash flow is
diffed against the expected one (1-cent tolerance):

| Contract type | Exact contracts | Cash flows matched |
|---|---|---|
| PAM (principal at maturity) | 25 / 25 | 301 / 301 |
| LAM (linear amortizer) | 31 / 31 | 711 / 711 |
| NAM (negative amortizer) | 22 / 22 | 578 / 578 |
| ANN (annuity) | 31 / 31 | 1003 / 1003 |
| COM (commodity) | 4 / 4 | 6 / 6 |
| STK (stock) | 10 / 10 | 75 / 75 |
| OPTNS (European option) | 23 / 23 | 36 / 36 |
| FUTUR (future) | 14 / 14 | 26 / 26 |
| FXOUT (FX outright) | 12 / 12 | 14 / 14 |
| CSH (cash) | 4 / 4 | — |
| SWPPV (plain-vanilla swap) | 14 / 14 | 119 / 119 |
| CAPFL (cap / floor) | 4 / 4 | 6 / 6 |
| LAX (exotic array amortizer) | 18 / 18 | 261 / 261 |
| CEC (collateral) | 15 / 15 | 9 / 9 |
| UMP (undefined maturity profile) | 9 / 9 | 10 / 10 |
| **Total (gated)** | **236 / 236** | **3155 / 3155** |

Every contract in the gated suite matches exactly. A few further types are
implemented but not yet fully conformant, so they are **not** in the gated suite:
**CEG** (13 / 14 — `guarantee14`'s reference value diverges from techspec §7.17,
which gives the value we compute), **SWAPS** (10 / 11 — one annuity-maturity-
derivation precision case) and **CLM** (14 / 15 — including the open-maturity
"call" cases via the exercise observer; `clm10` alone needs split-rate accrual
across a mid-period reset). Reproduce with:

```bash
scripts/fetch-actus-tests.sh    # download the reference data into actus-tests/
lake exe conformance            # exits 0 only if every contract matches
```

## Blueprint

A [leanblueprint](https://github.com/PatrickMassot/leanblueprint) document lives
in `blueprint/` and links the mathematical definitions to the Lean sources:

```bash
leanblueprint web        # HTML
leanblueprint pdf        # PDF
leanblueprint checkdecls # verify every \lean{} reference resolves
```

## References

* ACTUS standard — <https://www.actusfrf.org/>
* ACTUS dictionary & taxonomy — <https://github.com/actusfrf/actus-dictionary>
* Reference test cases — <https://github.com/actusfrf/actus-tests>
* Lean 4 — <https://leanprover.github.io/>
