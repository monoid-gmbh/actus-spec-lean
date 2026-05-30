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

and the two are **proven to agree**. The engine is validated against the ACTUS
Foundation's reference test suite: it matches **109 / 109** reference contracts
exactly (all 2593 cash flows). The project depends only on Lean's standard
library — **no Mathlib**.

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

`conformance` reads `actus-tests/actus-tests-{pam,lam,nam,ann}.json`, runs every
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
| Contracts | `Actus/Contract/PAM.lean`, `LAM.lean`, `NAM.lean`, `ANN.lean` | the lending family: per-event `stf`/`pof` functions and the relational `Step` |
| | `Actus/Contract/Lending/Common.lean` | shared `State`, terms accessors, and the `RiskFactorEnv` observer interface |
| Proofs | `Actus/Contract/Lending/Agree.lean` | relational ↔ functional agreement (`Step` is the graph of `stf`) |
| | `Actus/Contract/Lending/Properties.lean` | metatheorems: determinism, status-date monotonicity, maturity |
| Execution | `Actus/Execution.lean`, `Actus/Contract/Lending/Execution.lean` | the schedule-folding engine; `genSchedule` + per-contract cashflow generation |
| I/O | `Actus/IO/Parse.lean` | parser for the `actus-tests` JSON format (terms, risk factors, expected events) |
| | `Actus/IO/Conformance.lean` | the `conformance` executable |
| Tests | `Actus/Contract/*/Test.lean`, `Actus/IO/Test.lean` | worked examples with `rfl`-checked cashflow theorems and `#eval` demonstrations |

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

`Actus/Contract/Lending/Agree.lean` proves the two coincide — `Step` is exactly
the graph of `stf` over admissible event/time pairs — so the fast executable
engine and the clean relational spec cannot drift apart. Determinism then falls
out as a corollary, and `Properties.lean` proves further structural
metatheorems.

### A note on `Float`

Amounts use Lean's native `Float` (keeping the engine executable and
Mathlib-free). Since `Float` is not kernel-reducible, the in-Lean cashflow
theorems are stated in *formula form* (both sides unfold to the same
expression), and concrete numeric agreement is checked empirically by the
conformance harness rather than by `rfl`.

## Conformance

| Contract type | Exact contracts |
|---|---|
| PAM (principal at maturity) | 25 / 25 |
| LAM (linear amortizer) | 31 / 31 |
| NAM (negative amortizer) | 22 / 22 |
| ANN (annuity) | 31 / 31 |
| **Total** | **109 / 109** |

All 2593 reference cash flows match within a 1-cent tolerance. Run
`lake exe conformance` to reproduce.

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
