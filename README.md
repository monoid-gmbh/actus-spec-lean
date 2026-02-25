# ACTUS Formal Specification — Lean 4

A translation of the [ACTUS relational specification](https://github.com/input-output-hk/actus-spec-agda)
from **Agda** to **Lean 4**.  No Mathlib dependency; the project uses only
Lean's standard library.

## Quick Start

### Option 1: Using Nix (Recommended)

The project includes a complete Nix environment with all dependencies.

#### With Nix Flakes (modern Nix)

```bash
# Enter development shell (auto-installs all dependencies)
nix develop

# Build the project
lake build

# Build blueprint documentation
python scripts/blueprint.py build

# Serve blueprint locally
python scripts/blueprint.py serve
```

#### Without Nix Flakes (traditional Nix)

```bash
# Enter development shell
nix-shell

# Then use lake and python as above
lake build
python scripts/blueprint.py build
```

#### Build with Nix

```bash
# Build the Lean project
nix build

# Build the blueprint documentation
nix build .#blueprint

# Run the blueprint server
nix run  # Serves at http://localhost:8000
```

### Option 2: Manual Installation

If you prefer not to use Nix:

#### Building the Lean code

```bash
lake build
```

Requires the toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.14.0`).
If you have [`elan`](https://github.com/leanprover/elan) installed it will be
downloaded automatically.

### Building the blueprint documentation

The project includes a blueprint that generates beautiful mathematical documentation:

```bash
# Install leanblueprint (if not already installed)
pip install leanblueprint

# Build the blueprint
python scripts/blueprint.py build

# Serve locally to preview
python scripts/blueprint.py serve
# Then open http://localhost:8000 in your browser

# Clean generated files
python scripts/blueprint.py clean
```

The blueprint provides:
- Mathematical definitions with LaTeX rendering
- Dependency graphs showing relationships between definitions
- Links to the Lean source code
- Progress tracking (which definitions are formalized vs. planned)

## Project structure

```
lean-toolchain                  ← Lean version pin
lakefile.lean                   ← Lake build descriptor
FormalSpec.lean                 ← top-level re-export
Actus/
  Protocol.lean                 ← all ACTUS domain types and enumerations
  Closures.lean                 ← reflexive-transitive closure (Star)
  Abstract.lean                 ← abstract ActusContract / StateTransition
  Execution.lean                ← schedule / cashflow generation (stubs)
  Contract/
    PAM.lean                    ← Principal-at-Maturity contract
    PAM/
      Test.lean                 ← example execution trace + cashflow tests
```

## Module correspondence

| Agda source | Lean 4 source |
|---|---|
| `Actus.Protocol` | `Actus/Protocol.lean` |
| `Prelude.Closures _↝_` | `Actus/Closures.lean` |
| `Actus.Abstract` | `Actus/Abstract.lean` |
| `Actus.Execution` | `Actus/Execution.lean` |
| `Actus.Contract.PAM` | `Actus/Contract/PAM.lean` |
| `Actus.Contract.PAM.Test` | `Actus/Contract/PAM/Test.lean` |

## Translation notes

### Syntax mapping

| Agda | Lean 4 |
|---|---|
| `data T` | `inductive T` |
| `record T` | `structure T` |
| `Maybe` | `Option` |
| `just x` / `nothing` | `some x` / `none` |
| `ℕ` | `Nat` |
| `Type₁` | `Type 1` |
| `record s { f = v }` | `{ s with f := v }` |
| `⦃ RiskFactor ⦄` (unnamed instance) | explicit `rf : RiskFactor` parameter |
| `∙ p ─── conc` (inference rule notation) | inductive constructor with `∀` implicit args |
| `open import Prelude.Closures _↝_ public` | `Actus.Closures` (custom implementation) |

### `private variable` → constructor parameters

In the Agda source, `s : State`, `t : Time`, and `ipnr : Float` are declared
as `private variable`s that are implicitly generalised over each constructor.
In Lean 4 these become explicit implicit arguments `{s} {t} {ipnr}` on each
constructor of `Step`.

### Module parameters → explicit function parameters

The Agda `module Spec (contractTerms : Terms)` is replaced by passing `ct :
Terms` as an explicit argument to every definition (`Step ct`, `getCashflow
ct`, etc.).

### Closures

`Prelude.Closures` from the Agda standard library is re-implemented as
`Actus.Closures.Star` — a standard reflexive-transitive closure inductive with
`refl` and `step` constructors.

### Float arithmetic and proof obligations

Lean 4's `Float` type uses native IEEE-754 semantics; the kernel does **not**
reduce expressions like `1.0 * 0.0` definitionally.  The Agda source uses
`refl` for all proofs because Agda's kernel does reduce `primFloatTimes`.

In this translation:

* `test₁` and `test₂` remain `rfl` — the cashflow extractor returns literal
  pairs with no float arithmetic in the result type.
* `step₁` (IED): the result type contains `sign CR_RPA * 0.0`.  Since `sign`
  pattern-matches to `1.0`, this becomes `1.0 * 0.0`.  This is discharged via
  `native_decide` (native code evaluation) or `sorry` if `native_decide` is
  not available.
* `step₂` (MD): purely structural, stays `rfl`.

### Stubs

`genSchedule` and `genCashflows` in `Actus/Execution.lean` are `sorry` stubs,
faithfully reflecting the `{!!}` holes in the Agda source.
