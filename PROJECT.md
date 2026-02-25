# ACTUS Specification - Lean 4 Translation

## Project Summary

This is a complete translation of the ACTUS (Algorithmic Contract Types Unified Standards) formal specification from Agda to Lean 4, with added blueprint documentation.

### What's Included

**Lean 4 Formalization:**
- ✅ Complete protocol types (14 contract types, 23 event types, all conventions)
- ✅ Abstract contract interface (ActusContract, StateTransition)
- ✅ Star closure (reflexive-transitive closure) implementation
- ✅ PAM contract (Terms, State, Step transitions, cashflow extraction)
- ✅ PAM test suite (example execution with proofs)
- ✅ Execution stubs (genSchedule, genCashflows)

**Blueprint Documentation:**
- ✅ Mathematical documentation with LaTeX rendering
- ✅ Dependency graphs showing definition relationships
- ✅ Multi-chapter structure (Introduction, Core Concepts, PAM)
- ✅ Comprehensive reference for all protocol types
- ✅ Build scripts for easy documentation generation

**Nix Packaging:**
- ✅ Complete Nix flakes integration
- ✅ Development shell with all dependencies
- ✅ Reproducible builds
- ✅ Traditional Nix support (shell.nix, default.nix)
- ✅ Automatic leanblueprint installation
- ✅ CI/CD ready

### Directory Structure

```
actus-lean/
├── lean-toolchain              # Lean version (v4.14.0)
├── lakefile.lean               # Lake build configuration
├── README.md                   # Main documentation
├── PROJECT.md                  # This file
├── NIX.md                      # Nix documentation
├── .gitignore                  # Git ignore patterns
│
├── flake.nix                   # Nix flakes configuration
├── flake.lock                  # Locked Nix dependencies
├── shell.nix                   # Traditional Nix shell
├── default.nix                 # Traditional Nix build
│
├── Actus/                      # Main Lean sources
│   ├── Protocol.lean           # Domain types (492 lines)
│   ├── Closures.lean           # Star closure (35 lines)
│   ├── Abstract.lean           # Contract interface (50 lines)
│   ├── Execution.lean          # Schedule generation (29 lines)
│   └── Contract/
│       └── PAM.lean            # PAM implementation (190 lines)
│           └── Test.lean       # PAM tests (125 lines)
│
├── FormalSpec.lean             # Top-level re-export
│
├── blueprint/                  # Documentation
│   ├── web.toml                # Web config
│   ├── print.toml              # PDF config
│   ├── README.md               # Blueprint guide
│   └── src/
│       ├── content.md          # Main content
│       ├── chapter1.md         # Introduction
│       ├── chapter2.md         # Core concepts
│       ├── chapter3.md         # PAM contract
│       ├── macros.tex          # LaTeX macros
│       └── deps.lean           # Dependency tracking
│
└── scripts/
    └── blueprint.py            # Blueprint build script
```

## Quick Start

### With Nix (Recommended)

```bash
# Modern Nix (flakes)
nix develop          # Enter dev shell
lake build           # Build Lean code
python scripts/blueprint.py build  # Build docs

# Traditional Nix
nix-shell            # Enter dev shell
lake build           # Then same commands
```

### Without Nix

```bash
# Install Lean
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Install Python dependencies
pip install leanblueprint

# Build
lake build
python scripts/blueprint.py build
```

## Translation Notes

### Agda → Lean 4 Mappings

| Agda | Lean 4 |
|------|--------|
| `data T` | `inductive T` |
| `record T` | `structure T` |
| `Maybe` | `Option` |
| `ℕ` | `Nat` |
| `record s { f = v }` | `{ s with f := v }` |
| `⦃ T ⦄` (unnamed instance) | explicit parameter |
| `module M (x : T)` | `namespace M` with `variable (x : T)` |
| `private variable` | explicit implicit parameters |
| `Prelude.Closures` | custom `Actus.Closures` |

### Key Design Decisions

1. **Float arithmetic**: Lean 4's `Float` is native IEEE-754, not kernel-reducible. We define test states as exact record expressions from transitions to avoid Float reduction in proofs.

2. **Module parameters**: Agda's parameterized modules become namespaces with explicit parameters on each definition.

3. **Instance arguments**: Agda's unnamed instances become explicit parameters in function signatures.

4. **Closures**: Custom implementation of `Star` closure instead of Agda's stdlib.

## What Works

- ✅ All types compile
- ✅ PAM contract type-checks
- ✅ Example execution traces
- ✅ Cashflow extraction
- ✅ Test theorems prove by `rfl`
- ✅ No `sorry` in tests (only in stub implementations)
- ✅ Blueprint documentation builds

## Future Work

### Additional Contracts

- LAM (Linear Amortizer)
- NAM (Negative Amortizer)  
- ANN (Annuity)
- STK (Stock)
- OPTNS (Options)
- SWAPS (Swaps)
- And 8 more...

### Implementation

- Complete `genSchedule` algorithm
- Complete `genCashflows` algorithm
- Implement `yearFraction` for all day count conventions
- Implement `sign` function with actual role logic

### Verification

- Conservation laws (cashflows balance)
- Monotonicity properties
- Determinism proofs
- Contract equivalences
- Regulatory compliance proofs

## References

- **ACTUS Standard**: https://www.actusfrf.org/
- **Original Agda**: https://github.com/input-output-hk/actus-spec-agda
- **Lean 4**: https://leanprover.github.io/
- **Leanblueprint**: https://github.com/PatrickMassot/leanblueprint

## License

This translation maintains the same license as the original Agda source.

## Contributors

Translated from Agda to Lean 4 with blueprint documentation.
