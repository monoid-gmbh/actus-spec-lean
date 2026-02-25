# Introduction

## What is ACTUS?

ACTUS (Algorithmic Contract Types Unified Standards) is a standard for representing financial contracts algorithmically. It provides a comprehensive taxonomy of financial contracts and their behavioral patterns.

## Why Formal Verification?

Financial contracts involve:
- Complex calculations with potential for errors
- Legal and regulatory requirements
- Large sums of money where bugs are costly
- Need for transparency and auditability

Formal verification using proof assistants like Lean provides:
- **Mathematical certainty** that implementations match specifications
- **Executable specifications** that can be directly tested
- **Documentation** that cannot drift from the code
- **Type safety** preventing entire classes of errors

## Translation from Agda to Lean 4

This project is a translation of the ACTUS specification from Agda to Lean 4. The translation preserves:

- All type definitions and their structure
- The state-transition semantics
- The cashflow generation logic
- Example contract executions and their proofs

Key differences:
- Lean 4's native Float type vs. Agda's builtin floats
- Explicit instance arguments vs. Agda's unnamed instances
- Different module system (namespaces vs. parameterized modules)

## Architecture

The formalization is layered:

```
┌─────────────────────────────────────┐
│   Contract Implementations          │
│   (PAM, LAM, ANN, ...)              │
├─────────────────────────────────────┤
│   Execution Layer                   │
│   (Schedule/Cashflow Generation)    │
├─────────────────────────────────────┤
│   Abstract Contract Interface       │
│   (ActusContract, StateTransition)  │
├─────────────────────────────────────┤
│   Protocol & Domain Types           │
│   (Events, Roles, Conventions)      │
├─────────────────────────────────────┤
│   Core Infrastructure               │
│   (Star closure, basic types)       │
└─────────────────────────────────────┘
```

Each layer builds on the ones below it, ensuring a clean separation of concerns.
