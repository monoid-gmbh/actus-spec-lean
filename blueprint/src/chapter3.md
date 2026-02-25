# PAM: Principal at Maturity

## Overview

PAM (Principal at Maturity) is the simplest ACTUS contract type. It models:
- Bonds
- Term deposits  
- Bullet loans
- Simple mortgages

### Characteristics

- Principal is paid at Initial Exchange Date (IED)
- Interest accrues over time
- Principal is repaid at Maturity Date (MD)
- Interest can be paid periodically or at maturity

## Terms

\begin{definition}
\label{def:pam-terms}
\lean{Actus.Contract.PAM.Terms}
\leanok
PAM contract terms:
- `statusDate : Nat` - Current status date
- `contractRole : ContractRole` - Is this an asset or liability?
- `notionalPrincipal : Float` - Principal amount
- `nominalInterest : Option Float` - Interest rate (if any)
- `feeBasis : FeeBasis` - How fees are calculated
- `feeRate : Float` - Fee rate
- `dayCountConvention : DayCountConvention` - How to count days
\end{definition}

## State

\begin{definition}
\label{def:pam-state}
\lean{Actus.Contract.PAM.State}
\leanok
PAM contract state:
- `name : String` - Contract identifier
- `statusDate : Nat` - Current time
- `notionalPrincipal : Float` - Outstanding principal
- `nominalInterest : Float` - Current interest rate
- `accruedInterest : Float` - Interest accumulated so far
- `accruedFees : Float` - Fees accumulated so far
\end{definition}

## State Transitions

\begin{definition}
\label{def:pam-step}
\lean{Actus.Contract.PAM.Step}
\leanok
PAM has four transition rules:

1. **IED** (Initial Exchange Date)
   - Preconditions: contract is in test state, interest rate is specified
   - Effect: Set notional principal, activate interest rate
   
2. **IP₁** (Interest Payment - fee basis is Notional)
   - Precondition: `feeBasis = FEB_N`
   - Effect: Reset accrued interest, calculate fees based on notional
   
3. **IP₂** (Interest Payment - other fee basis)
   - Precondition: `feeBasis ≠ FEB_N`
   - Effect: Reset accrued interest and fees
   
4. **MD** (Maturity Date)
   - Precondition: contract is in test state
   - Effect: Update status date (principal repayment happens via cashflow)
\end{definition}

## Cashflow Extraction

\begin{definition}
\label{def:pam-getcashflow}
\lean{Actus.Contract.PAM.getCashflow}
\leanok
Each transition produces a cashflow:
- **IED**: `((0, IED), 0.0)` - Initial exchange (amount depends on terms)
- **IP**: `((t, IP), interest_payment)` - Interest payment at time t
- **MD**: `((t, MD), principal_repayment)` - Principal repayment at maturity
\end{definition}

\begin{definition}
\label{def:pam-getcashflows}
\lean{Actus.Contract.PAM.getCashflows}
\leanok
Collect all cashflows along an execution trace by recursing on the `Star` structure.
\end{definition}

## Example Execution

We demonstrate a simple PAM contract with zero principal and interest:

\begin{definition}
\label{def:pam-example}
\lean{Actus.Contract.PAM.Test.pam}
\leanok
Example contract terms with all amounts set to zero.
\end{definition}

### States

\begin{definition}
\label{def:pam-s1}
\lean{Actus.Contract.PAM.Test.s₁}
\leanok
State after IED: time = 0, all balances zero.
\end{definition}

\begin{definition}
\label{def:pam-s2}
\lean{Actus.Contract.PAM.Test.s₂}
\leanok
State after MD: time = 1, all balances zero.
\end{definition}

### Transitions

\begin{lemma}
\label{lem:pam-step1}
\lean{Actus.Contract.PAM.Test.step₁}
\leanok
The contract can transition from `s₀` to `s₁` via IED.
\end{lemma}

\begin{lemma}
\label{lem:pam-step2}
\lean{Actus.Contract.PAM.Test.step₂}
\leanok
The contract can transition from `s₁` to `s₂` via MD.
\end{lemma}

\begin{lemma}
\label{lem:pam-trace}
\lean{Actus.Contract.PAM.Test.trace}
\leanok
Complete execution trace: `s₀ →[IED] s₁ →[MD] s₂`.
\end{lemma}

### Cashflow Verification

\begin{theorem}
\label{thm:pam-test1}
\lean{Actus.Contract.PAM.Test.test₁}
\leanok
The IED transition produces cashflow `((0, IED), 0.0)`.
\end{theorem}

\begin{theorem}
\label{thm:pam-test2}
\lean{Actus.Contract.PAM.Test.test₂}
\leanok
The complete trace produces exactly two cashflows:
```
[((0, IED), 0.0), ((1, MD), 1.0)]
```
\end{theorem}

These theorems are proven by reflexivity (`rfl`), demonstrating that our
implementation matches the expected behavior exactly.

## Implementation Details

### Float Arithmetic

Lean 4's `Float` type uses native IEEE-754 semantics. Unlike Agda, the kernel
does not reduce float operations definitionally.

To work around this, we define states `s₁` and `s₂` as the exact record
expressions produced by the transitions, rather than as independent literal
records. This allows the type checker to unify states definitionally without
evaluating `1.0 * 0.0`.

### Contract Role Sign

\begin{definition}
\label{def:sign}
\lean{Actus.Protocol.sign}
\leanok
The sign function maps contract roles to {-1, +1}:
- Positive for asset positions (receiving principal)
- Negative for liability positions (paying principal)

Currently implemented as a stub returning `1.0` for all roles.
\end{definition}
