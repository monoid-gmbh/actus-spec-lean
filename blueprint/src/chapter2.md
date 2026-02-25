# Core Concepts

## Contracts as State Machines

In ACTUS, a financial contract is modeled as a state machine:

- **State**: The current status of the contract (balances, accruals, dates)
- **Events**: Trigger state transitions (payments, rate resets, maturity)
- **Transitions**: Rules for how events change the state
- **Cashflows**: Payments generated during transitions

\begin{definition}
\label{def:actus-contract}
\lean{Actus.Abstract.ActusContract}
\leanok
An ACTUS contract consists of:
- A type `Terms` of contract terms (fixed parameters)
- A type `State` of contract states (evolving data)
\end{definition}

## State Transitions

\begin{definition}
\label{def:state-transition}
\lean{Actus.Abstract.StateTransition}
\leanok
A state transition system for a contract `c` consists of:
- An initial state `s₀ : c.State`
- A transition relation `rel : c.State → c.State → Prop`
- A cashflow extractor `getCashflow : ∀ {s s'}, rel s s' → RiskFactor → Cashflow`
\end{definition}

The transition relation `rel s s'` is a proposition that holds when state `s` can transition to state `s'` in one step.

## Execution Traces

An execution trace is a sequence of states connected by transitions:

```
s₀ →[e₁] s₁ →[e₂] s₂ →[e₃] ... →[eₙ] sₙ
```

We formalize this using the reflexive-transitive closure:

\begin{definition}
\label{def:star-closure}
\lean{Actus.Closures.Star}
\leanok
`Star r a b` means `b` is reachable from `a` in zero or more steps of relation `r`.
\end{definition}

## Events and Cashflows

\begin{definition}
\label{def:event-type}
\lean{Actus.Protocol.EventType}
\leanok
ACTUS defines 23 event types covering:
- Lifecycle events (IED, MD, TD)
- Payment events (IP, PR, FP)
- Rate resets (RR, RRF)
- Scaling events (SC)
- Credit events (CE, CD)
\end{definition}

\begin{definition}
\label{def:event}
\lean{Actus.Protocol.Event}
\leanok
An event is a pair `(time, type)` where:
- `time : Nat` is when the event occurs
- `type : EventType` is what kind of event it is
\end{definition}

\begin{definition}
\label{def:cashflow}
\lean{Actus.Protocol.Cashflow}
\leanok
A cashflow is a pair `(event, amount)` where:
- `event : Event` is when and why the payment occurs
- `amount : Float` is how much is paid (negative = outflow, positive = inflow)
\end{definition}

## Risk Factors

Cashflow amounts depend on market conditions (risk factors):

\begin{definition}
\label{def:risk-factor}
\lean{Actus.Protocol.RiskFactor}
\leanok
Risk factors include:
- `CURS r` - Currency exchange rate `r`
- `XXXX r` - Placeholder for other market factors
\end{definition}

The same contract execution may produce different cashflows under different risk scenarios.
