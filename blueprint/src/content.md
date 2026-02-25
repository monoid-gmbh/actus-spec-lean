# ACTUS Formal Specification

\tableofcontents

\input{chapter1}

\input{chapter2}

\input{chapter3}

# Protocol Types Reference

## Contract Types

\begin{definition}
\label{def:contract-type}
\lean{Actus.Protocol.ContractType}
\leanok
ACTUS defines 14 contract types:
- **PAM** - Principal at Maturity (bonds, term deposits)
- **LAM** - Linear Amortizer (mortgages with linear repayment)
- **NAM** - Negative Amortizer (mortgages with growing principal)
- **ANN** - Annuity (equal periodic payments)
- **STK** - Stock (equity instruments)
- **OPTNS** - Option (call/put options)
- **FUTUR** - Future (futures contracts)
- **COM** - Commodity (physical commodities)
- **CSH** - Cash (cash positions)
- **CLM** - Call Money (callable deposits)
- **SWPPV** - Plain Vanilla Swap
- **SWAPS** - Interest Rate Swap
- **CEG** - Guarantee (credit guarantees)
- **CEC** - Collateral (collateral agreements)
\end{definition}

## Contract Roles

\begin{definition}
\label{def:contract-role}
\lean{Actus.Protocol.ContractRole}
\leanok
Contract roles specify the perspective:
- **CR_RPA** - Real Position Asset
- **CR_RPL** - Real Position Liability  
- **CR_LG** - Long Position
- **CR_ST** - Short Position
- **CR_BUY** - Protection Buyer
- **CR_SEL** - Protection Seller
- And others for swaps, collateral, etc.
\end{definition}

## Day Count Conventions

\begin{definition}
\label{def:day-count-convention}
\lean{Actus.Protocol.DayCountConvention}
\leanok
Methods for calculating time fractions:
- **DCC_A_AISDA** - Actual/Actual ISDA
- **DCC_A_360** - Actual/360 (US convention)
- **DCC_A_365** - Actual/365 (UK convention)
- **DCC_E30_360** - 30E/360 (Eurobond)
- **DCC_B_252** - Business days / 252
\end{definition}

\begin{definition}
\label{def:year-fraction}
\lean{Actus.Protocol.yearFraction}
\uses{def:day-count-convention}
Calculate the year fraction between two dates according to a day count convention.
Currently implemented as a stub returning `0.0`.
\end{definition}

## Fee and Interest Bases

\begin{definition}
\label{def:fee-basis}
\lean{Actus.Protocol.FeeBasis}
\leanok
How fees are calculated:
- **FEB_A** - Absolute value
- **FEB_N** - Based on notional principal
\end{definition}

\begin{definition}
\label{def:interest-calculation-base}
\lean{Actus.Protocol.InterestCalculationBase}
\leanok
Base for interest calculations:
- **IPCB_NT** - Notional principal
- **IPCB_NTIED** - Notional plus interest at IED
- **IPCB_NTL** - Notional minus life cap
\end{definition}

# Future Work

## Additional Contract Types

The following ACTUS contract types are defined in the protocol but not yet implemented:

- **LAM** (Linear Amortizer) - Mortgages with fixed periodic principal reduction
- **NAM** (Negative Amortizer) - Loans where principal can grow
- **ANN** (Annuity) - Equal periodic payments covering principal and interest
- **STK** (Stock) - Equity instruments with dividends
- **OPTNS** (Options) - Call and put options
- **SWAPS** - Interest rate and currency swaps
- And others...

Each would follow the same pattern as PAM:
1. Define `Terms` structure
2. Define `State` structure  
3. Define `Step` transition relation
4. Implement `getCashflow` extractor
5. Prove example executions and properties

## Schedule Generation

\begin{definition}
\label{def:gen-schedule}
\lean{Actus.Execution.genSchedule}
Generate the complete event schedule from contract terms.
Implementation is intentionally left as `sorry` (matching the Agda source).
\end{definition}

\begin{definition}
\label{def:gen-cashflows}
\lean{Actus.Execution.genCashflows}
Generate the complete cashflow stream from contract terms.
Implementation is intentionally left as `sorry` (matching the Agda source).
\end{definition}

These functions would implement the ACTUS algorithms for:
- Computing event dates based on cycles and business day conventions
- Generating the complete event schedule
- Calculating state transitions for all events
- Extracting all cashflows

## Formal Properties

Future work could include proving:

- **Conservation laws**: Total cashflows balance (what goes out must come in)
- **Monotonicity**: Time always increases in execution traces
- **Determinism**: Same contract and risk factors always produce same cashflows
- **Equivalences**: Different contract parameterizations that are financially equivalent
- **Risk bounds**: Upper and lower bounds on possible cashflows
- **Regulatory compliance**: Contracts satisfy regulatory requirements

## Integration with Real Systems

The formal specification could be:
- **Extracted to executable code** for production use
- **Used as a reference** for testing implementations in other languages
- **Integrated with smart contracts** on blockchain platforms
- **Used for regulatory reporting** with mathematical guarantees
