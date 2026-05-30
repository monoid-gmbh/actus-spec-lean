/-
## Shared state, terms accessors, and risk-factor environment (lending family)

PAM, LAM, NAM and ANN share the same state-variable vocabulary and reuse each
other's state-transition functions ("Same as PAM", `STF_X_PAM()` in §7.2–7.5).
To make that reuse literal we use **one** `State` record and the dictionary
`ContractTerms Float` for all four contracts.

* `State` — the lending state variables (`Md, Nt, Ipnr, Ipac, Feac, Nsc, Isc,
  Prnxt, Ipcb, Prf, Sd`).
* term accessors (`nt`, `ipnr`, `fer`, …) resolve the `Option` dictionary fields
  to concrete values with ACTUS defaults, so the STF/POF formulas stay readable.
* `RiskFactorEnv` — the risk-factor observer interface `Oʳᶠ / Oᵉᵛ` (§5),
  restricted to the quantities the lending STF/POF formulas reference.
* `yf` — year fraction `Y(s, t)` between two `Time` points (serial day numbers),
  resolving the contract's day-count convention.
-/

import Actus.Protocol
import Actus.Util.Date
import Actus.Util.DayCount
import Actus.Util.Conventions

namespace Actus.Contract.Lending

open Actus.Protocol
open Actus.Util

-- ---------------------------------------------------------------------------
-- Terms
-- ---------------------------------------------------------------------------

/-- Lending-family contract terms = the dictionary `ContractTerms` over `Float`. -/
abbrev Terms := ContractTerms Float

/-- A blank contract: every optional attribute undefined, sensible defaults for
    the required ones.  Build concrete contracts with record-update syntax,
    e.g. `{ defaultTerms with notionalPrincipal := some 1000.0, … }`. -/
def defaultTerms : Terms where
  contractId         := ""
  contractType       := .PAM
  contractRole       := .CR_RPA
  settlementCurrency := none
  initialExchangeDate := none
  dayCountConvention  := none
  scheduleConfig      := { calendar := none, endOfMonthConvention := none
                           businessDayConvention := none }
  statusDate          := { day := 1, month := 1, year := 2020 }
  marketObjectCodeRef := none
  contractPerformance         := none
  creditEventTypeCovered      := none
  coverageOfCreditEnhancement := none
  guaranteedExposure          := none
  cycleOfFee             := none
  cycleAnchorDateOfFee   := none
  feeAccrued             := none
  feeBasis               := none
  feeRate                := none
  cycleAnchorDateOfInterestPayment         := none
  cycleOfInterestPayment                   := none
  accruedInterest                          := none
  capitalizationEndDate                    := none
  cycleAnchorDateOfInterestCalculationBase := none
  cycleOfInterestCalculationBase           := none
  interestCalculationBase                  := none
  interestCalculationBaseA                 := none
  nominalInterestRate                      := none
  nominalInterestRate2                     := none
  interestScalingMultiplier                := none
  maturityDate     := none
  amortizationDate := none
  exerciseDate     := none
  notionalPrincipal                    := none
  premiumDiscountAtIED                 := none
  cycleAnchorDateOfPrincipalRedemption := none
  cycleOfPrincipalRedemption           := none
  nextPrincipalRedemptionPayment       := none
  purchaseDate                         := none
  priceAtPurchaseDate                  := none
  terminationDate                      := none
  priceAtTerminationDate               := none
  quantity                             := none
  currency                             := none
  currency2                            := none
  scalingIndexAtStatusDate           := none
  cycleAnchorDateOfScalingIndex      := none
  cycleOfScalingIndex                := none
  scalingEffect                      := none
  scalingIndexAtContractDealDate     := none
  marketObjectCodeOfScalingIndex     := none
  notionalScalingMultiplier          := none
  cycleOfOptionality          := none
  cycleAnchorDateOfOptionality := none
  optionStrike1               := none
  settlementPeriod := none
  exerciseAmount   := none
  futuresPrice     := none
  penaltyRate      := none
  penaltyType      := none
  prepaymentEffect := none
  cycleOfRateReset           := none
  cycleAnchorDateOfRateReset := none
  nextResetRate              := none
  rateSpread                 := none
  rateMultiplier             := none
  periodFloor                := none
  periodCap                  := none
  lifeCap                    := none
  lifeFloor                  := none
  marketObjectCodeOfRateReset := none
  cycleOfDividend           := none
  cycleAnchorDateOfDividend := none
  nextDividendPaymentAmount := none
  enableSettlement := false

namespace Terms

@[inline] private def f (o : Option Float) : Float := o.getD 0.0

def nt    (ct : Terms) : Float := f ct.notionalPrincipal
def ipnr  (ct : Terms) : Float := f ct.nominalInterestRate
def fer   (ct : Terms) : Float := f ct.feeRate
def pdied (ct : Terms) : Float := f ct.premiumDiscountAtIED
def pprd  (ct : Terms) : Float := f ct.priceAtPurchaseDate
def ptd   (ct : Terms) : Float := f ct.priceAtTerminationDate
def pyrt  (ct : Terms) : Float := f ct.penaltyRate
def rrsp  (ct : Terms) : Float := f ct.rateSpread
/-- Rate multiplier defaults to `1.0` (identity) when absent. -/
def rrmlt (ct : Terms) : Float := ct.rateMultiplier.getD 1.0
-- Absent rate caps/floors impose no bound: `±∞` so `min`/`max` are no-ops.
private def posInf : Float := 1.0 / 0.0
private def negInf : Float := -1.0 / 0.0
def rrpc  (ct : Terms) : Float := ct.periodCap.getD posInf
def rrpf  (ct : Terms) : Float := ct.periodFloor.getD negInf
def rrlc  (ct : Terms) : Float := ct.lifeCap.getD posInf
def rrlf  (ct : Terms) : Float := ct.lifeFloor.getD negInf
def rrnxt (ct : Terms) : Float := f ct.nextResetRate
def prnxt (ct : Terms) : Float := f ct.nextPrincipalRedemptionPayment
def ipcba (ct : Terms) : Float := f ct.interestCalculationBaseA
def feb   (ct : Terms) : FeeBasis := ct.feeBasis.getD .FEB_A
def scief (ct : Terms) : ScalingEffect := ct.scalingEffect.getD .SE_OOO
def scied (ct : Terms) : Float := ct.scalingIndexAtContractDealDate.getD 1.0
def cntrl (ct : Terms) : ContractRole := ct.contractRole
def dcc   (ct : Terms) : DayCountConvention := ct.dayCountConvention.getD .DCC_A_360

end Terms

-- ---------------------------------------------------------------------------
-- State
-- ---------------------------------------------------------------------------

/-- Lending-family state variables (ACTUS dictionary short names).  `Md`/`Sd`
    are serial day numbers on the `Time` axis. -/
structure State where
  md    : Time          -- maturity date
  nt    : Float         -- notional principal      (Nt)
  ipnr  : Float         -- nominal interest rate    (Ipnr)
  ipac  : Float         -- accrued interest         (Ipac)
  feac  : Float         -- fee accrued              (Feac)
  nsc   : Float         -- notional scaling mult.   (Nsc)
  isc   : Float         -- interest scaling mult.   (Isc)
  prnxt : Float         -- next principal redemption (Prnxt)
  ipcb  : Float         -- interest calculation base (Ipcb)
  prf   : Performance   -- contract performance      (Prf)
  sd    : Time          -- status date               (Sd)
  deriving Repr

-- ---------------------------------------------------------------------------
-- Risk-factor observer environment  (Oʳᶠ / Oᵉᵛ, §5)
-- ---------------------------------------------------------------------------

/-- The risk-factor observations the lending STF/POF formulas depend on.
    `curs` is the settlement-currency factor `X^CURS(t)`; `marketRate` is
    `Oʳᶠ(RRMO, t)`; `prepayment` is `Oᵉᵛ(CID, PP, t)`. -/
structure RiskFactorEnv where
  curs       : Time → Float := fun _ => 1.0
  marketRate : Time → Float := fun _ => 0.0
  prepayment : Time → Float := fun _ => 0.0
  /-- Year fractions of the principal-redemption periods remaining as of a reset
      time, used to recompute the ANN annuity amount `A` (§3.8).  External
      schedule context, hence modeled here like a risk-factor observation;
      defaults to `[]` (no effect) for the non-annuity contracts. -/
  annuityYfs : Time → List Float := fun _ => []
  /-- Scaling index `Oʳᶠ(SCMO, t)` driving the `SC` scaling multipliers. -/
  scalingIndex : Time → Float := fun _ => 1.0

/-- Trivial environment: unit fx factor, no market rate, no prepayment. -/
def RiskFactorEnv.id : RiskFactorEnv := {}

-- ---------------------------------------------------------------------------
-- Year fraction between two Time points (serial day numbers)
-- ---------------------------------------------------------------------------

/-- Does the scaling effect scale interest (`Isc`)? -/
def scalesInterest : ScalingEffect → Bool
  | .SE_IOO | .SE_INO => true | _ => false

/-- Does the scaling effect scale the notional (`Nsc`)? -/
def scalesNotional : ScalingEffect → Bool
  | .SE_ONO | .SE_INO => true | _ => false

/-- `Y(s, t)` for the contract's day-count convention, with `s`,`t` on the
    `Time` axis (converted back to calendar dates via `ofEpochDay`). -/
def yf (ct : Terms) (s t : Time) : Float :=
  DayCount.yearFraction (Terms.dcc ct) (Date.ofEpochDay s) (Date.ofEpochDay t)

end Actus.Contract.Lending
