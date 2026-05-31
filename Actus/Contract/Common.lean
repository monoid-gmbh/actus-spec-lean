/-
## Shared state, terms accessors, and risk-factor environment (lending family)

PAM, LAM, NAM and ANN share the same state-variable vocabulary and reuse each
other's state-transition functions ("Same as PAM", `STF_X_PAM()` in §7.2–7.5).
To make that reuse literal we use **one** `State` record and the dictionary
`ContractTerms` for all four contracts.

Everything here is **generic over the amount type `α`** (an `Amount`): the same
definitions are instantiated at `Float` for the executable engine and at `ℝ` for
the relational specification and its metatheorems.

* `State α` — the lending state variables (`Md, Nt, Ipnr, Ipac, Feac, Nsc, Isc,
  Prnxt, Ipcb, Prf, Sd`).
* term accessors (`nt`, `ipnr`, `fer`, …) resolve the `Option` dictionary fields
  to concrete values with ACTUS defaults, so the STF/POF formulas stay readable.
* `RiskFactorEnv α` — the observer interface `Oʳᶠ / Oᵉᵛ` (§5), restricted to the
  quantities the lending STF/POF formulas reference.  The **year fraction**
  `Y(s, t)` is included here as a convention observation: over `Float` the engine
  supplies the real day-count computation; the `ℝ` spec takes it abstractly.
-/

import Actus.Protocol
import Actus.Util.Date
import Actus.Util.DayCount
import Actus.Util.Conventions
import Actus.Util.Amount

namespace Actus.Contract

open Actus.Protocol
open Actus.Util
open Actus (Amount)

-- ---------------------------------------------------------------------------
-- Terms
-- ---------------------------------------------------------------------------

/-- Shared contract terms = the dictionary `ContractTerms` over `α`. -/
abbrev Terms (α : Type) := ContractTerms α

/-- A blank `Float` contract: every optional attribute undefined, sensible
    defaults for the required ones.  Build concrete contracts with record-update
    syntax, e.g. `{ defaultTerms with notionalPrincipal := some 1000.0, … }`. -/
def defaultTerms : Terms Float where
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
  notionalPrincipal2                   := none
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
  optionType                  := none
  optionExerciseType          := none
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
  marketObjectCodeOfDividends := none
  contractStructure := none
  deliverySettlement := none
  enableSettlement := false

namespace Terms

variable {α : Type}

@[inline] private def f [Amount α] (o : Option α) : α := o.getD 0

def nt    [Amount α] (ct : Terms α) : α := f ct.notionalPrincipal
def ipnr  [Amount α] (ct : Terms α) : α := f ct.nominalInterestRate
def fer   [Amount α] (ct : Terms α) : α := f ct.feeRate
def pdied [Amount α] (ct : Terms α) : α := f ct.premiumDiscountAtIED
def pprd  [Amount α] (ct : Terms α) : α := f ct.priceAtPurchaseDate
def ptd   [Amount α] (ct : Terms α) : α := f ct.priceAtTerminationDate
def pyrt  [Amount α] (ct : Terms α) : α := f ct.penaltyRate
def rrsp  [Amount α] (ct : Terms α) : α := f ct.rateSpread
/-- Rate multiplier defaults to `1` (identity) when absent. -/
def rrmlt [Amount α] (ct : Terms α) : α := ct.rateMultiplier.getD 1
def rrnxt [Amount α] (ct : Terms α) : α := f ct.nextResetRate
def prnxt [Amount α] (ct : Terms α) : α := f ct.nextPrincipalRedemptionPayment
def ipcba [Amount α] (ct : Terms α) : α := f ct.interestCalculationBaseA
def feb   (ct : Terms α) : FeeBasis := ct.feeBasis.getD .FEB_A
def scief (ct : Terms α) : ScalingEffect := ct.scalingEffect.getD .SE_OOO
def scied [Amount α] (ct : Terms α) : α := ct.scalingIndexAtContractDealDate.getD 1
def cntrl (ct : Terms α) : ContractRole := ct.contractRole
def dcc   (ct : Terms α) : DayCountConvention := ct.dayCountConvention.getD .DCC_A_360

end Terms

-- ---------------------------------------------------------------------------
-- Rate caps/floors as clamps (absent bound = no clamp; no `±∞` needed)
-- ---------------------------------------------------------------------------

/-- Apply an optional upper bound: `min x c` when present, else `x`. -/
def clampHi {α : Type} [Amount α] (c : Option α) (x : α) : α :=
  match c with | some c => min x c | none => x

/-- Apply an optional lower bound: `max x f` when present, else `x`. -/
def clampLo {α : Type} [Amount α] (fl : Option α) (x : α) : α :=
  match fl with | some fl => max x fl | none => x

-- ---------------------------------------------------------------------------
-- State
-- ---------------------------------------------------------------------------

/-- Shared contract state variables (ACTUS dictionary short names).  `Md`/`Sd`
    are serial day numbers on the `Time` axis; the monetary/rate variables have
    the generic amount type `α`. -/
structure State (α : Type) where
  md    : Time          -- maturity date
  nt    : α             -- notional principal       (Nt)
  ipnr  : α             -- nominal interest rate     (Ipnr)
  ipac  : α             -- accrued interest          (Ipac)
  feac  : α             -- fee accrued               (Feac)
  nsc   : α             -- notional scaling mult.    (Nsc)
  isc   : α             -- interest scaling mult.    (Isc)
  prnxt : α             -- next principal redemption (Prnxt)
  ipcb  : α             -- interest calculation base (Ipcb)
  prf   : Performance   -- contract performance      (Prf)
  sd    : Time          -- status date               (Sd)
  deriving Repr

-- ---------------------------------------------------------------------------
-- Risk-factor observer environment  (Oʳᶠ / Oᵉᵛ, §5)
-- ---------------------------------------------------------------------------

/-- The risk-factor observations the lending STF/POF formulas depend on.
    `curs` is the settlement-currency factor `X^CURS(t)`; `marketRate` is
    `Oʳᶠ(RRMO, t)`; `prepayment` is `Oᵉᵛ(CID, PP, t)`; `yf s t` is the year
    fraction `Y(s, t)` (a convention observation — see the module header). -/
structure RiskFactorEnv (α : Type) [Amount α] where
  curs       : Time → α := fun _ => 1
  marketRate : Time → α := fun _ => 0
  prepayment : Time → α := fun _ => 0
  /-- Year fractions of the principal-redemption periods remaining as of a reset
      time, used to recompute the ANN annuity amount `A` (§3.8). -/
  annuityYfs : Time → List α := fun _ => []
  /-- Scaling index `Oʳᶠ(SCMO, t)` driving the `SC` scaling multipliers. -/
  scalingIndex : Time → α := fun _ => 1
  /-- Market rate by market-object code: `Oʳᶠ(m, t)`.  Used by composite
      contracts (SWAPS) to resolve each leg's own rate-reset series. -/
  marketRateOf : String → Time → α := fun _ _ => 0
  /-- Observed dividend stream `Oᵉᵛ(DV)` — (date, amount) pairs (STK). -/
  dividends : List (Time × α) := []
  /-- Year fraction `Y(s, t)` between two `Time` points. -/
  yf : Time → Time → α := fun _ _ => 0
  /-- Maturity / termination given as end-of-day (`23:59:59`): the event settles
      and accrues to the *next* midnight while the schedule structure uses the
      written date (§2.8). -/
  maturityEOD    : Bool := false
  terminationEOD : Bool := false
  purchaseEOD    : Bool := false

/-- Trivial environment: unit fx factor, no market rate, no prepayment. -/
def RiskFactorEnv.id {α : Type} [Amount α] : RiskFactorEnv α := {}

-- ---------------------------------------------------------------------------
-- Scaling effects
-- ---------------------------------------------------------------------------

/-- Does the scaling effect scale interest (`Isc`)? -/
def scalesInterest : ScalingEffect → Bool
  | .SE_IOO | .SE_INO => true | _ => false

/-- Does the scaling effect scale the notional (`Nsc`)? -/
def scalesNotional : ScalingEffect → Bool
  | .SE_ONO | .SE_INO => true | _ => false

-- ---------------------------------------------------------------------------
-- Year fraction (Float): the executable day-count computation used to build a
-- `Float` `RiskFactorEnv.yf`.  (The relational spec over `ℝ` takes `yf`
-- abstractly from the environment instead.)
-- ---------------------------------------------------------------------------

/-- `Y(s, t)` for the contract's day-count convention, with `s`,`t` on the
    `Time` axis (converted back to calendar dates via `ofEpochDay`). -/
def yf (ct : Terms Float) (s t : Time) : Float :=
  DayCount.yearFraction (Terms.dcc ct) (Date.ofEpochDay s) (Date.ofEpochDay t)

end Actus.Contract
