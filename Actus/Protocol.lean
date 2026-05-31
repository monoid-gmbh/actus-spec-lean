/-
## ACTUS domain

All enumeration types, record types, event types, and core cashflow aliases
used throughout the ACTUS formal specification.

Translated from `Actus/Protocol.lagda.md` (Agda) to Lean 4.
-/

namespace Actus.Protocol

-- ---------------------------------------------------------------------------
-- Contract Type
-- ---------------------------------------------------------------------------

inductive ContractType where
  | PAM   -- Principal at maturity
  | LAM   -- Linear amortizer
  | NAM   -- Negative amortizer
  | ANN   -- Annuity
  | STK   -- Stock
  | OPTNS -- Option
  | FUTUR -- Future
  | COM   -- Commodity
  | CSH   -- Cash
  | CLM   -- Call Money
  | SWPPV -- Plain Vanilla Swap
  | SWAPS -- Swap
  | CEG   -- Guarantee
  | CEC   -- Collateral
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Contract Role
-- ---------------------------------------------------------------------------

inductive ContractRole where
  | CR_RPA -- Real position asset
  | CR_RPL -- Real position liability
  | CR_CLO -- Role of a collateral
  | CR_CNO -- Role of a close-out-netting
  | CR_COL -- Role of an underlying to a collateral
  | CR_LG  -- Long position
  | CR_ST  -- Short position
  | CR_BUY -- Protection buyer
  | CR_SEL -- Protection seller
  | CR_RFL -- Receive first leg
  | CR_PFL -- Pay first leg
  | CR_RF  -- Receive fix leg
  | CR_PF  -- Pay fix leg
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Day Count Convention
-- ---------------------------------------------------------------------------

inductive DayCountConvention where
  | DCC_A_AISDA     -- Actual/Actual ISDA
  | DCC_A_360       -- Actual/360
  | DCC_A_365       -- Actual/365
  | DCC_E30_360ISDA -- 30E/360 ISDA
  | DCC_E30_360     -- 30E/360
  | DCC_B_252       -- Business / 252
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- End of Month Convention
-- ---------------------------------------------------------------------------

inductive EndOfMonthConvention where
  | EOMC_EOM -- End of month
  | EOMC_SD  -- Same day
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Business Day Convention
-- ---------------------------------------------------------------------------

inductive BusinessDayConvention where
  | BDC_NULL -- No shift
  | BDC_SCF  -- Shift/calculate following
  | BDC_SCMF -- Shift/calculate modified following
  | BDC_CSF  -- Calculate/shift following
  | BDC_CSMF -- Calculate/shift modified following
  | BDC_SCP  -- Shift/calculate preceding
  | BDC_SCMP -- Shift/calculate modified preceding
  | BDC_CSP  -- Calculate/shift preceding
  | BDC_CSMP -- Calculate/shift modified preceding
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Calendar
-- ---------------------------------------------------------------------------

inductive Calendar where
  | CLDR_MF -- Monday to Friday
  | CLDR_NC -- No calendar
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Schedule Configuration
-- ---------------------------------------------------------------------------

structure ScheduleConfig where
  calendar              : Option Calendar
  endOfMonthConvention  : Option EndOfMonthConvention
  businessDayConvention : Option BusinessDayConvention
  deriving Repr

-- ---------------------------------------------------------------------------
-- Contract Performance
-- ---------------------------------------------------------------------------

inductive Performance where
  | PRF_PF -- Performant
  | PRF_DL -- Delayed
  | PRF_DQ -- Delinquent
  | PRF_DF -- Default
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Credit Event Type Covered
-- ---------------------------------------------------------------------------

inductive CreditEventTypeCovered where
  | CETC_DL -- Delayed
  | CETC_DQ -- Delinquent
  | CETC_DF -- Default
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Guaranteed Exposure
-- ---------------------------------------------------------------------------

inductive CreditEventGuaranteedExposure where
  | CEGE_NO -- Nominal value
  | CEGE_NI -- Nominal interest
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Fee Basis
-- ---------------------------------------------------------------------------

inductive FeeBasis where
  | FEB_A -- Absolute value
  | FEB_N -- Notional
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Interest Calculation Base
-- ---------------------------------------------------------------------------

inductive InterestCalculationBase where
  | IPCB_NT    -- Notional
  | IPCB_NTIED -- Notional + Interest at IED
  | IPCB_NTL   -- Notional - Life cap
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Scaling Effect
-- ---------------------------------------------------------------------------

inductive ScalingEffect where
  | SE_OOO -- No scaling
  | SE_IOO -- Interest only
  | SE_ONO -- Notional only
  | SE_OOM -- Maximum of notional and interest
  | SE_INO -- Interest and notional
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Penalty Type
-- ---------------------------------------------------------------------------

inductive PenaltyType where
  | PYTP_A -- Absolute
  | PYTP_N -- Nominal rate
  | PYTP_I -- Current interest rate differential
  | PYTP_O -- No penalty
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Prepayment Effect
-- ---------------------------------------------------------------------------

inductive PrepaymentEffect where
  | PPEF_N -- No prepayment
  | PPEF_A -- Prepayment allowed with penalty
  | PPEF_M -- Prepayment allowed without penalty
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Delivery Settlement
-- ---------------------------------------------------------------------------

inductive DeliverySettlement where
  | DS_S -- Settlement
  | DS_D -- Delivery
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Object Code Collateral
-- ---------------------------------------------------------------------------

inductive ObjectCodeCollateral where
  | OBJC_A -- Collateral applies
  | OBJC_N -- No collateral
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Seniority
-- ---------------------------------------------------------------------------

inductive Seniority where
  | SE_S -- Senior
  | SE_J -- Junior
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Cycle
-- ---------------------------------------------------------------------------

structure Cycle where
  n      : Nat
  period : String  -- P, Y, M, W, D, etc.
  stub   : Bool
  deriving Repr

-- ---------------------------------------------------------------------------
-- Period
-- ---------------------------------------------------------------------------

structure Period where
  n          : Nat
  period     : String
  isLongStub : Bool
  deriving Repr

-- ---------------------------------------------------------------------------
-- Reference Role
-- ---------------------------------------------------------------------------

inductive ReferenceRole where
  | FIL -- First leg
  | SEL -- Second leg
  | MOC -- Matched object code
  deriving Repr, DecidableEq

-- ---------------------------------------------------------------------------
-- Local Time
-- ---------------------------------------------------------------------------

structure LocalTime where
  day   : Nat
  month : Nat
  year  : Nat
  deriving Repr

-- ---------------------------------------------------------------------------
-- Mutually recursive: Reference, ContractStructure, ContractTerms
-- ---------------------------------------------------------------------------

mutual
  inductive Reference (α : Type) : Type where
    | referenceTerms : ContractTerms α → Reference α
    | referenceId    : String → Reference α

  inductive ContractStructure (α : Type) : Type where
    | mk : Reference α → ReferenceRole → ContractType → ContractStructure α

  structure ContractTerms (α : Type) : Type where
    -- General
    contractId         : String
    contractType       : ContractType
    contractRole       : ContractRole
    settlementCurrency : Option String
    -- Calendar
    initialExchangeDate                      : Option LocalTime
    dayCountConvention                       : Option DayCountConvention
    scheduleConfig                           : ScheduleConfig
    -- Contract Identification
    statusDate          : LocalTime
    marketObjectCodeRef : Option String
    -- Counterparty
    contractPerformance         : Option Performance
    creditEventTypeCovered      : Option CreditEventTypeCovered
    coverageOfCreditEnhancement : Option α
    guaranteedExposure          : Option CreditEventGuaranteedExposure
    -- Fees
    cycleOfFee             : Option Cycle
    cycleAnchorDateOfFee   : Option LocalTime
    feeAccrued             : Option α
    feeBasis               : Option FeeBasis
    feeRate                : Option α
    -- Interest
    cycleAnchorDateOfInterestPayment         : Option LocalTime
    cycleOfInterestPayment                   : Option Cycle
    accruedInterest                          : Option α
    capitalizationEndDate                    : Option LocalTime
    cycleAnchorDateOfInterestCalculationBase : Option LocalTime
    cycleOfInterestCalculationBase           : Option Cycle
    interestCalculationBase                  : Option InterestCalculationBase
    interestCalculationBaseA                 : Option α
    nominalInterestRate                      : Option α
    nominalInterestRate2                     : Option α
    interestScalingMultiplier                : Option α
    -- Dates
    maturityDate     : Option LocalTime
    amortizationDate : Option LocalTime
    exerciseDate     : Option LocalTime
    -- Notional Principal
    notionalPrincipal                    : Option α
    premiumDiscountAtIED                 : Option α
    cycleAnchorDateOfPrincipalRedemption : Option LocalTime
    cycleOfPrincipalRedemption           : Option Cycle
    nextPrincipalRedemptionPayment       : Option α
    purchaseDate                         : Option LocalTime
    priceAtPurchaseDate                  : Option α
    terminationDate                      : Option LocalTime
    priceAtTerminationDate               : Option α
    quantity                             : Option α
    currency                             : Option String
    currency2                            : Option String
    -- Scaling Index
    scalingIndexAtStatusDate           : Option α
    cycleAnchorDateOfScalingIndex      : Option LocalTime
    cycleOfScalingIndex                : Option Cycle
    scalingEffect                      : Option ScalingEffect
    scalingIndexAtContractDealDate     : Option α
    marketObjectCodeOfScalingIndex     : Option String
    notionalScalingMultiplier          : Option α
    -- Optionality
    cycleOfOptionality          : Option Cycle
    cycleAnchorDateOfOptionality : Option LocalTime
    optionStrike1               : Option α
    -- Settlement
    settlementPeriod : Option Cycle
    exerciseAmount   : Option α
    futuresPrice     : Option α
    -- Penalty
    penaltyRate      : Option α
    penaltyType      : Option PenaltyType
    prepaymentEffect : Option PrepaymentEffect
    -- Rate Reset
    cycleOfRateReset           : Option Cycle
    cycleAnchorDateOfRateReset : Option LocalTime
    nextResetRate              : Option α
    rateSpread                 : Option α
    rateMultiplier             : Option α
    periodFloor                : Option α
    periodCap                  : Option α
    lifeCap                    : Option α
    lifeFloor                  : Option α
    marketObjectCodeOfRateReset : Option String
    -- Dividend
    cycleOfDividend           : Option Cycle
    cycleAnchorDateOfDividend : Option LocalTime
    nextDividendPaymentAmount : Option α
    -- Composite contracts (e.g. SWAPS): the child legs and their reference roles
    contractStructure : Option (List (ContractStructure α))
    -- Settlement mode for composites: "S" = net/cash, else gross/delivery ("D")
    deliverySettlement : Option String
    -- Misc
    enableSettlement : Bool
end

-- ---------------------------------------------------------------------------
-- Event Type
-- ---------------------------------------------------------------------------

inductive EventType where
  | AD   -- Analysis date
  | IED  -- Initial exchange date
  | FP   -- Fee payment
  | PR   -- Principal redemption
  | PD   -- Principal drawing
  | PRD  -- Purchase
  | TD   -- Termination date
  | IP   -- Interest payment
  | IPCI -- Interest capitalization
  | IPCB -- Interest calculation base fixing
  | RR   -- Rate reset
  | RRF  -- Rate reset fixing
  | DV   -- Dividend payment
  | PRF  -- Principal prepayment (free)
  | PY   -- Penalty payment
  | PP   -- Principal prepayment (penalty)
  | CD   -- Credit default
  | STD  -- Settlement date
  | MD   -- Maturity date
  | XD   -- Exercise date
  | SC   -- Scaling index fixing
  | CE   -- Credit event
  | PI   -- Premium payment
  deriving Repr, DecidableEq

/-- Priority for intra-timestamp event ordering (lower = processed first).
    Order derived from the ACTUS reference event sequences: in particular
    `PR < IP`, `IP` before rate resets / scaling / `IPCB`, and interest (`IP`)
    before contract-closing events (`PRD`, `TD`, `MD`) so it accrues on the full
    notional before the contract is purchased/terminated/matured. -/
def eventTypePriority : EventType → Nat
  | .AD   => 0  | .IED  => 1  | .FP   => 2  | .PR   => 3
  | .PD   => 4  | .IPCI => 5  | .IP   => 6  | .RRF  => 7
  | .RR   => 8  | .IPCB => 9  | .SC   => 10 | .PRF  => 11
  | .PY   => 12 | .PP   => 13 | .DV   => 14 | .CD   => 15
  | .STD  => 16 | .PRD  => 17 | .TD   => 18 | .XD   => 19
  | .MD   => 20 | .CE   => 21 | .PI   => 22

/-- String representation of an event type. -/
def eventTypeToString : EventType → String
  | .AD   => "AD"  | .IED  => "IED"  | .FP   => "FP"  | .PR   => "PR"
  | .PD   => "PD"  | .PRD  => "PRD"  | .TD   => "TD"  | .IP   => "IP"
  | .IPCI => "IPCI"| .IPCB => "IPCB" | .RR   => "RR"  | .RRF  => "RRF"
  | .DV   => "DV"  | .PRF  => "PRF"  | .PY   => "PY"  | .PP   => "PP"
  | .CD   => "CD"  | .STD  => "STD"  | .MD   => "MD"  | .XD   => "XD"
  | .SC   => "SC"  | .CE   => "CE"   | .PI   => "PI"

-- ---------------------------------------------------------------------------
-- Convention functions
--
-- The Year Fraction Convention `Y : s, t, DCC → ℝ` (§3.6) and the Contract Role
-- Sign `R : CNTRL → {-1, +1}` (§3.7) are implemented in the utility layer:
--   `Actus.Util.DayCount.yearFraction`  and  `Actus.Util.Conventions.sign`.
-- They live there (not here) because they depend on the date arithmetic in
-- `Actus.Util.Date`, which in turn imports this module.
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Risk Factor
-- ---------------------------------------------------------------------------

inductive RiskFactor where
  | CURS : Float → RiskFactor
  | XXXX : Float → RiskFactor
  deriving Repr

-- ---------------------------------------------------------------------------
-- Core time / cashflow aliases
-- ---------------------------------------------------------------------------

abbrev Time      := Nat
abbrev Payoff    := Float
abbrev Event     := Time × EventType
abbrev Cashflow  := Event × Payoff
abbrev Schedule  := List Event
abbrev Cashflows := List Cashflow

end Actus.Protocol
