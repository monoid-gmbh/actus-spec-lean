/-
## JSON parser for the ACTUS reference test format

Reads contracts from the ACTUS Foundation reference test suite (`actus-tests`),
whose files are a JSON object keyed by test id:

```json
{ "pam01": { "identifier": "pam01",
             "terms": { "contractType": "PAM", "contractRole": "RPA", … },
             "to": "2014-01-01T00:00:00",
             "dataObserved": { … },
             "eventsObserved": [ { "type": "IED", "time": "…", "payoff": … }, … ] },
  … }
```

* `termsFromJson` decodes a `terms` object into `ContractTerms Float`, starting
  from `defaultTerms` and overriding the keys that are present.
* `testCaseFromJson` / `testFileFromJson` decode the surrounding wrapper.
* `riskFactorsFromJson` builds a `RiskFactorEnv` from `dataObserved`.
* `cashflowsOf` dispatches on `contractType` to the lending engine.

Scope: the lending family (PAM/LAM/NAM/ANN).  Other contract types parse into
`Terms` fine but `cashflowsOf` returns `[]` for them.

Number values may be JSON numbers *or* strings (the reference suite uses both);
`jsonToFloat` accepts either, routing strings through `Json.parse` since
`String.toFloat?` is not in core Lean.
-/

import Lean.Data.Json
import Actus.Protocol
import Actus.Contract.Common
import Actus.Contract.Execution

namespace Actus.IO.Parse

open Lean (Json JsonNumber)
open Actus.Protocol
open Actus.Contract

-- ---------------------------------------------------------------------------
-- Scalar decoders
-- ---------------------------------------------------------------------------

/-- A JSON number, or a numeric string (`"1000.0"`), to `Float`. -/
def jsonToFloat (j : Json) : Except String Float :=
  match j with
  | .num n => .ok n.toFloat
  | .str s => do
      let j' ← Json.parse s
      let n ← j'.getNum?
      pure n.toFloat
  | _ => .error s!"expected number, got {j.compress}"

/-- ISO-8601 date(-time) string `"YYYY-MM-DD[THH:MM:SS]"` to `LocalTime`.  (The
    `23:59:59` end-of-day convention extends accrual to the next midnight but the
    event is still stamped on the written date, so the date part is taken as-is.) -/
def parseDate (s : String) : Except String LocalTime :=
  let datePart := (s.splitOn "T").headD s
  match datePart.splitOn "-" with
  | [y, m, d] =>
    match y.toNat?, m.toNat?, d.toNat? with
    | some y, some m, some d => .ok { day := d, month := m, year := y }
    | _, _, _ => .error s!"bad date '{s}'"
  | _ => .error s!"bad date '{s}'"

/-- Is the timestamp end-of-day (`…T23:59:59`)? -/
def isEndOfDay (s : String) : Bool :=
  (((s.splitOn "T").drop 1).headD "").startsWith "23:59:59"

/-- Like `parseDate`, but a `23:59:59` end-of-day timestamp rolls to the next
    midnight (used for *event* dates so computed and expected events align). -/
def parseDateRoll (s : String) : Except String LocalTime := do
  let base ← parseDate s
  pure (if isEndOfDay s then Actus.Util.Date.addDays base 1 else base)

/-- ACTUS cycle string, e.g. `"P1ML1"` (period 1 Month, long stub) or the older
    `"1M-"` form, to `Cycle`.  The leading `P` and a trailing stub marker
    (`L0`/`L1`, or a `+`/`-` suffix) are both accepted; `L1` or `+` mark a long
    stub. -/
def parseCycle (s : String) : Except String Cycle := do
  let cs := s.toList
  let cs := match cs with | 'P' :: rest => rest | _ => cs
  let (digits, rest) := cs.span Char.isDigit
  if digits.isEmpty then .error s!"cycle '{s}': missing count"
  let n := (String.ofList digits).toNat?.getD 0
  match rest with
  | unit :: tail =>
    let period := String.ofList [unit]
    if ["D", "W", "M", "Q", "H", "Y"].contains period then
      let stub := tail.any (fun c => c == '1' || c == '+')
      pure { n := n, period := period, stub := stub }
    else .error s!"cycle '{s}': bad period unit '{period}'"
  | [] => .error s!"cycle '{s}': missing period unit"

private def enum (what : String) (table : List (String × α)) (s : String) :
    Except String α :=
  match table.find? (·.1 == s) with
  | some (_, v) => .ok v
  | none        => .error s!"unknown {what} code '{s}'"

def contractTypeOf : String → Except String ContractType := enum "contractType"
  [("PAM", .PAM), ("LAM", .LAM), ("NAM", .NAM), ("ANN", .ANN), ("STK", .STK),
   ("OPTNS", .OPTNS), ("FUTUR", .FUTUR), ("COM", .COM), ("CSH", .CSH),
   ("CLM", .CLM), ("SWPPV", .SWPPV), ("SWAPS", .SWAPS), ("CEG", .CEG), ("CEC", .CEC),
   ("FXOUT", .FXOUT), ("UMP", .UMP), ("CAPFL", .CAPFL), ("LAX", .LAX)]

def contractRoleOf : String → Except String ContractRole := enum "contractRole"
  [("RPA", .CR_RPA), ("RPL", .CR_RPL), ("CLO", .CR_CLO), ("CNO", .CR_CNO),
   ("COL", .CR_COL), ("LG", .CR_LG), ("ST", .CR_ST), ("BUY", .CR_BUY),
   ("SEL", .CR_SEL), ("RFL", .CR_RFL), ("PFL", .CR_PFL), ("RF", .CR_RF), ("PF", .CR_PF)]

def dayCountOf : String → Except String DayCountConvention := enum "dayCountConvention"
  [("AA", .DCC_A_AISDA), ("A/AISDA", .DCC_A_AISDA),
   ("A360", .DCC_A_360), ("A/360", .DCC_A_360),
   ("A365", .DCC_A_365), ("A/365", .DCC_A_365),
   ("30E360ISDA", .DCC_E30_360ISDA), ("30E/360ISDA", .DCC_E30_360ISDA),
   ("30E360", .DCC_E30_360), ("30E/360", .DCC_E30_360),
   ("B252", .DCC_B_252), ("B/252", .DCC_B_252)]

def eomOf : String → Except String EndOfMonthConvention := enum "endOfMonthConvention"
  [("EOM", .EOMC_EOM), ("SD", .EOMC_SD)]

def bdcOf : String → Except String BusinessDayConvention := enum "businessDayConvention"
  [("NULL", .BDC_NULL), ("SCF", .BDC_SCF), ("SCMF", .BDC_SCMF), ("CSF", .BDC_CSF),
   ("CSMF", .BDC_CSMF), ("SCP", .BDC_SCP), ("SCMP", .BDC_SCMP), ("CSP", .BDC_CSP),
   ("CSMP", .BDC_CSMP)]

def calendarOf : String → Except String Calendar := enum "calendar"
  [("MF", .CLDR_MF), ("NC", .CLDR_NC), ("NOCALENDAR", .CLDR_NC),
   ("MONDAYTOFRIDAY", .CLDR_MF)]

def referenceRoleOf : String → Except String ReferenceRole := enum "referenceRole"
  [("FIL", .FIL), ("SEL", .SEL), ("MOC", .MOC), ("UDL", .UDL),
   ("COVE", .COVE), ("COVI", .COVI)]

def performanceOf : String → Except String Performance := enum "contractPerformance"
  [("PF", .PRF_PF), ("DL", .PRF_DL), ("DQ", .PRF_DQ), ("DF", .PRF_DF)]

def creditEventTypeOf : String → Except String CreditEventTypeCovered :=
  enum "creditEventTypeCovered" [("DL", .CETC_DL), ("DQ", .CETC_DQ), ("DF", .CETC_DF)]

def guaranteedExposureOf : String → Except String CreditEventGuaranteedExposure :=
  enum "guaranteedExposure" [("NO", .CEGE_NO), ("NI", .CEGE_NI)]

def feeBasisOf : String → Except String FeeBasis := enum "feeBasis"
  [("A", .FEB_A), ("N", .FEB_N)]

def icbOf : String → Except String InterestCalculationBase := enum "interestCalculationBase"
  [("NT", .IPCB_NT), ("NTIED", .IPCB_NTIED), ("NTL", .IPCB_NTL)]

def penaltyTypeOf : String → Except String PenaltyType := enum "penaltyType"
  [("O", .PYTP_O), ("A", .PYTP_A), ("N", .PYTP_N), ("I", .PYTP_I)]

def prepaymentOf : String → Except String PrepaymentEffect := enum "prepaymentEffect"
  [("N", .PPEF_N), ("A", .PPEF_A), ("M", .PPEF_M)]

def scalingEffectOf : String → Except String ScalingEffect := enum "scalingEffect"
  [("OOO", .SE_OOO), ("000", .SE_OOO), ("IOO", .SE_IOO), ("I00", .SE_IOO),
   ("ONO", .SE_ONO), ("0N0", .SE_ONO), ("OOM", .SE_OOM), ("00M", .SE_OOM),
   ("INO", .SE_INO), ("IN0", .SE_INO)]

-- ---------------------------------------------------------------------------
-- Field helpers
-- ---------------------------------------------------------------------------

/-- The value at key `k`, if present. -/
private def field? (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption

/-- The value at the first present key among `ks` (the reference suite uses
    several spellings, e.g. `eventType`/`type`, `eventDate`/`time`). -/
private def fieldAny? (j : Json) (ks : List String) : Option Json :=
  ks.findSome? (field? j ·)

/-- Required field: error if absent or malformed. -/
private def req (j : Json) (k : String) (p : Json → Except String α) : Except String α :=
  match field? j k with
  | some v => p v
  | none   => .error s!"missing required field '{k}'"

/-- Required field under any of several key spellings. -/
private def reqAny (j : Json) (ks : List String) (p : Json → Except String α) :
    Except String α :=
  match fieldAny? j ks with
  | some v => p v
  | none   => .error s!"missing required field (any of {ks})"

/-- Optional field under any of several key spellings. -/
private def optAny (j : Json) (ks : List String) (p : Json → Except String α) :
    Except String (Option α) :=
  match fieldAny? j ks with
  | some .null     => .ok none
  | some (.str "") => .ok none
  | some v         => (p v).map some
  | none           => .ok none

/-- Optional field: `none` if absent, `null`, or the empty string (the
    reference suite uses `""` for unset attributes); error if present but
    malformed. -/
private def opt (j : Json) (k : String) (p : Json → Except String α) :
    Except String (Option α) :=
  match field? j k with
  | some .null     => .ok none
  | some (.str "") => .ok none
  | some v         => (p v).map some
  | none           => .ok none

private def pStr   (j : Json) : Except String String    := j.getStr?
private def pFloat (j : Json) : Except String Float      := jsonToFloat j
private def pDate  (j : Json) : Except String LocalTime  := do parseDate (← j.getStr?)
private def pCycle (j : Json) : Except String Cycle      := do parseCycle (← j.getStr?)

/-- Parse a field that may be a single scalar *or* a JSON array of scalars into a
    list (the ACTUS array attributes accept either form). -/
private def pList (p : Json → Except String α) (j : Json) : Except String (List α) :=
  match j.getArr? with
  | .ok arr  => arr.toList.mapM p
  | .error _ => (p j).map ([·])
private def pEnum  (f : String → Except String α) (j : Json) : Except String α :=
  do f (← j.getStr?)

-- ---------------------------------------------------------------------------
-- Terms
-- ---------------------------------------------------------------------------

/-- Decode a `terms` object into `ContractTerms Float`. -/
partial def termsFromJson (j : Json) : Except String (Terms Float) := do
  let contractType ← req j "contractType" (pEnum contractTypeOf)
  let contractId   ← (opt j "contractID" pStr).map (·.getD "")
  -- child legs of a composite (SWAPS) omit contractRole — the parent assigns it
  let contractRole ← (opt j "contractRole" (pEnum contractRoleOf)).map (·.getD .CR_RPA)
  let statusDate   ← req j "statusDate" pDate
  -- composite contract structure: recursively parse each child leg's `object`
  let contractStructure : Option (List (ContractStructure Float)) ←
    opt j "contractStructure" (fun v => do
      let arr ← v.getArr?
      (arr.toList.mapM (fun el => do
        let role  ← req el "referenceRole" (pEnum referenceRoleOf)
        let rtyp  ← (opt el "referenceType" pStr).map (·.getD "CNT")
        if rtyp == "MOC" then
          -- underlying referenced by market-object code (not a full contract)
          let moc ← req el "object" (fun o => req o "marketObjectCode" pStr)
          pure (ContractStructure.mk (Reference.referenceId moc) role .PAM)
        else if rtyp == "CID" then
          -- covered/covering contract referenced by contract identifier (CEG/CEC)
          let cid ← req el "object" (fun o => req o "contractIdentifier" pStr)
          pure (ContractStructure.mk (Reference.referenceId cid) role .PAM)
        else
          let child ← req el "object" termsFromJson
          pure (ContractStructure.mk (Reference.referenceTerms child) role child.contractType))))
  let cal ← opt j "calendar" (pEnum calendarOf)
  let bdc ← opt j "businessDayConvention" (pEnum bdcOf)
  let eom ← opt j "endOfMonthConvention" (pEnum eomOf)
  pure { defaultTerms with
    contractId         := contractId
    contractType       := contractType
    contractRole       := contractRole
    statusDate         := statusDate
    settlementCurrency := ← opt j "settlementCurrency" pStr
    currency           := ← opt j "currency" pStr
    dayCountConvention := ← opt j "dayCountConvention" (pEnum dayCountOf)
    scheduleConfig     := { calendar := cal, businessDayConvention := bdc
                            endOfMonthConvention := eom }
    contractPerformance := ← opt j "contractPerformance" (pEnum performanceOf)
    initialExchangeDate := ← opt j "initialExchangeDate" pDate
    maturityDate        := ← opt j "maturityDate" pDate
    amortizationDate    := ← opt j "amortizationDate" pDate
    purchaseDate        := ← opt j "purchaseDate" pDate
    terminationDate     := ← opt j "terminationDate" pDate
    notionalPrincipal   := ← opt j "notionalPrincipal" pFloat
    premiumDiscountAtIED := ← opt j "premiumDiscountAtIED" pFloat
    priceAtPurchaseDate := ← opt j "priceAtPurchaseDate" pFloat
    priceAtTerminationDate := ← opt j "priceAtTerminationDate" pFloat
    -- interest
    nominalInterestRate := ← opt j "nominalInterestRate" pFloat
    accruedInterest     := ← opt j "accruedInterest" pFloat
    cycleAnchorDateOfInterestPayment := ← opt j "cycleAnchorDateOfInterestPayment" pDate
    cycleOfInterestPayment           := ← opt j "cycleOfInterestPayment" pCycle
    capitalizationEndDate            := ← opt j "capitalizationEndDate" pDate
    interestCalculationBase          := ← opt j "interestCalculationBase" (pEnum icbOf)
    interestCalculationBaseA         := ← opt j "interestCalculationBaseAmount" pFloat
    cycleAnchorDateOfInterestCalculationBase :=
      ← opt j "cycleAnchorDateOfInterestCalculationBase" pDate
    cycleOfInterestCalculationBase   := ← opt j "cycleOfInterestCalculationBase" pCycle
    interestScalingMultiplier        := ← opt j "interestScalingMultiplier" pFloat
    notionalScalingMultiplier        := ← opt j "notionalScalingMultiplier" pFloat
    -- principal redemption
    cycleAnchorDateOfPrincipalRedemption :=
      ← opt j "cycleAnchorDateOfPrincipalRedemption" pDate
    cycleOfPrincipalRedemption       := ← opt j "cycleOfPrincipalRedemption" pCycle
    nextPrincipalRedemptionPayment   := ← opt j "nextPrincipalRedemptionPayment" pFloat
    -- array (piecewise) schedules — exotic amortizer (LAX)
    arrayCycleAnchorDateOfInterestPayment :=
      ← opt j "arrayCycleAnchorDateOfInterestPayment" (pList pDate)
    arrayCycleOfInterestPayment :=
      ← opt j "arrayCycleOfInterestPayment" (pList (fun e => (pCycle e).map some))
    arrayCycleAnchorDateOfPrincipalRedemption :=
      ← opt j "arrayCycleAnchorDateOfPrincipalRedemption" (pList pDate)
    arrayCycleOfPrincipalRedemption :=
      ← opt j "arrayCycleOfPrincipalRedemption" (pList (fun e => (pCycle e).map some))
    arrayNextPrincipalRedemptionPayment :=
      ← opt j "arrayNextPrincipalRedemptionPayment" (pList pFloat)
    arrayIncreaseDecrease :=
      ← opt j "arrayIncreaseDecrease" (pList pStr)
    arrayCycleAnchorDateOfRateReset :=
      ← opt j "arrayCycleAnchorDateOfRateReset" (pList pDate)
    arrayRate         := ← opt j "arrayRate" (pList pFloat)
    arrayFixedVariable := ← opt j "arrayFixedVariable" (pList pStr)
    -- fees
    feeBasis             := ← opt j "feeBasis" (pEnum feeBasisOf)
    feeRate              := ← opt j "feeRate" pFloat
    feeAccrued           := ← opt j "feeAccrued" pFloat
    cycleAnchorDateOfFee := ← opt j "cycleAnchorDateOfFee" pDate
    cycleOfFee           := ← opt j "cycleOfFee" pCycle
    -- penalties / prepayment
    penaltyRate      := ← opt j "penaltyRate" pFloat
    penaltyType      := ← opt j "penaltyType" (pEnum penaltyTypeOf)
    prepaymentEffect := ← opt j "prepaymentEffect" (pEnum prepaymentOf)
    -- rate reset
    cycleAnchorDateOfRateReset := ← opt j "cycleAnchorDateOfRateReset" pDate
    cycleOfRateReset           := ← opt j "cycleOfRateReset" pCycle
    nextResetRate              := ← opt j "nextResetRate" pFloat
    rateSpread                 := ← opt j "rateSpread" pFloat
    rateMultiplier             := ← opt j "rateMultiplier" pFloat
    periodFloor                := ← opt j "periodFloor" pFloat
    periodCap                  := ← opt j "periodCap" pFloat
    lifeCap                    := ← opt j "lifeCap" pFloat
    lifeFloor                  := ← opt j "lifeFloor" pFloat
    marketObjectCodeOfRateReset := ← opt j "marketObjectCodeOfRateReset" pStr
    marketObjectCodeRef         := ← opt j "marketObjectCode" pStr
    -- scaling
    scalingEffect                  := ← opt j "scalingEffect" (pEnum scalingEffectOf)
    cycleAnchorDateOfScalingIndex  := ← opt j "cycleAnchorDateOfScalingIndex" pDate
    cycleOfScalingIndex            := ← opt j "cycleOfScalingIndex" pCycle
    marketObjectCodeOfScalingIndex := ← opt j "marketObjectCodeOfScalingIndex" pStr
    scalingIndexAtContractDealDate := ← opt j "scalingIndexAtContractDealDate" pFloat
    scalingIndexAtStatusDate       := ← opt j "scalingIndexAtStatusDate" pFloat
    marketObjectCodeOfDividends    := ← opt j "marketObjectCodeOfDividends" pStr
    quantity                       := ← opt j "quantity" pFloat
    optionStrike1                  := ← opt j "optionStrike1" pFloat
    optionType                     := ← opt j "optionType" pStr
    optionExerciseType             := ← opt j "optionExerciseType" pStr
    futuresPrice                   := ← opt j "futuresPrice" pFloat
    nominalInterestRate2           := ← opt j "nominalInterestRate2" pFloat
    notionalPrincipal2             := ← opt j "notionalPrincipal2" pFloat
    currency2                      := ← opt j "currency2" pStr
    settlementPeriod               := ← opt j "settlementPeriod" pCycle
    xDayNotice                     := ← opt j "xDayNotice" pCycle
    contractStructure              := contractStructure
    deliverySettlement             := ← opt j "deliverySettlement" pStr
    creditEventTypeCovered         := ← opt j "creditEventTypeCovered" (pEnum creditEventTypeOf)
    coverageOfCreditEnhancement    := ← opt j "coverageOfCreditEnhancement" pFloat
    guaranteedExposure             := ← opt j "guaranteedExposure" (pEnum guaranteedExposureOf) }

/-- Decode a `terms` object given as a raw JSON string. -/
def termsFromString (s : String) : Except String (Terms Float) := do
  termsFromJson (← Json.parse s)

-- ---------------------------------------------------------------------------
-- Risk-factor environment from `dataObserved`
-- ---------------------------------------------------------------------------

def eventTypeOf : String → Except String EventType := enum "eventType"
  [("AD", .AD), ("IED", .IED), ("FP", .FP), ("PR", .PR), ("PD", .PD),
   ("PRD", .PRD), ("TD", .TD), ("IP", .IP), ("IPCI", .IPCI), ("IPCB", .IPCB),
   ("RR", .RR), ("RRF", .RRF), ("DV", .DV), ("PRF", .PRF), ("PY", .PY),
   ("PP", .PP), ("CD", .CD), ("STD", .STD), ("MD", .MD), ("XD", .XD),
   ("SC", .SC), ("CE", .CE), ("PI", .PI), ("IPFX", .IPFX), ("IPFL", .IPFL)]

/-- A single observed market series: `(marketObjectCode, [(time, value)])`. -/
private def parseSeries (j : Json) : Except String (List (String × List (Time × Float))) :=
  match field? j "dataObserved" with
  | none => .ok []
  | some (.obj kvs) =>
    kvs.toList.mapM fun kv => do
      let data ← (kv.2.getObjVal? "data") >>= Json.getArr?
      let obs ← data.toList.mapM fun e => do
        let t ← reqAny e ["timestamp", "time"] pDate
        let v ← reqAny e ["value"] pFloat
        pure (Actus.Contract.Execution.toTime t, v)
      pure (kv.1, obs)
  | some _ => .error "dataObserved must be an object"

/-- Observed credit events from `eventsObserved`: the `(time, contractId,
    performanceState)` triples of every `type == "CE"` entry.  The state string
    (e.g. `"DF"`) is taken from `states.contractPerformance` (drives CEG/CEC). -/
private def parseCreditEvents (j : Json) : Except String (List (Time × String × String)) :=
  match field? j "eventsObserved" with
  | none => .ok []
  | some v =>
    match v.getArr? with
    | .error _ => .ok []
    | .ok arr  => do
      let evs ← arr.toList.mapM fun e => do
        let ty  ← (optAny e ["type", "eventType"] pStr)
        match ty with
        | some "CE" =>
          let t   ← reqAny e ["time", "eventDate"] pDate
          let cid ← (optAny e ["contractId", "contractIdentifier"] pStr)
          let st  ← match field? e "states" with
            | some s => (optAny s ["contractPerformance"] pStr)
            | none   => pure none
          pure (some (Actus.Contract.Execution.toTime t, cid.getD "", st.getD ""))
        | _ => pure none
      pure (evs.filterMap id)

/-- Observed exercise time from `eventsObserved`: the latest `XD` event time, if
    any (closes an open-maturity CLM "call"). -/
private def parseExerciseDate (j : Json) : Except String (Option Time) :=
  match field? j "eventsObserved" with
  | none => .ok none
  | some v =>
    match v.getArr? with
    | .error _ => .ok none
    | .ok arr  => do
      let ts ← arr.toList.mapM fun e => do
        let ty ← (optAny e ["type", "eventType"] pStr)
        match ty with
        | some "XD" => do
          let t ← reqAny e ["time", "eventDate"] pDate
          pure (some (Actus.Contract.Execution.toTime t))
        | _ => pure none
      pure ((ts.filterMap id).foldl (fun acc t => max acc t) 0
              |> (fun m => if m == 0 then none else some m))

/-- Step interpolation: the latest observation with `time ≤ t`. -/
private def stepLookup (obs : List (Time × Float)) (t : Time) : Float :=
  match (obs.filter (·.1 ≤ t)).reverse.head? with
  | some p => p.2
  | none   => (obs.head?.map (·.2)).getD 0.0

/-- Build a `RiskFactorEnv` from a test case's `dataObserved`, wiring the
    rate-reset market series (`Oʳᶠ(RRMO,·)`).  Settlement-currency factor is
    `1` (single-currency reference cases); prepayment/annuity default to none. -/
def riskFactorsFromJson (j : Json) (ct : Terms Float) : Except String (RiskFactorEnv Float) := do
  let series ← parseSeries j
  let creditEvents ← parseCreditEvents j
  let exerciseDate ← parseExerciseDate j
  let lookup := fun (moc : Option String) =>
    match moc with
    | some m => ((series.find? (·.1 == m)).map (·.2)).getD []
    | none   => []
  -- detect the `23:59:59` end-of-day marker on the maturity/termination terms
  let termsJ := (j.getObjVal? "terms").toOption
  let eodOf := fun (k : String) =>
    match termsJ.bind (fun t => (t.getObjVal? k).toOption) with
    | some (.str s) => isEndOfDay s
    | _             => false
  pure { marketRate     := stepLookup (lookup ct.marketObjectCodeOfRateReset)
         scalingIndex   := stepLookup (lookup ct.marketObjectCodeOfScalingIndex)
         -- MOC-indexed rate lookup (composite legs resolve their own series)
         marketRateOf   := fun m => stepLookup (lookup (some m))
         -- observed dividend stream (STK): the (date, amount) pairs of its series
         dividends      := lookup ct.marketObjectCodeOfDividends
         creditEvents   := creditEvents
         exerciseDate   := exerciseDate
         maturityEOD    := eodOf "maturityDate" || eodOf "amortizationDate"
         terminationEOD := eodOf "terminationDate"
         purchaseEOD    := eodOf "purchaseDate" }

-- ---------------------------------------------------------------------------
-- Test-case wrapper
-- ---------------------------------------------------------------------------

/-- One expected event from `eventsObserved`. -/
structure ObservedEvent where
  type   : EventType
  time   : LocalTime
  payoff : Float
  deriving Repr

/-- One `actus-tests` entry. -/
structure TestCase where
  identifier : String
  terms      : Terms Float
  horizon    : Option LocalTime
  events     : List ObservedEvent

private def observedEventFromJson (j : Json) : Except String ObservedEvent := do
  pure {
    type   := ← reqAny j ["eventType", "type"] (pEnum eventTypeOf)
    time   := ← reqAny j ["eventDate", "time"] (fun v => do parseDateRoll (← v.getStr?))
    payoff := (← optAny j ["payoff"] pFloat).getD 0.0 }

/-- Decode one test entry: its `terms`, horizon `to`, and expected events
    (`results`, falling back to `eventsObserved`). -/
def testCaseFromJson (j : Json) : Except String TestCase := do
  let events ←
    match fieldAny? j ["results", "eventsObserved"] with
    | none   => pure []
    | some e => do (← e.getArr?).toList.mapM observedEventFromJson
  pure {
    identifier := (← opt j "identifier" pStr).getD ""
    terms      := ← req j "terms" termsFromJson
    horizon    := ← opt j "to" pDate
    events     := events }

/-- Decode a whole `actus-tests` file: a JSON object keyed by test id. -/
def testFileFromJson (j : Json) : Except String (List (String × TestCase)) :=
  match j with
  | .obj kvs => kvs.toList.mapM fun kv => do pure (kv.1, ← testCaseFromJson kv.2)
  | _        => .error "expected a JSON object keyed by test id"

/-- Decode a whole `actus-tests` file given as a raw JSON string. -/
def testFileFromString (s : String) : Except String (List (String × TestCase)) := do
  testFileFromJson (← Json.parse s)

-- ---------------------------------------------------------------------------
-- Contract dispatch
-- ---------------------------------------------------------------------------

/-- Run the lending engine appropriate to the parsed `contractType`.  Returns
    `[]` for contract types outside the implemented lending family. -/
def cashflowsOf (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  match ct.contractType with
  | .PAM => Actus.Contract.Execution.pamCashflows ct rf
  | .LAM => Actus.Contract.Execution.lamCashflows ct rf
  | .NAM => Actus.Contract.Execution.namCashflows ct rf
  | .ANN => Actus.Contract.Execution.annCashflows ct rf
  | .CLM => Actus.Contract.Execution.clmCashflows ct rf
  | .SWAPS => Actus.Contract.Execution.swapsCashflows ct rf
  | .COM => Actus.Contract.Execution.comCashflows ct rf
  | .STK => Actus.Contract.Execution.stkCashflows ct rf
  | .OPTNS => Actus.Contract.Execution.optnsCashflows ct rf
  | .FUTUR => Actus.Contract.Execution.futurCashflows ct rf
  | .FXOUT => Actus.Contract.Execution.fxoutCashflows ct rf
  | .SWPPV => Actus.Contract.Execution.swppvCashflows ct rf
  | .UMP => Actus.Contract.Execution.umpCashflows ct rf
  | .CAPFL => Actus.Contract.Execution.capflCashflows ct rf
  | .LAX => Actus.Contract.Execution.laxCashflows ct rf
  | .CEG => Actus.Contract.Execution.cegCashflows ct rf
  | .CEC => Actus.Contract.Execution.cecCashflows ct rf
  | .CSH => []   -- cash: a position with no scheduled cash flows (AD only, payoff 0)

/-- Parse a test case and compute its cashflows under its own observed risk
    factors — the full file → cashflows pipeline. -/
def cashflowsOfTestCase (tc : TestCase) (raw : Json) : Except String Cashflows := do
  let rf ← riskFactorsFromJson raw tc.terms
  pure (cashflowsOf tc.terms rf)

end Actus.IO.Parse
