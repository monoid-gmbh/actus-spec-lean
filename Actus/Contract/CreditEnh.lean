/- ## Credit enhancement: CEG (guarantee) and CEC (collateral) over covered
   contracts; pay out on a covered contract's observed credit event. -/

import Actus.Contract.Engine
import Actus.Contract.Lending

namespace Actus.Contract.Execution

open Actus.Protocol
open Actus.Util
open Actus.Contract

/-- Final state of a covered child contract after running its own events
    *strictly before* time `te` — used to read its outstanding notional and
    accrued interest for the credit-enhancement exposure.  `none` for types the
    lending engine does not run. -/
def legStateBefore (child : Terms Float) (rf : RiskFactorEnv Float) (te : Time) :
    Option (State Float) :=
  let rf     := { rf with yf := fun a b => yf child a b }
  let before := fun (sched : Schedule) => sched.filter (fun e => Nat.blt e.1 te)
  match child.contractType with
  | .PAM => some (Execution.finalState (PAM.stf child rf)
      (PAM.init child (mdTime child) (sdTime child))
      (before (genSchedule child false rf.maturityEOD rf.terminationEOD)))
  | .LAM => some (Execution.finalState (LAM.stf child rf) (lamInit child)
      (before (genSchedule child true rf.maturityEOD rf.terminationEOD)))
  | .NAM => some (Execution.finalState (NAM.stf child rf)
      (NAM.init child (mdTime child) (sdTime child))
      (before (genSchedule child true rf.maturityEOD rf.terminationEOD)))
  | .ANN => some (Execution.finalState (ANN.stf child rf) (annInit child rf)
      (before (genSchedule child true rf.maturityEOD rf.terminationEOD)))
  | _    => none

/-- Exposure of one covered contract at credit-event time `te`: its outstanding
    notional, plus accrued interest when `withInterest` (guaranteed exposure
    `NI`).  Accrual extends from the contract's last status date to `te`. -/
def legExposure (child : Terms Float) (rf : RiskFactorEnv Float) (te : Time)
    (withInterest : Bool) : Float :=
  match legStateBefore child rf te with
  | none   => 0
  | some s =>
    let nt   := Float.abs s.nt
    let accr := Float.abs (s.ipac + s.nt * s.ipnr * yf child s.sd te)
    nt + (if withInterest then accr else 0)

/-- Credit enhancement (CEG guarantee / CEC collateral).  Pays a premium `PRD`
    at purchase; on a covered (`COVE`) contract's credit event matching
    `creditEventTypeCovered` it settles the covered exposure — `XD` (0) at the
    event date and `STD = sign · coverage · exposure` at event + settlementPeriod
    (BDC-shifted).  For collateral (`collateral = true`) the payout is capped at
    the observed value of the covering (`COVI`) object.  With no matching event
    it closes with a zero `MD` at maturity (its own, else the covered maturity). -/
def creditEnhancementCashflows (collateral : Bool) (ct : Terms Float)
    (rf : RiskFactorEnv Float) : Cashflows :=
  let legs := ct.contractStructure.getD []
  let s    := Conventions.sign (α := Float) ct.contractRole
  let covered : List (Terms Float) := legs.filterMap fun
    | .mk (.referenceTerms child) .COVE _ => some child
    | _                                    => none
  let coveredIds : List String := legs.filterMap fun
    | .mk (.referenceTerms child) .COVE _ => some child.contractId
    | .mk (.referenceId cid)      .COVE _ => some cid
    | _                                    => none
  -- covering (COVI) object: (market-object code, quantity) for the value cap
  let coviMoc : Option (String × Float) := legs.findSome? fun
    | .mk (.referenceTerms child) .COVI _ =>
        child.marketObjectCodeRef.map (fun m => (m, child.quantity.getD 1))
    | _ => none
  -- maturity for the no-event close & the trigger window: the contract's own,
  -- else the latest covered-contract maturity
  let coveredMatDate : Option LocalTime :=
    covered.filterMap (·.maturityDate) |>.foldl (fun acc d =>
      match acc with
      | some a => if Nat.blt (toTime a) (toTime d) then some d else some a
      | none   => some d) none
  let matDate : Option LocalTime := ct.maturityDate.orElse fun _ => coveredMatDate
  let matT    : Option Time      := matDate.map toTime
  let prd := (ct.purchaseDate.map fun d =>
                [((toTime d, EventType.PRD), -s * Terms.pprd ct)]).getD []
  let cetcStr := match ct.creditEventTypeCovered with
    | some .CETC_DF => "DF" | some .CETC_DQ => "DQ" | some .CETC_DL => "DL" | none => ""
  let trigger := rf.creditEvents.find? fun (te, cid, st) =>
    coveredIds.contains cid && st == cetcStr &&
      (match matT with | some m => Nat.ble te m | none => true)
  let body := match trigger with
    | some (te, _, _) =>
      let withInterest := match ct.guaranteedExposure with | some .CEGE_NI => true | _ => false
      let exposure :=
        if covered.isEmpty then Terms.nt ct                  -- CID ref: own notional
        else (covered.map (fun c => legExposure c rf te withInterest)).foldl (·+·) 0
      let cov     := ct.coverageOfCreditEnhancement.getD 1
      let payout0 := cov * exposure
      let payout  := if collateral then
          match coviMoc with
          | some (m, q) => min payout0 (rf.marketRateOf m te * q)
          | none        => payout0
        else payout0
      let stdT := match ct.settlementPeriod with
        | some c => toTime (bdcShift ct.scheduleConfig
                     (Date.addPeriod (Date.ofEpochDay te) c.n c.period))
        | none   => te
      [((te, EventType.XD), (0 : Float)), ((stdT, EventType.STD), s * payout)]
    | none => (matT.map fun m => [((m, EventType.MD), (0 : Float))]).getD []
  -- absolute-basis fees: `FP = sign · feeRate` at fee-cycle dates before close
  let fees := match ct.feeRate, ct.cycleAnchorDateOfFee with
    | some fr, some _ =>
      let upper := match trigger with | some (te, _, _) => te | none => matT.getD 0
      let feeDates := (cyclicTimes ct.scheduleConfig ct.cycleAnchorDateOfFee ct.cycleOfFee
         ct.cycleAnchorDateOfFee matDate false).filter (fun t => Nat.blt t upper)
      feeDates.map (fun t =>
        ((toTime (bdcShift ct.scheduleConfig (Date.ofEpochDay (Int.ofNat t))),
          EventType.FP), s * fr))
    | _, _ => []
  let sdT := toTime ct.statusDate
  sortCF ((prd ++ fees ++ body).filter (fun c => Nat.ble sdT c.1.1))

def cegCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  creditEnhancementCashflows false ct rf

def cecCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  creditEnhancementCashflows true ct rf

end Actus.Contract.Execution
