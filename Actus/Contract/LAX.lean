/- ## LAX: exotic amortizer with piecewise (array) principal/interest schedules. -/

import Actus.Contract.Engine

namespace Actus.Contract.Execution

open Actus.Protocol
open Actus.Util
open Actus.Contract

/-- Indexed lookup with a default. -/
def getI {α : Type} (l : List α) (i : Nat) (d : α) : α := (l[i]?).getD d

/-- LAX — an exotic amortizer whose principal-redemption and interest schedules
    are given piecewise by *array* attributes.  Each principal segment redeems
    (`DEC` → `PR`) or draws (`INC` → `PI`) its own amount on its own cycle; the
    notional accrues interest (`IP`) the LAM way, capitalised across redemptions;
    the contract matures (`MD`, paying the residual notional) at the explicit
    `maturityDate` or when the final segment exhausts the notional.  Rate resets
    come from the `arrayRate`/`arrayFixedVariable` arrays (`FIX` → `RRF` to the
    given rate, `VAR` → `RR` to the market rate). -/
def laxCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }
  match ct.initialExchangeDate with
  | none     => []
  | some ied =>
    let sgn  := Conventions.sign (α := Float) ct.contractRole
    let n    := Terms.nt ct
    let cfg  := ct.scheduleConfig
    let rate0 := Terms.ipnr ct
    let iedT := toTime ied
    -- principal segments
    let prAnchors := ct.arrayCycleAnchorDateOfPrincipalRedemption.getD []
    let prCycles  := ct.arrayCycleOfPrincipalRedemption.getD []
    let prAmts    := ct.arrayNextPrincipalRedemptionPayment.getD []
    let prDirs    := ct.arrayIncreaseDecrease.getD []
    let nseg := prAnchors.length
    -- build principal events (date, isInc, amount); thread the running notional
    -- so the last `DEC` segment can derive maturity by notional exhaustion.
    let rec buildPrin (i : Nat) (run : Float) :
        List (Time × Bool × Float) × Option LocalTime :=
      if h : i < nseg then
        let anchor := getI prAnchors i ied
        let cyc    := getI prCycles i none
        let amt    := getI prAmts i 0
        let isInc  := getI prDirs i "DEC" == "INC"
        let isLast := i + 1 == nseg
        if isLast then
          -- last segment: end at the explicit maturity, else exhaust notional
          match ct.maturityDate with
          | some md =>
            let dates := Schedule.schedule cfg anchor cyc md false
            (dates.map (fun d => (toTime d, isInc, amt)), some md)
          | none =>
            -- number of redemptions to clear the notional (≥1)
            let k := if isInc || amt == 0 then 1
                     else max 1 (Float.toUInt64 (Float.ceil (run / amt))).toNat
            let dates := (List.range k).map (fun j =>
              match cyc with
              | some c => Date.addPeriod anchor (j * c.n) c.period
              | none   => anchor)
            (dates.map (fun d => (toTime d, isInc, amt)), dates.getLast?)
        else
          let nextA := getI prAnchors (i+1) ied
          let dates := Schedule.schedule cfg anchor cyc nextA false
          let run'  := dates.foldl (fun r _ => if isInc then r + amt else r - amt) run
          let (rest, mat) := buildPrin (i+1) run'
          (dates.map (fun d => (toTime d, isInc, amt)) ++ rest, mat)
      else ([], none)
    let (prinRaw, matDateOpt) := buildPrin 0 n
    let matDate := matDateOpt.getD ied
    let matT    := toTime matDate
    -- principal events: the redemption coinciding with maturity becomes `MD`
    let prin : List (Time × EventType × Float) := prinRaw.map fun (t, isInc, amt) =>
      if t == matT then (t, EventType.MD, amt)
      else if isInc then (t, EventType.PI, amt) else (t, EventType.PR, amt)
    let prin := if prin.any (fun e => e.1 == matT && eventTypePriority e.2.1 == eventTypePriority .MD)
                then prin else prin ++ [(matT, EventType.MD, 0)]
    -- interest events (array schedule up to & including maturity)
    let ipAnchors := ct.arrayCycleAnchorDateOfInterestPayment.getD []
    let ipCycles  := ct.arrayCycleOfInterestPayment.getD []
    let ipPairs   := (List.range ipAnchors.length).map fun i =>
      (getI ipAnchors i ied, getI ipCycles i none)
    let ipDates := (Schedule.arraySchedule cfg ipPairs matDate).map toTime
    let ipEv : List (Time × EventType × Float) :=
      (ipDates.filter (fun t => Nat.blt iedT t)).map (fun t => (t, EventType.IP, 0))
    -- rate resets from the rate arrays
    let rrAnchors := ct.arrayCycleAnchorDateOfRateReset.getD []
    let rrRates   := ct.arrayRate.getD []
    let rrFixVar  := ct.arrayFixedVariable.getD []
    let rrEv : List (Time × EventType × Float) := (List.range rrAnchors.length).map fun i =>
      let t   := toTime (getI rrAnchors i ied)
      let fix := getI rrFixVar i "FIX" == "FIX"
      -- FIX: the array rate is the new fixed rate.  VAR: it is the spread over
      -- the observed market rate.
      if fix then (t, EventType.RRF, getI rrRates i rate0)
      else (t, EventType.RR, rf.marketRate t * Terms.rrmlt ct + getI rrRates i 0)
    -- IED + everything, sorted by (time, priority)
    let iedEv : Time × EventType × Float := (iedT, EventType.IED, 0)
    let evs := (iedEv :: prin ++ ipEv ++ rrEv)
    let evs := evs.toArray.qsort (fun a b =>
      if a.1 == b.1 then Nat.blt (eventTypePriority a.2.1) (eventTypePriority b.2.1)
      else Nat.blt a.1 b.1) |>.toList
    -- fold the LAX state machine: nt signed, ipac accrued, ipnr rate, sd status
    let step := fun (st : Float × Float × Float × Time) (e : Time × EventType × Float) =>
      let (nt, ipac, ipnr, sd) := st
      let t := e.1
      let accr := ipac + nt * ipnr * rf.yf sd t   -- accrued interest up to t
      let prem := ct.premiumDiscountAtIED.getD 0
      match e.2.1 with
      | .IED => ((sgn * n, 0, rate0, t), ((t, EventType.IED), -sgn * (n + prem)))
      | .IP  => ((nt, 0, ipnr, t),       ((t, EventType.IP), accr))
      | .PR  => ((nt - sgn * e.2.2, accr, ipnr, t), ((t, EventType.PR), sgn * e.2.2))
      | .PI  => ((nt + sgn * e.2.2, accr, ipnr, t), ((t, EventType.PI), -sgn * e.2.2))
      | .MD  => ((0, accr, ipnr, t),     ((t, EventType.MD), nt))
      | .RRF => ((nt, accr, e.2.2, t),   ((t, EventType.RRF), 0))
      | .RR  => ((nt, accr, e.2.2, t),   ((t, EventType.RR), 0))
      | _    => ((nt, accr, ipnr, t),    ((t, e.2.1), 0))
    let flows := (evs.foldl (fun (acc : (Float × Float × Float × Time) × Cashflows) e =>
      let (st', cf) := step acc.1 e
      (st', acc.2 ++ [cf])) ((sgn * n, 0, rate0, iedT), [])).2
    let sdT := toTime ct.statusDate
    sortCF (flows.filter (fun c => Nat.ble sdT c.1.1))

end Actus.Contract.Execution
