/-
## Lending family execution wrappers (PAM/LAM/NAM/ANN/CLM)

Thin executable entry points that thread each stateful contract's `stf`/`pof`
(the relational+functional spec in `PAM`…`CLM`) over the generated schedule.
-/

import Actus.Contract.Engine
import Actus.Contract.PAM
import Actus.Contract.LAM
import Actus.Contract.NAM
import Actus.Contract.ANN
import Actus.Contract.CLM

namespace Actus.Contract.Execution

open Actus.Protocol
open Actus.Util
open Actus.Contract

def pamCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }   -- supply the day-count year fraction
  remapSettlement ct.scheduleConfig <| afterPurchase ct <|
    Execution.runSchedule (PAM.stf ct rf) (PAM.pof ct rf)
      (PAM.init ct (mdTime ct) (sdTime ct)) (genSchedule ct false rf.maturityEOD rf.terminationEOD)

/-- Initial LAM state.  Applies the contract-role sign to `Prnxt`, and when
    `PRNXT` is absent sizes the linear instalment as `NT / (#PR + 1)` (the `+1`
    for the maturity redemption). -/
def lamInit (ct : Terms Float) : State Float :=
  let s0   := LAM.init ct (mdTime ct) (sdTime ct)
  let base := match ct.nextPrincipalRedemptionPayment with
    | some _ => Terms.prnxt ct
    | none   => Terms.nt ct / Float.ofNat (numPR (genSchedule ct true) + 1)
  { s0 with prnxt := Conventions.sign (Terms.cntrl ct) * base }

def lamCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }
  remapSettlement ct.scheduleConfig <| afterPurchase ct <|
    Execution.runSchedule (LAM.stf ct rf) (LAM.pof ct rf)
      (lamInit ct) (genSchedule ct true rf.maturityEOD rf.terminationEOD)

def namCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }
  remapSettlement ct.scheduleConfig <| afterPurchase ct <|
    Execution.runSchedule (NAM.stf ct rf) (NAM.pof ct rf)
      (NAM.init ct (mdTime ct) (sdTime ct)) (genSchedule ct true rf.maturityEOD rf.terminationEOD)

/-- The annuity amortization horizon: the `amortizationDate` if given, else the
    maturity.  The instalment amortizes to here even when an earlier
    `maturityDate` ends the contract with a balloon. -/
def annHorizon (ct : Terms Float) : Option LocalTime :=
  ct.amortizationDate.orElse fun _ => maturityOf ct

def annHorizonT (ct : Terms Float) : Time := ((annHorizon ct).map toTime).getD (mdTime ct)

def annInit (ct : Terms Float) (rf : RiskFactorEnv Float) : State Float :=
  let s0 := ANN.init ct (mdTime ct) (sdTime ct)
  match ct.nextPrincipalRedemptionPayment with
  | some _ => s0
  | none =>
    let prTimes := cyclicTimes ct.scheduleConfig ct.cycleAnchorDateOfPrincipalRedemption
                     ct.cycleOfPrincipalRedemption ct.initialExchangeDate (annHorizon ct) false
    -- Notional at the start of redemption: run the events before the first PR
    -- (`IED`, any `IPCI` capitalizations) so the annuity amortizes the *grown*
    -- notional rather than `NT`.
    let sched   := genSchedule ct true
    let firstPR := ((sched.find? fun e => eventTypePriority e.2 == eventTypePriority .PR).map
                     (·.1)).getD (annHorizonT ct)
    let grown   := (sched.filter fun e => Nat.blt e.1 firstPR).foldl
      (fun s (e : Event) => ANN.stf ct rf e.2 e.1 s) s0
    -- the annuity's first period runs from one redemption cycle before the
    -- first redemption (PRANX − PRCL), but never before IED.
    let iedT  := (ct.initialExchangeDate.map toTime).getD (sdTime ct)
    let first := match ct.cycleAnchorDateOfPrincipalRedemption,
                       ct.cycleOfPrincipalRedemption with
      | some a, some c => Nat.max iedT (toTime (Date.subPeriod a c.n c.period))
      | _, _           => iedT
    -- the annuity amortizes to the horizon; an end-of-day amortization date
    -- extends the final period to the next midnight.
    let horizonT := annHorizonT ct + (if rf.maturityEOD then 1 else 0)
    let bounds := (first :: prTimes) ++ [horizonT]
    let yfs    := (bounds.zip bounds.tail).map fun p => yf ct p.1 p.2
    let a      := Conventions.sign (Terms.cntrl ct) *
                    Schedule.annuity (Float.abs grown.nt) (Float.abs grown.ipac) (Terms.ipnr ct) yfs
    { s0 with prnxt := a }

/-- ANN execution runner: like `runSchedule`, but after each rate reset
    (`RR`/`RRF`) it re-amortizes — recomputing `Prnxt` as the annuity over the
    *remaining* redemption schedule (the `PR` dates after the reset, then `MD`)
    at the new rate, so total instalments stay constant within each rate regime. -/
def annRun (ct : Terms Float) (rf : RiskFactorEnv Float) (mdT : Time) :
    State Float → Schedule → Cashflows
  | _, []             => []
  | s, (t, e) :: rest =>
    let cf : Cashflow := ((t, e), ANN.pof ct rf e t s)
    let s' := ANN.stf ct rf e t s
    let s'' :=
      if eventTypePriority e == eventTypePriority .RR
         || eventTypePriority e == eventTypePriority .RRF then
        let prRem := rest.filterMap fun ev =>
          if eventTypePriority ev.2 == eventTypePriority .PR then some ev.1 else none
        let bounds := (t :: prRem) ++ [mdT]
        let yfs    := (bounds.zip bounds.tail).map fun p => yf ct p.1 p.2
        -- amortize the *magnitude* then re-apply the contract-role sign (as in
        -- `annInit`); using the already-signed `s'.nt` would double the sign and
        -- flip `Prnxt` for a liability (RPL) leg.
        { s' with prnxt := Conventions.sign (Terms.cntrl ct) *
                    Schedule.annuity (Float.abs s'.nt) (Float.abs s'.ipac) s'.ipnr yfs }
      else s'
    cf :: annRun ct rf mdT s'' rest

def annCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }
  remapSettlement ct.scheduleConfig <| afterPurchase ct <|
    annRun ct rf (annHorizonT ct) (annInit ct rf) (genSchedule ct true rf.maturityEOD rf.terminationEOD)

/-- CLM event schedule for a defined-maturity contract: IED, interest-cycle
    `IPCI` strictly before MD, rate resets, then the final `IP` and `MD` at
    maturity. -/
def genScheduleCLM (ct : Terms Float) (mdOpt : Option LocalTime) (mEOD : Bool := false) :
    Schedule :=
  let cfg := ct.scheduleConfig
  let ied := ct.initialExchangeDate
  match mdOpt with
  | none        => []   -- no maturity and no observed exercise ⇒ nothing to settle
  | some mdDate =>
    let md  := some mdDate
    let mdT := toTime mdDate
    let single (d : Option LocalTime) (e : EventType) : List Event :=
      (d.map (fun x => [(toTime x, e)])).getD []
    -- interest-cycle points; those strictly before maturity capitalize (IPCI)
    let ipciEvents : List Event :=
      (cyclicTimes cfg ct.cycleAnchorDateOfInterestPayment ct.cycleOfInterestPayment ied md false
        |>.filter (fun t => Nat.blt t mdT)).map (fun t => (t, EventType.IPCI))
    -- rate resets strictly before maturity (first is RRF when RRNXT is set)
    let rrEvents : List Event :=
      let ts := (cyclicTimes cfg ct.cycleAnchorDateOfRateReset ct.cycleOfRateReset ied md false
        |>.filter (fun t => Nat.blt t mdT))
      match ct.nextResetRate, ts with
      | some _, first :: rest => (first, .RRF) :: rest.map (fun t => (t, .RR))
      | _,      _             => ts.map (fun t => (t, .RR))
    let events : List Event :=
      single ied .IED ++ ipciEvents ++ rrEvents ++ [(mdT, EventType.IP), (mdT, EventType.MD)]
    -- keep only events strictly after the status date (the initial exchange at
    -- the status date is historical — already reflected in the init state)
    let events := let sdT := toTime ct.statusDate; events.filter (fun (e : Event) => Nat.blt sdT e.1)
    -- end-of-day roll of the maturity events
    let events := if mEOD then events.map (fun e => if e.1 == mdT then (mdT + 1, e.2) else e) else events
    let lt := fun (a b : Event) =>
      if a.1 == b.1 then Nat.blt (eventTypePriority a.2) (eventTypePriority b.2)
      else Nat.blt a.1 b.1
    (events.toArray.qsort lt).toList

def clmCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }
  -- effective maturity: the explicit `maturityDate`, else the observed exercise
  -- (the `XD` "call" date `sup τ(Oᵉᵛ(CID))`, §7.6) for an open-maturity contract.
  let effMd : Option LocalTime := ct.maturityDate.orElse fun _ =>
    rf.exerciseDate.map (fun t => Date.ofEpochDay (Int.ofNat t))
  let isOpen := ct.maturityDate.isNone
  let mdT := (effMd.map toTime).getD (sdTime ct)
  let flows := Execution.runSchedule (CLM.stf ct rf) (CLM.pof ct rf)
      (CLM.init ct mdT (sdTime ct)) (genScheduleCLM ct effMd rf.maturityEOD)
  -- On a call, the `XD` exercise marker is stamped at the exercise date `mdT`,
  -- but settlement (`IP` accrued + `STD` of the grown notional) is deferred by the
  -- exercise-notice period `xDayNotice` (§7.6).  Capitalisation/accrual still stop
  -- at the exercise date — only the cash-flow timestamps move.
  let flows := if isOpen then
      let setlT := match effMd, ct.xDayNotice with
        | some d, some c => toTime (Date.addPeriod d c.n c.period)
        | _,      _      => mdT
      flows.map (fun cf =>
        if eventTypePriority cf.1.2 == eventTypePriority .MD then ((setlT, EventType.STD), cf.2)
        else if cf.1.1 == mdT && eventTypePriority cf.1.2 == eventTypePriority .IP
             then ((setlT, EventType.IP), cf.2) else cf)
        ++ [((mdT, EventType.XD), (0 : Float))]
    else flows
  let flows := (flows.toArray.qsort (fun a b =>
    if a.1.1 == b.1.1 then Nat.blt (eventTypePriority a.1.2) (eventTypePriority b.1.2)
    else Nat.blt a.1.1 b.1.1)).toList
  remapSettlement ct.scheduleConfig <| afterPurchase ct <| flows

end Actus.Contract.Execution
