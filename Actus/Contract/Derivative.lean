/- ## Derivative contracts: OPTNS (option), FUTUR (future), FXOUT (FX outright),
   CAPFL (cap/floor) — cash-settled on an underlying. -/

import Actus.Contract.Engine

namespace Actus.Contract.Execution

open Actus.Protocol
open Actus.Util
open Actus.Contract

/-- OPTNS — a European, cash-settled option on an underlying.  Premium paid at
    `PRD`; at maturity the intrinsic value settles (`STD`): `max(S−K, 0)` for a
    call, `max(K−S, 0)` for a put, where `S` is the underlying's observed price
    (the `UDL` market-object code) at maturity and `K = optionStrike1`.  The
    zero-valued `MD`/`XD` markers are dropped by the cash filter. -/
def optnsCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let s   := Conventions.sign (α := Float) ct.contractRole
  let prd := (ct.purchaseDate.map fun d =>
                [((toTime d, EventType.PRD), -s * Terms.pprd ct)]).getD []
  let std := match ct.maturityDate with
    | none    => []
    | some md =>
      let mdT := toTime md
      let k   := ct.optionStrike1.getD 0
      let moc := (ct.contractStructure.getD []).findSome? fun
        | .mk (.referenceId m) .UDL _ => some m
        | _                            => none
      let sT  := match moc with | some m => rf.marketRateOf m mdT | none => 0
      let intrinsic := match ct.optionType with
        | some "P" => max (k - sT) 0      -- put
        | _        => max (sT - k) 0      -- call (default)
      -- settlement happens `settlementPeriod` after exercise/maturity
      let stdT := match ct.settlementPeriod with
        | some c => toTime (bdcShift ct.scheduleConfig (Date.addPeriod md c.n c.period))
        | none   => mdT
      [((stdT, EventType.STD), s * intrinsic)]
  let sdT := toTime ct.statusDate
  sortCF ((prd ++ std).filter (fun c => Nat.ble sdT c.1.1))

/-- FUTUR — a cash-settled future on an underlying.  Premium/price paid at
    `PRD`; at maturity the linear payoff settles (`STD`): `sign·(S − F)`, where
    `S` is the underlying's observed price (the `UDL` market-object code) at
    maturity and `F = futuresPrice`.  Like OPTNS but with a linear (not
    max-clamped) payoff; settlement honours `settlementPeriod` + the BDC. -/
def futurCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let s   := Conventions.sign (α := Float) ct.contractRole
  let prd := (ct.purchaseDate.map fun d =>
                [((toTime d, EventType.PRD), -s * Terms.pprd ct)]).getD []
  let std := match ct.maturityDate with
    | none    => []
    | some md =>
      let mdT := toTime md
      let f   := ct.futuresPrice.getD 0
      let moc := (ct.contractStructure.getD []).findSome? fun
        | .mk (.referenceId m) .UDL _ => some m
        | _                            => none
      let sT  := match moc with | some m => rf.marketRateOf m mdT | none => 0
      let stdT := match ct.settlementPeriod with
        | some c => toTime (bdcShift ct.scheduleConfig (Date.addPeriod md c.n c.period))
        | none   => mdT
      [((stdT, EventType.STD), s * (sT - f))]
  let sdT := toTime ct.statusDate
  sortCF ((prd ++ std).filter (fun c => Nat.ble sdT c.1.1))

/-- FXOUT — an FX outright (forward exchange of two currency notionals).
    *Delivery* (`deliverySettlement ≠ "S"`): at maturity exchange the two
    notionals — `MD` flows `sign·Nt1` and `−sign·Nt2`.  *Cash* (`"S"`): a single
    net `STD = sign·(Nt1 − fx·Nt2)` at maturity + `settlementPeriod`, where `fx`
    is the observed `currency2/currency` rate at maturity. -/
def fxoutCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  match ct.maturityDate with
  | none    => []
  | some md =>
    let s    := Conventions.sign (α := Float) ct.contractRole
    let mdT  := toTime md + (if rf.maturityEOD then 1 else 0)
    let nt1  := Terms.nt ct
    let nt2  := ct.notionalPrincipal2.getD 0
    let base := match ct.deliverySettlement with
      | some "S" =>
        let fxMOC := (ct.currency2.getD "") ++ "/" ++ (ct.currency.getD "")
        let rate  := rf.marketRateOf fxMOC (toTime md)
        -- settlement runs `settlementPeriod` after the (EOD-rolled) maturity
        let stdT  := match ct.settlementPeriod with
          | some c => toTime (bdcShift ct.scheduleConfig (Date.addPeriod (Date.ofEpochDay mdT) c.n c.period))
          | none   => mdT
        [((stdT, EventType.STD), s * (nt1 - rate * nt2))]
      | _ =>
        [((mdT, EventType.MD), s * nt1), ((mdT, EventType.MD), -s * nt2)]
    -- termination ends the contract early: drop the maturity exchange, settle TD
    -- (the termination price is received regardless of contract role)
    let flows := match ct.terminationDate with
      | some td => let tdT := toTime td + (if rf.terminationEOD then 1 else 0)
                   (base.filter (fun c => Nat.ble c.1.1 tdT)) ++ [((tdT, EventType.TD), Terms.ptd ct)]
      | none    => base
    -- purchase mid-life: drop pre-purchase flows, settle PRD
    let flows := match ct.purchaseDate with
      | some pd => let pT := toTime pd + (if rf.purchaseEOD then 1 else 0)
                   afterPurchase ct (((pT, EventType.PRD), -s * Terms.pprd ct) :: flows)
      | none    => flows
    let sdT := toTime ct.statusDate
    sortCF (flows.filter (fun c => Nat.ble sdT c.1.1))

/-- CAPFL — an interest-rate cap/floor on an underlying (`UDL`/`CNT` child PAM).
    For each of the underlying's interest periods `[t⁻, t]` it pays the rate
    excess over the cap plus the shortfall under the floor:
    `sign · N · Y(t⁻,t) · (max(rate−lifeCap, 0) + max(lifeFloor−rate, 0))`, where
    `rate` is the underlying's in-force reset — the latest rate reset strictly
    before `t`, falling back to the child's nominal rate when none precedes. -/
def capflCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  match ct.contractStructure.bind (·.findSome? fun
          | .mk (.referenceTerms child) .UDL _ => some child
          | _                                  => none) with
  | none       => []
  | some child =>
    match child.maturityDate with
    | none    => []
    | some md =>
      let rf      := { rf with yf := fun a b => yf child a b }
      let s       := Conventions.sign (α := Float) ct.contractRole
      let n       := Terms.nt child
      let cfg     := child.scheduleConfig
      let nominal := Terms.ipnr child
      let ipDates := cyclicTimes cfg child.cycleAnchorDateOfInterestPayment
                       child.cycleOfInterestPayment child.initialExchangeDate (some md) true
      -- rate-reset dates; the rate in force at `t` is the latest reset before `t`
      let rrDates := cyclicTimes cfg child.cycleAnchorDateOfRateReset
                       child.cycleOfRateReset child.initialExchangeDate (some md) false
      let moc     := child.marketObjectCodeOfRateReset
      let rateAt  := fun (t : Time) =>
        match (rrDates.filter (fun r => Nat.blt r t)).reverse.head? with
        | some r => match moc with | some m => rf.marketRateOf m r | none => nominal
        | none   => nominal
      let iedT    := toTime (child.initialExchangeDate.getD child.statusDate)
      let bounds  := iedT :: ipDates
      let flows := (bounds.zip ipDates).map fun p =>
        let r      := rateAt p.2
        let capX   := match ct.lifeCap   with | some c => max (r - c) 0 | none => 0
        let floorX := match ct.lifeFloor with | some f => max (f - r) 0 | none => 0
        ((p.2, EventType.IP), s * n * (capX + floorX) * rf.yf p.1 p.2)
      let sdT := toTime ct.statusDate
      sortCF (flows.filter (fun c => Nat.ble sdT c.1.1))

end Actus.Contract.Execution
