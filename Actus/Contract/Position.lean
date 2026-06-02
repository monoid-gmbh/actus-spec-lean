/- ## Position contracts: COM (commodity), STK (stock).  (CSH has no scheduled
   cash flows — handled inline in the dispatcher.) -/

import Actus.Contract.Engine

namespace Actus.Contract.Execution

open Actus.Protocol
open Actus.Util
open Actus.Contract

/-- COM: a commodity position.  Purchase pays `−R·quantity·priceAtPurchase`;
    termination receives `R·quantity·priceAtTermination`. -/
def comCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let s   := Conventions.sign (α := Float) ct.contractRole
  let qty := ct.quantity.getD 0
  let tdRoll := if rf.terminationEOD then 1 else 0   -- 23:59:59 settles next midnight
  let prd := (ct.purchaseDate.map fun d =>
                [((toTime d, EventType.PRD), -s * qty * Terms.pprd ct)]).getD []
  let td  := (ct.terminationDate.map fun d =>
                [((toTime d + tdRoll, EventType.TD), s * qty * Terms.ptd ct)]).getD []
  let sdT := toTime ct.statusDate
  sortCF ((prd ++ td).filter (fun c => Nat.ble sdT c.1.1))

/-- STK: an equity position.  Purchase pays `−R·priceAtPurchase`; termination
    receives `R·priceAtTermination`; each observed dividend pays `R·amount`. -/
def stkCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let s   := Conventions.sign (α := Float) ct.contractRole
  let prd := (ct.purchaseDate.map fun d =>
                [((toTime d, EventType.PRD), -s * Terms.pprd ct)]).getD []
  let td  := (ct.terminationDate.map fun d =>
                [((toTime d + (if rf.terminationEOD then 1 else 0), EventType.TD), s * Terms.ptd ct)]).getD []
  let dv  := rf.dividends.map fun (t, v) =>
               ((toTime (bdcShift ct.scheduleConfig (Date.ofEpochDay t)), EventType.DV), s * v)
  let sdT := toTime ct.statusDate
  sortCF ((prd ++ dv ++ td).filter (fun c => Nat.ble sdT c.1.1))

end Actus.Contract.Execution
