/- ## UMP: undefined-maturity profile (non-maturity deposit). -/

import Actus.Contract.Engine

namespace Actus.Contract.Execution

open Actus.Protocol
open Actus.Util
open Actus.Contract

/-- UMP — undefined-maturity profile (a non-maturity deposit / savings account).
    Principal is exchanged at `IED` (`−sign·N`); interest capitalizes (`IPCI`,
    no cash) on the interest cycle, compounding the notional `Nt ← Nt·(1+rate·Y)`.
    On termination, `TD` settles at the *agreed buy-back price* plus the interest
    accrued since the last capitalization: `sign·(PTD + Ipac)`, where
    `Ipac = Nt^cap·rate·Y(t^cap, t^TD)` on the capitalized notional (so with a
    negative rate the accrual reduces the price). -/
def umpCashflows (ct : Terms Float) (rf : RiskFactorEnv Float) : Cashflows :=
  let rf := { rf with yf := fun a b => yf ct a b }
  match ct.initialExchangeDate with
  | none     => []
  | some ied =>
    let s    := Conventions.sign (α := Float) ct.contractRole
    let n    := Terms.nt ct
    let rate := Terms.ipnr ct
    let cfg  := ct.scheduleConfig
    let iedT := toTime ied
    let iedCF : Cashflow := ((iedT, EventType.IED), -s * n)
    let tdCF := match ct.terminationDate with
      | none    => []
      | some td =>
        let tdT := toTime td + (if rf.terminationEOD then 1 else 0)
        let ipciDates := (cyclicTimes cfg ct.cycleAnchorDateOfInterestPayment
                            ct.cycleOfInterestPayment ct.initialExchangeDate (some td) false).filter
                            (fun t => Nat.blt iedT t && Nat.blt t tdT)
        -- notional capitalized up to the last `IPCI` before termination
        let bounds  := iedT :: ipciDates
        let grownCap := (bounds.zip ipciDates).foldl
                          (fun nt p => nt + nt * rate * rf.yf p.1 p.2) n
        let lastCap := (ipciDates.getLast?).getD iedT
        let ipac    := grownCap * rate * rf.yf lastCap tdT
        [((tdT, EventType.TD), s * (Terms.ptd ct + ipac))]
    let sdT := toTime ct.statusDate
    sortCF (([iedCF] ++ tdCF).filter (fun c => Nat.ble sdT c.1.1))

end Actus.Contract.Execution
