/-
## LAM Test

A linearly-amortizing loan: 1000 notional repaid in four quarterly principal
instalments of 250, with quarterly interest at 10%.  Demonstrates the `PR` and
`IPCB` machinery and the executable schedule pipeline.
-/

import Actus.Contract.Common
import Actus.Contract.Execution
import Actus.Contract.LAM
import Actus.Util.Conventions

namespace Actus.Contract.LAM.Test

open Actus.Protocol
open Actus.Contract
open Actus.Util.Conventions (sign)

def lam : Terms Float :=
  { defaultTerms with
    contractRole                         := .CR_RPA
    notionalPrincipal                    := some 1000.0
    nominalInterestRate                  := some 0.1
    nextPrincipalRedemptionPayment       := some 250.0
    interestCalculationBase              := some .IPCB_NT
    dayCountConvention                   := some .DCC_A_360
    initialExchangeDate                  := some { day := 1, month := 1, year := 2020 }
    maturityDate                         := some { day := 1, month := 1, year := 2021 }
    cycleOfInterestPayment               := some { n := 3, period := "M", stub := false }
    cycleOfPrincipalRedemption           := some { n := 3, period := "M", stub := false } }

/-- A principal-redemption step reduces the notional by the redeemed amount
    (the instalment capped at the remaining notional). -/
theorem pr_reduces_notional (rf : RiskFactorEnv Float) (t : Time) (s : State Float) :
    (LAM.stf_PR lam rf t s).nt = s.nt - LAM.redeemed s.nt s.prnxt := rfl

#eval Execution.genSchedule lam true
#eval Execution.lamCashflows lam .id

end Actus.Contract.LAM.Test
