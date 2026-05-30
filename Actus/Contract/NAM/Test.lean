/-
## NAM Test

A negative amortizer: the fixed instalment covers interest first, only the
remainder reduces principal.  Same terms as the LAM example, but redemption is
interest-first, so the principal balance falls more slowly.
-/

import Actus.Contract.Lending.Common
import Actus.Contract.Lending.Execution
import Actus.Contract.NAM

namespace Actus.Contract.NAM.Test

open Actus.Protocol
open Actus.Contract.Lending

def nam : Terms :=
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

/-- The NAM redemption applies the instalment interest-first: the principal
    reduction is `Prnxt − Ipac_{t+}`. -/
theorem pr_principal_portion (t : Time) (s : State) :
    (NAM.stf_PR nam t s).nt = s.nt - LAM.redeemed s.nt (s.prnxt - LAM.ipacAccrIpcb nam t s) := rfl

#eval Lending.Execution.namCashflows nam .id

end Actus.Contract.NAM.Test
