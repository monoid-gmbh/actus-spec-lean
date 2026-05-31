/-
## ANN Test

An annuity loan: constant total instalments.  The instalment `Prnxt` is given
up front here; on a rate reset it would be recomputed from the Annuity Amount
function `A` (§3.8) using the remaining-period year fractions in
`RiskFactorEnv.annuityYfs`.
-/

import Actus.Contract.Common
import Actus.Contract.Execution
import Actus.Contract.ANN

namespace Actus.Contract.ANN.Test

open Actus.Protocol
open Actus.Contract

def ann : Terms Float :=
  { defaultTerms with
    contractRole                         := .CR_RPA
    notionalPrincipal                    := some 1000.0
    nominalInterestRate                  := some 0.1
    nextPrincipalRedemptionPayment       := some 260.0
    interestCalculationBase              := some .IPCB_NT
    dayCountConvention                   := some .DCC_A_360
    initialExchangeDate                  := some { day := 1, month := 1, year := 2020 }
    maturityDate                         := some { day := 1, month := 1, year := 2021 }
    cycleOfInterestPayment               := some { n := 3, period := "M", stub := false }
    cycleOfPrincipalRedemption           := some { n := 3, period := "M", stub := false } }

/-- A rate reset recomputes the next instalment as the annuity amount over the
    environment's remaining-period year fractions. -/
theorem rr_sets_annuity (rf : RiskFactorEnv Float) (t : Time) (s : State Float) :
    (ANN.stf_RR ann rf t s).prnxt =
      ANN.annuityAmount rf t (ANN.stf_RR ann rf t s).nt
        (LAM.ipacAccrIpcb rf t s) (ANN.stf_RR ann rf t s).ipnr := rfl

#eval Execution.annCashflows ann .id

end Actus.Contract.ANN.Test
