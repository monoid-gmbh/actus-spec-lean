/-
## Parser test

Parses an `actus-tests`-shaped PAM entry (3-month bullet loan, monthly interest)
and runs it through the lending engine, alongside the file's expected events.
-/

import Actus.IO.Parse

namespace Actus.IO.Test

open Actus.Protocol
open Actus.Contract
open Actus.IO.Parse

/-- A reference-style test file: one PAM contract keyed by `"pam01"`. -/
def pam01 : String :=
  "{\"pam01\":{\"identifier\":\"pam01\",\"terms\":{" ++
    "\"contractType\":\"PAM\",\"contractID\":\"pam01\"," ++
    "\"statusDate\":\"2015-01-01T00:00:00\",\"contractRole\":\"RPA\"," ++
    "\"dayCountConvention\":\"30E360\",\"currency\":\"USD\"," ++
    "\"initialExchangeDate\":\"2015-01-02T00:00:00\"," ++
    "\"maturityDate\":\"2015-04-02T00:00:00\",\"premiumDiscountAtIED\":\"0\"," ++
    "\"notionalPrincipal\":\"1000\",\"nominalInterestRate\":\"0.05\"," ++
    "\"cycleAnchorDateOfInterestPayment\":\"2015-01-02T00:00:00\"," ++
    "\"cycleOfInterestPayment\":\"P1ML0\"," ++
    "\"endOfMonthConvention\":\"SD\",\"businessDayConvention\":\"NULL\",\"calendar\":\"NC\"}," ++
    "\"to\":\"2015-04-02T00:00:00\",\"dataObserved\":{}," ++
    "\"eventsObserved\":[" ++
      "{\"type\":\"IED\",\"time\":\"2015-01-02T00:00:00\",\"payoff\":-1000.0}," ++
      "{\"type\":\"IP\",\"time\":\"2015-02-02T00:00:00\",\"payoff\":4.166667}," ++
      "{\"type\":\"IP\",\"time\":\"2015-03-02T00:00:00\",\"payoff\":4.166667}," ++
      "{\"type\":\"IP\",\"time\":\"2015-04-02T00:00:00\",\"payoff\":4.166667}," ++
      "{\"type\":\"MD\",\"time\":\"2015-04-02T00:00:00\",\"payoff\":1000.0}]}}"

/-- Parsing succeeds and recognizes a PAM contract. -/
example :
    (termsFromString
      "{\"contractType\":\"PAM\",\"contractRole\":\"RPA\",\"statusDate\":\"2015-01-01T00:00:00\"}"
    ).toOption.map (·.contractType) = some .PAM := by native_decide

/-- An unknown role code is rejected with an informative error. -/
example :
    (termsFromString
      "{\"contractType\":\"PAM\",\"contractRole\":\"ZZZ\",\"statusDate\":\"2015-01-01T00:00:00\"}"
    ).toOption = none := by native_decide

-- Parsed contract summary: id, notional, and the file's expected events.
#eval (testFileFromString pam01).toOption.map
  (·.map fun (id, tc) =>
    (id, tc.terms.notionalPrincipal,
     tc.events.map fun (e : ObservedEvent) => (e.type, e.payoff)))

-- The cashflows our engine computes for the parsed contract.
#eval (testFileFromString pam01).toOption.map
  (·.map fun (id, tc) => (id, cashflowsOf tc.terms .id))

end Actus.IO.Test
