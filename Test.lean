/-
## Test suite root

Worked examples with `rfl`-checked cash-flow theorems and `#eval` demonstrations.
This is a separate library target (`Test`) so the tests are still built by
`lake build` but are kept out of the documented `Actus` API surface.
-/

import Test.PAM
import Test.LAM
import Test.NAM
import Test.ANN
import Test.IO
