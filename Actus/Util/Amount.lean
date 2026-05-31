/-
## The `Amount` numeric interface

The lending engine is written **once**, generically, against the lawless
numeric operations bundled here, and then instantiated at two types:

* `Float` — the *executable* model (the conformance engine, the parser, the
  `#eval` traces).  IEEE-754: fast, but no usable algebraic laws (`NaN` breaks
  even `a ≤ a`), so no metatheorem about magnitudes can be proved over it.
* `ℝ`     — the *relational specification* and its metatheorems.  An exact,
  totally-ordered field (via Mathlib): the rate-cap/floor bounds, redemption
  non-overshoot and conservation are genuine theorems here.

`Amount` carries only **operations**, no axioms — which is exactly why both
`Float` and `ℝ` are instances.  The *laws* live in `ℝ`'s Mathlib structure and
are used directly in `Actus.Contract.Lending.Properties`; `Float` is (correctly)
*not* expected to satisfy them.
-/

import Mathlib.Data.Real.Basic

namespace Actus

/-- Lawless numeric operations shared by the executable (`Float`) and the
    specification (`ℝ`) amount types.  Definitions of the lending engine take
    `[Amount α]`; instantiate at `Float` to run and at `ℝ` to prove. -/
class Amount (α : Type) extends
    Zero α, One α, Add α, Sub α, Mul α, Div α, Neg α, Min α, Max α, LE α where
  /-- Absolute value (magnitude). -/
  abs : α → α

/-- Executable instance: native IEEE-754 `Float`. -/
instance : Amount Float where
  abs := Float.abs

/-- Specification instance: the real numbers.  Noncomputable (so it never leaks
    into the executable engine), with `abs` the Mathlib absolute value, so that
    `Amount.abs (x : ℝ) = |x|` definitionally and the order lemmas apply. -/
noncomputable instance : Amount ℝ where
  abs := abs

@[simp] theorem Amount.abs_real (x : ℝ) : Amount.abs x = |x| := rfl

end Actus
