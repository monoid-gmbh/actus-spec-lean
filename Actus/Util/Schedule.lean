/-
## Schedule generation (§3.1–3.2) and the Annuity Amount function (§3.8)

* `schedule` is the Schedule function `S(s, c, T, B)`: the sequence of cyclic
  event times from anchor `s` with cycle `c` up to end date `T`, with `B`
  controlling whether `T` itself belongs to the schedule.  EOM and BDC
  conventions are applied to every generated time via `applyConventions`.
* `arraySchedule` is the array-schedule generalisation `S̄(s⃗, c⃗)` (§3.2).
* `annuity` is the Annuity Amount function `A(s, T, n, a, r)` (§3.8) used to
  size the annuity payment of an `ANN` contract.

Generated calendar times are mapped onto the `Time := Nat` event axis with
`toTime` (serial day number, clamped at the 1970 epoch).
-/

import Actus.Protocol
import Actus.Util.Date
import Actus.Util.Conventions
import Actus.Util.Amount

namespace Actus.Util.Schedule

open Actus.Protocol
open Actus.Util.Date
open Actus.Util.Conventions
open Actus (Amount)

/-- Map a calendar date onto the `Time` axis (serial day number ≥ 0). -/
def toTime (d : LocalTime) : Time := (toEpochDay d).toNat

/-- Is this cycle measured in months or longer (so EOM can apply)? -/
private def cycleIsMonthly (c : Cycle) : Bool :=
  (monthsOfUnit c.period).isSome

/-- The `k`-th cyclic time, computed as `s + k·c` from the anchor (multiplying
    the period) rather than by iterating `addCycle`.  This matters for
    month/quarter/year cycles anchored near month end: e.g. from Jan-30 the
    sequence is Jan-30, Feb-28, Mar-30, … (the anchor day recovers in longer
    months), whereas iterating `addCycle` would drift down to Feb-28, Mar-28, …. -/
private def nth (s : LocalTime) (c : Cycle) (k : Nat) : LocalTime :=
  addPeriod s (k * c.n) c.period

/-- Raw cyclic times `s, s+c, s+2c, …` strictly before `t`. -/
private def rawTimes (s : LocalTime) (c : Cycle) (t : LocalTime) : List LocalTime :=
  let fuel := (toEpochDay t - toEpochDay s).toNat + 2
  let rec go (fuel k : Nat) (acc : List LocalTime) : List LocalTime :=
    match fuel with
    | 0 => acc.reverse
    | fuel + 1 =>
      let x := nth s c k
      if toEpochDay x ≥ toEpochDay t then acc.reverse
      else go fuel (k + 1) (x :: acc)
  go fuel 0 []

/-- Stub correction for a `T`-terminated cyclic schedule (§3.1).  When `T` is not
    on the cycle grid there is a final stub period `[lastInterior, T]`.  The
    cycle's stub flag decides its treatment (ACTUS codes: `L0` = **long** stub,
    `L1` = **short** stub; `parseCycle` records `c.stub = true` for `L1`):

    * short stub (`c.stub`): keep `lastInterior` — a short final period stands;
    * long stub (`!c.stub`): drop `lastInterior`, merging it into a long final
      period `[secondLastInterior, T]`.

    No correction when `T` is on the grid. -/
private def stubCorrect (s : LocalTime) (c : Cycle) (t : LocalTime)
    (body : List LocalTime) : List LocalTime :=
  if body.isEmpty then body
  else
    -- `t` is on the grid iff it equals the next anchored grid point `s + |body|·c`.
    let onGrid := toEpochDay (nth s c body.length) == toEpochDay t
    if !c.stub && !onGrid then body.dropLast else body

/-- Schedule function `S(s, c, T, B)` (§3.1).

    * `c = none` yields the two-point schedule `[s, T]`.
    * otherwise the cyclic times up to `T` are generated; when `includeEnd` (the
      boolean `B`) `T` is appended, applying long/short stub correction to the
      final period.
    Each time has the contract's EOM and BDC conventions applied. -/
def schedule (cfg : ScheduleConfig) (s : LocalTime) (c : Option Cycle)
    (t : LocalTime) (includeEnd : Bool := true) : List LocalTime :=
  match c with
  | none   => if includeEnd then [s, t] else [s]
  | some c =>
    -- conventions (EOM/BDC) apply to the cyclic times only; the end date `t`
    -- (the contract maturity) is appended as-is so it is not rolled past itself.
    let body := (stubCorrect s c t (rawTimes s c t)).map (applyConventions cfg s (cycleIsMonthly c))
    if includeEnd then body ++ [t] else body

/-- Array schedule `S̄(s⃗, c⃗)` (§3.2): concatenate `S(sᵢ, cᵢ, sᵢ₊₁)` over the
    successive anchor/cycle pairs, ending at `tEnd`. -/
def arraySchedule (cfg : ScheduleConfig)
    (anchors : List (LocalTime × Option Cycle)) (tEnd : LocalTime) : List LocalTime :=
  let rec go : List (LocalTime × Option Cycle) → List LocalTime
    | [] => []
    | [(s, c)] => schedule cfg s c tEnd true
    | (s, c) :: (s', c') :: rest =>
      schedule cfg s c s' false ++ go ((s', c') :: rest)
  go anchors

-- ---------------------------------------------------------------------------
-- Annuity Amount function  A(s, T, n, a, r)   (§3.8)
-- ---------------------------------------------------------------------------

/-- Annuity amount `A(s,T,n,a,r)` (§3.8): the constant total instalment that
    amortizes `n + a` over the payment periods whose year fractions are `yfs`
    (`Y(tᵢ, tᵢ₊₁)`), at rate `r`.  Computed as the present-value annuity

    `A = (n + a) / Σₖ ∏_{j ≤ k} (1 + r·yfⱼ)⁻¹`,

    i.e. `n + a` divided by the sum of discount factors — the formulation the
    ACTUS reference uses.  (`Σₖ` runs over the periods; the inner product is the
    discount factor to the end of period `k`.) -/
def annuity {α : Type} [Amount α] (n a r : α) (yfs : List α) : α :=
  let (_, sumDisc) :=
    yfs.foldl (fun (acc : α × α) y =>
      let prod := acc.1 * (1 + r * y)        -- ∏_{j ≤ k} (1 + r·yf_j)
      (prod, acc.2 + 1 / prod)) (1, 0)
  -- empty schedule ⇒ no discounting (denominator would be 0); otherwise the
  -- denominator is a sum of positive discount factors, so division is safe.
  if yfs.isEmpty then n + a else (n + a) / sumDisc

end Actus.Util.Schedule
