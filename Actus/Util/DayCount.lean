/-
## Year-Fraction Convention  (§3.6)

The year-fraction interface `Y : s, t, DCC → ℝ` returns the fraction of a year
between two dates `s ≤ t` under a day-count convention `DCC`.  The techspec
leaves the concrete `DCC` implementations to the user; here we give the standard
implementations for every `DayCountConvention` in `Actus.Protocol`.

This file replaces the placeholder `yearFraction` that previously lived in
`Actus.Protocol` (which always returned `0.0`).
-/

import Actus.Protocol
import Actus.Util.Date

namespace Actus.Util.DayCount

open Actus.Protocol
open Actus.Util.Date

/-- Actual day count between `s` and `t` (as a `Float`). -/
def actualDays (s t : LocalTime) : Float :=
  Float.ofInt (toEpochDay t - toEpochDay s)

/-- Days in calendar year `y` (366 if leap). -/
def daysInYear (y : Nat) : Float :=
  if isLeapYear y then 366.0 else 365.0

private def startOfYear (y : Nat) : LocalTime := { day := 1, month := 1, year := y }

/-- 30/360-style day count with European day clamping. -/
private def days30 (s t : LocalTime) : Float :=
  let d1 := min s.day 30
  let d2 := min t.day 30
  Float.ofNat (360 * (t.year - s.year)) +
    Float.ofInt (30 * ((t.month : Int) - (s.month : Int)) + ((d2 : Int) - (d1 : Int)))

/-- 30E/360-ISDA day clamping: month-end (incl. Feb) and the 31st map to 30. -/
private def clampISDA (d : LocalTime) : Nat :=
  if d.day == 31 || (d.month == 2 && isEndOfMonth d) then 30 else d.day
where
  isEndOfMonth (x : LocalTime) : Bool := x.day == daysInMonth x.year x.month

/-- Actual/Actual (ISDA): split the interval at calendar-year boundaries. -/
private def actAct (s t : LocalTime) : Float :=
  if s.year == t.year then
    actualDays s t / daysInYear s.year
  else
    let firstPart := actualDays s (startOfYear (s.year + 1)) / daysInYear s.year
    let lastPart  := actualDays (startOfYear t.year) t / daysInYear t.year
    let middle    := Float.ofNat (t.year - s.year - 1)
    firstPart + middle + lastPart

/-- Year fraction between `s` and `t` (assumes `s ≤ t`) under `dcc` (§3.6). -/
def yearFraction (dcc : DayCountConvention) (s t : LocalTime) : Float :=
  match dcc with
  | .DCC_A_360 => actualDays s t / 360.0
  | .DCC_A_365 => actualDays s t / 365.0
  | .DCC_A_AISDA => actAct s t
  | .DCC_E30_360 => days30 s t / 360.0
  | .DCC_E30_360ISDA =>
      let d1 := clampISDA s
      let d2 := clampISDA t
      (Float.ofNat (360 * (t.year - s.year)) +
        Float.ofInt (30 * ((t.month : Int) - (s.month : Int)) + ((d2 : Int) - (d1 : Int)))) / 360.0
  | .DCC_B_252 =>
      -- Business/252: count Mon–Fri days in (s, t].
      let rec go (fuel : Nat) (cur : Int) (acc : Float) : Float :=
        match fuel with
        | 0 => acc
        | fuel + 1 =>
          if cur > toEpochDay t then acc
          else
            let w := (if cur >= -4 then (cur + 4) % 7 else (cur + 5) % 7 + 6)
            let acc := if 1 ≤ w && w ≤ 5 then acc + 1.0 else acc
            go fuel (cur + 1) acc
      go ((toEpochDay t - toEpochDay s).toNat) (toEpochDay s + 1) 0.0 / 252.0

end Actus.Util.DayCount
