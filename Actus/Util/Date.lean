/-
## Date arithmetic on `LocalTime`

ACTUS schedules are computed on ISO-8601 calendar dates (§2.8 of the techspec).
This module provides the calendar primitives the schedule machinery needs:

* proleptic-Gregorian serial day numbers (`toEpochDay`) so dates can be ordered
  and mapped onto the `Time := Nat` axis events live on (`Protocol.Time`);
* calendar-aware shifts (`addPeriod`, `addCycle`) for the `Cycle`/`Period`
  records (`Protocol.Cycle`, `Protocol.Period`);
* leap-year / month-length / weekday helpers.

The serial-day conversion is Howard Hinnant's `days_from_civil` algorithm
(days relative to 1970-01-01), valid across the whole proleptic Gregorian range.
-/

import Actus.Protocol

namespace Actus.Util.Date

open Actus.Protocol

-- ---------------------------------------------------------------------------
-- Calendar primitives
-- ---------------------------------------------------------------------------

/-- Proleptic-Gregorian leap-year test. -/
def isLeapYear (y : Nat) : Bool :=
  (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

/-- Number of days in month `m` (1–12) of year `y`. -/
def daysInMonth (y m : Nat) : Nat :=
  match m with
  | 1  => 31 | 2  => if isLeapYear y then 29 else 28
  | 3  => 31 | 4  => 30 | 5  => 31 | 6  => 30
  | 7  => 31 | 8  => 31 | 9  => 30 | 10 => 31
  | 11 => 30 | 12 => 31
  | _  => 30

-- ---------------------------------------------------------------------------
-- Serial day number  (Hinnant `days_from_civil`, epoch = 1970-01-01)
-- ---------------------------------------------------------------------------

/-- Days from 1970-01-01 (negative for earlier dates). -/
def toEpochDay (d : LocalTime) : Int :=
  let y : Int := (d.year : Int) - (if d.month <= 2 then 1 else 0)
  let era : Int := (if y >= 0 then y else y - 399) / 400
  let yoe : Int := y - era * 400
  let mp : Int := (d.month : Int) + (if d.month > 2 then -3 else 9)
  let doy : Int := (153 * mp + 2) / 5 + (d.day : Int) - 1
  let doe : Int := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- Inverse of `toEpochDay` (Hinnant `civil_from_days`). -/
def ofEpochDay (z : Int) : LocalTime :=
  let z := z + 719468
  let era : Int := (if z >= 0 then z else z - 146096) / 146097
  let doe : Int := z - era * 146097
  let yoe : Int := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y : Int := yoe + era * 400
  let doy : Int := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp : Int := (5 * doy + 2) / 153
  let d : Int := doy - (153 * mp + 2) / 5 + 1
  let m : Int := mp + (if mp < 10 then 3 else -9)
  { day   := d.toNat
    month := m.toNat
    year  := (y + (if m <= 2 then 1 else 0)).toNat }

-- ---------------------------------------------------------------------------
-- Ordering
-- ---------------------------------------------------------------------------

instance : Ord LocalTime where
  compare a b := compare (toEpochDay a) (toEpochDay b)

instance : LE LocalTime := ⟨fun a b => toEpochDay a ≤ toEpochDay b⟩
instance : LT LocalTime := ⟨fun a b => toEpochDay a < toEpochDay b⟩

instance : BEq LocalTime where
  beq a b := toEpochDay a == toEpochDay b

/-- Weekday, 0 = Sunday … 6 = Saturday (Hinnant `weekday_from_days`). -/
def weekday (d : LocalTime) : Nat :=
  let z := toEpochDay d
  (if z >= -4 then (z + 4) % 7 else (z + 5) % 7 + 6).toNat

-- ---------------------------------------------------------------------------
-- Calendar shifts
-- ---------------------------------------------------------------------------

/-- Add `n` whole months, clamping the day to the target month's length. -/
def addMonths (d : LocalTime) (n : Nat) : LocalTime :=
  let total := (d.month - 1) + n               -- 0-based month index
  let year  := d.year + total / 12
  let month := total % 12 + 1
  { day := min d.day (daysInMonth year month), month := month, year := year }

/-- Add `n` whole days. -/
def addDays (d : LocalTime) (n : Nat) : LocalTime :=
  ofEpochDay (toEpochDay d + (n : Int))

/-- Number of months in one ACTUS period unit (`Q`=3, `H`=6, `Y`=12, `M`=1). -/
def monthsOfUnit : String → Option Nat
  | "M" => some 1 | "Q" => some 3 | "H" => some 6 | "Y" => some 12
  | _   => none

/-- Number of days in one ACTUS period unit (`D`=1, `W`=7). -/
def daysOfUnit : String → Option Nat
  | "D" => some 1 | "W" => some 7
  | _   => none

/-- Advance `d` by `n` units of the given period (`D/W/M/Q/H/Y`). -/
def addPeriod (d : LocalTime) (n : Nat) (unit : String) : LocalTime :=
  match monthsOfUnit unit with
  | some k => addMonths d (n * k)
  | none   => match daysOfUnit unit with
              | some k => addDays d (n * k)
              | none   => d

/-- Advance `d` by one `Cycle`. -/
def addCycle (d : LocalTime) (c : Cycle) : LocalTime :=
  addPeriod d c.n c.period

/-- Subtract `n` whole months (floor division on the month index). -/
def subMonths (d : LocalTime) (n : Nat) : LocalTime :=
  let total : Int := (d.month : Int) - 1 - (n : Int)
  let q : Int := if total ≥ 0 then total / 12 else -((-total + 11) / 12)  -- floor div
  let year  := ((d.year : Int) + q).toNat
  let month := (total - q * 12).toNat + 1
  { day := min d.day (daysInMonth year month), month := month, year := year }

/-- Move `d` back by `n` units of the given period (`D/W/M/Q/H/Y`). -/
def subPeriod (d : LocalTime) (n : Nat) (unit : String) : LocalTime :=
  match monthsOfUnit unit with
  | some k => subMonths d (n * k)
  | none   => match daysOfUnit unit with
              | some k => ofEpochDay (toEpochDay d - (n * k : Nat))
              | none   => d

end Actus.Util.Date
