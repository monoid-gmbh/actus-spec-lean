/-
## Conventions: contract-role sign, end-of-month, business-day shift

Implements three convention layers from the techspec:

* **Contract Role Sign** `R : CNTRL → {-1,+1}` (§3.7, Table 1, p.6) — the
  direction of a cash flow / role-sensitive state from the `CRID`'s viewpoint.
* **End-Of-Month Shift** `EOM` (§3.3) — whether monthly+ schedule times fall on
  the same day-of-month or are pushed to month end.
* **Business Day Shift** `BDC` (§3.4) and the **Business Day Calendar** `CLDR`
  (§3.5) — moving non-business schedule times onto business days.

This file replaces the placeholder `sign` that previously lived in
`Actus.Protocol`.
-/

import Actus.Protocol
import Actus.Util.Date

namespace Actus.Util.Conventions

open Actus.Protocol
open Actus.Util.Date

-- ---------------------------------------------------------------------------
-- Contract Role Sign  (R : CNTRL → {-1, +1}),  Table 1, p.6
-- ---------------------------------------------------------------------------

/-- Contract-role sign: `+1` for a claim (asset side), `-1` for an obligation. -/
def sign : ContractRole → Float
  | .CR_RPA => 1.0   | .CR_RPL => -1.0
  | .CR_LG  => 1.0   | .CR_ST  => -1.0
  | .CR_BUY => 1.0   | .CR_SEL => -1.0
  | .CR_RFL => 1.0   | .CR_PFL => -1.0
  | .CR_RF  => 1.0   | .CR_PF  => -1.0
  | .CR_CLO => 1.0   | .CR_CNO => 1.0
  | .CR_COL => 1.0

-- ---------------------------------------------------------------------------
-- End-Of-Month convention  (§3.3)
-- ---------------------------------------------------------------------------

/-- Last calendar day of `d`'s month. -/
def endOfMonth (d : LocalTime) : LocalTime :=
  { d with day := daysInMonth d.year d.month }

/-- Is `d` the last day of its month? -/
def isEndOfMonth (d : LocalTime) : Bool :=
  d.day == daysInMonth d.year d.month

/-- An anchor triggers the EOM convention when it is the last day of a month
    that is shorter than 31 days (§3.3). -/
def eomApplies (anchor : LocalTime) : Bool :=
  isEndOfMonth anchor && daysInMonth anchor.year anchor.month < 31

/-- Apply the end-of-month convention to a generated schedule time `d`, given
    the schedule's `anchor`.  Only relevant for month-or-longer cycles; the
    caller passes that decision via `cycleIsMonthly`. -/
def applyEOM (eomc : EndOfMonthConvention) (anchor : LocalTime)
    (cycleIsMonthly : Bool) (d : LocalTime) : LocalTime :=
  if cycleIsMonthly && eomApplies anchor then
    match eomc with
    | .EOMC_EOM => endOfMonth d                       -- push to month end
    | .EOMC_SD  => { d with day := min anchor.day (daysInMonth d.year d.month) }
  else d

-- ---------------------------------------------------------------------------
-- Business Day Calendar  (§3.5)
-- ---------------------------------------------------------------------------

/-- Is `d` a business day under calendar `cal`?  `CLDR_NC` (and the absence of a
    calendar) treats every calendar day as a business day. -/
def isBusinessDay (cal : Option Calendar) (d : LocalTime) : Bool :=
  match cal with
  | some .CLDR_MF => let w := weekday d; 1 ≤ w && w ≤ 5   -- Mon..Fri
  | _             => true

-- ---------------------------------------------------------------------------
-- Business Day Shift  (§3.4)
-- ---------------------------------------------------------------------------

/-- Next business day on/after `d` (fuel-bounded; a week is always enough). -/
partial def shiftFollowing (cal : Option Calendar) (d : LocalTime) : LocalTime :=
  if isBusinessDay cal d then d else shiftFollowing cal (addDays d 1)

/-- Latest business day on/before `d`. -/
def shiftPreceding (cal : Option Calendar) (d : LocalTime) : LocalTime :=
  let rec go (fuel : Nat) (x : LocalTime) : LocalTime :=
    match fuel with
    | 0 => x
    | fuel + 1 => if isBusinessDay cal x then x else go fuel (ofEpochDay (toEpochDay x - 1))
  go 7 d

/-- Apply a business-day convention to the *event date*.  The shift/calculate
    distinction (SC* vs CS*) affects only which date the year-fraction is
    computed from, not the resulting event date, so both collapse here. -/
def applyBDC (bdc : BusinessDayConvention) (cal : Option Calendar)
    (d : LocalTime) : LocalTime :=
  match bdc with
  | .BDC_NULL => d
  | .BDC_SCF | .BDC_CSF => shiftFollowing cal d
  | .BDC_SCP | .BDC_CSP => shiftPreceding cal d
  | .BDC_SCMF | .BDC_CSMF =>
      let f := shiftFollowing cal d
      if f.month == d.month then f else shiftPreceding cal d
  | .BDC_SCMP | .BDC_CSMP =>
      let p := shiftPreceding cal d
      if p.month == d.month then p else shiftFollowing cal d

/-- Does the convention shift *before* calculating (`SC*`)?  Such conventions
    move the schedule date first, so calculations use the shifted date.  The
    *calculate-then-shift* family (`CS*`) and `NULL` do not. -/
def isShiftFirst : BusinessDayConvention → Bool
  | .BDC_SCF | .BDC_SCMF | .BDC_SCP | .BDC_SCMP => true
  | _ => false

/-- Apply EOM, then — for *shift-then-calculate* (`SC*`) conventions — the
    business-day shift, so that calculations downstream use the shifted date.
    For `CS*` conventions the shift is deferred to `settlementDate` (the schedule
    keeps the unshifted date so accruals are computed on it). -/
def applyConventions (cfg : ScheduleConfig) (anchor : LocalTime)
    (cycleIsMonthly : Bool) (d : LocalTime) : LocalTime :=
  let d := match cfg.endOfMonthConvention with
           | some eomc => applyEOM eomc anchor cycleIsMonthly d
           | none      => d
  match cfg.businessDayConvention with
  | some bdc => if isShiftFirst bdc then applyBDC bdc cfg.calendar d else d
  | none     => d

/-- The business-day on which a schedule time settles.  For `CS*` conventions
    this applies the deferred shift (the event is stamped on the business day
    while accruals used the unshifted date); for `SC*` the shift already
    happened in `applyConventions`, and `NULL`/none never shift. -/
def settlementDate (cfg : ScheduleConfig) (d : LocalTime) : LocalTime :=
  match cfg.businessDayConvention with
  | some bdc => if isShiftFirst bdc then d else applyBDC bdc cfg.calendar d
  | none     => d

end Actus.Util.Conventions
