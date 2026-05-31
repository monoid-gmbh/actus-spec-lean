/-
## PAM — Principal at Maturity  (§7.1)

#### Description
Principal paid in full at the Initial Exchange Date `IED` and repaid in a lump
sum at the Maturity Date `MD`; fixed or variable interest in between.

#### Real-world instruments
Bonds, term deposits, bullet loans and mortgages, etc.

### Modeling
This module gives PAM **both** models the user asked for, written once and
**generic over the amount type `α`** (`Float` to execute, `ℝ` to prove):

* a *functional* model — one `stf_*`/`pof_*` per event from the §7.1
  STF/POF tables, plus the dispatchers `stf`/`pof`.  These are reused verbatim
  by LAM/NAM/ANN (the "Same as PAM" / `STF_X_PAM()` table entries).
* a *relational* model — the inductive `Step`, the readable spec, whose every
  constructor concludes `Step s (stf_X …)`.  The two are proven to agree in
  `Actus.Contract.Agree`.

Convention helpers `sign`, the year fraction `Y` (via `RiskFactorEnv.yf`) and
fee/interest accrual are shared via `Actus.Contract.Common`.
-/

import Actus.Protocol
import Actus.Abstract
import Actus.Closures
import Actus.Contract.Common
import Actus.Util.Conventions

namespace Actus.Contract.PAM

open Actus.Protocol
open Actus.Abstract
open Actus.Closures
open Actus.Contract
open Actus.Util.Conventions (sign)
open Actus (Amount)

variable {α : Type} [Amount α]

-- ---------------------------------------------------------------------------
-- Shared accrual sub-formulas
-- ---------------------------------------------------------------------------

/-- Interest accrual `Ipac_{t-} + Y(Sd_{t-}, t)·Ipnr_{t-}·Nt_{t-}`. -/
def ipacAccr (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  s.ipac + rf.yf s.sd t * s.ipnr * s.nt

/-- Fee accrual `Feac_{t+}` (§7.1).  The `FEB_N` branch is exact; the absolute
    (`FEB_A`) branch's proration over the fee period is omitted because the
    state does not carry the fee-period boundaries `t^{FP±}`. -/
def feacNext (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  match Terms.feb ct with
  | .FEB_N => s.feac + rf.yf s.sd t * s.nt * Terms.fer ct
  | .FEB_A => s.feac

-- ---------------------------------------------------------------------------
-- State Transition Functions  (STF, §7.1)
-- ---------------------------------------------------------------------------

def stf_AD (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  { s with ipac := ipacAccr rf t s, sd := t }

def stf_IED (ct : Terms α) (t : Time) (s : State α) : State α :=
  { s with
    nt   := sign (Terms.cntrl ct) * Terms.nt ct
    ipnr := Terms.ipnr ct
    ipac := sign (Terms.cntrl ct) * (ct.accruedInterest.getD 0)
    sd   := t }

def stf_MD (t : Time) (s : State α) : State α :=
  { s with nt := 0, ipac := 0, feac := 0, sd := t }

def stf_PP (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  { s with ipac := ipacAccr rf t s, feac := feacNext ct rf t s
           nt := s.nt - rf.prepayment t, sd := t }

def stf_PY (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  { s with ipac := ipacAccr rf t s, feac := feacNext ct rf t s, sd := t }

def stf_FP (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  { s with ipac := ipacAccr rf t s, feac := 0, sd := t }

def stf_PRD (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  { s with ipac := ipacAccr rf t s, feac := feacNext ct rf t s, sd := t }

def stf_TD (t : Time) (s : State α) : State α :=
  { s with nt := 0, ipac := 0, feac := 0, ipnr := 0, sd := t }

def stf_IP (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  { s with ipac := 0, feac := feacNext ct rf t s, sd := t }

def stf_IPCI (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  { s with nt := s.nt + ipacAccr rf t s, ipac := 0
           feac := feacNext ct rf t s, sd := t }

/-- Rate reset: `Ipnr_{t+} = clamp_{[RRLF,RRLC]}(Ipnr+Δr)` with
    `Δr = clamp_{[RRPF,RRPC]}(Oʳᶠ(RRMO,t)·RRMLT + RRSP − Ipnr)`.  Absent caps /
    floors impose no bound (`clampHi`/`clampLo` with `none`). -/
def stf_RR (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  let dr := clampHi ct.periodCap
              (clampLo ct.periodFloor
                (rf.marketRate t * Terms.rrmlt ct + Terms.rrsp ct - s.ipnr))
  let newRate := clampHi ct.lifeCap (clampLo ct.lifeFloor (s.ipnr + dr))
  { s with ipac := ipacAccr rf t s, feac := feacNext ct rf t s, ipnr := newRate, sd := t }

def stf_RRF (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  { s with ipac := ipacAccr rf t s, feac := feacNext ct rf t s
           ipnr := Terms.rrnxt ct, sd := t }

/-- Scaling (§7.1): `Nsc`/`Isc` are reset to `Oʳᶠ(SCMO,t)/SCIED` for the
    dimensions the `SCEF` code scales (notional and/or interest). -/
def stf_SC (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  let factor := rf.scalingIndex t / Terms.scied ct
  { s with ipac := ipacAccr rf t s, feac := feacNext ct rf t s
           nsc := if scalesNotional (Terms.scief ct) then factor else s.nsc
           isc := if scalesInterest (Terms.scief ct) then factor else s.isc
           sd := t }

/-- Credit event uses `STF_AD_PAM()`. -/
def stf_CE (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α := stf_AD rf t s

/-- STF dispatcher by event type (events not in the PAM schedule just advance
    the status date). -/
def stf (ct : Terms α) (rf : RiskFactorEnv α) (ev : EventType) (t : Time) (s : State α) : State α :=
  match ev with
  | .AD   => stf_AD rf t s      | .IED  => stf_IED ct t s
  | .MD   => stf_MD t s         | .PP   => stf_PP ct rf t s
  | .PY   => stf_PY ct rf t s   | .FP   => stf_FP rf t s
  | .PRD  => stf_PRD ct rf t s  | .TD   => stf_TD t s
  | .IP   => stf_IP ct rf t s   | .IPCI => stf_IPCI ct rf t s
  | .RR   => stf_RR ct rf t s   | .RRF  => stf_RRF ct rf t s
  | .SC   => stf_SC ct rf t s   | .CE   => stf_CE rf t s
  | _     => { s with sd := t }

-- ---------------------------------------------------------------------------
-- Payoff Functions  (POF, §7.1)
-- ---------------------------------------------------------------------------

def pof_AD : α := 0

def pof_IED (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) : α :=
  rf.curs t * sign (Terms.cntrl ct) * (-1) * (Terms.nt ct + Terms.pdied ct)

def pof_MD (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  rf.curs t * (s.nsc * s.nt + s.isc * s.ipac + s.feac)

def pof_PP (rf : RiskFactorEnv α) (t : Time) : α :=
  rf.curs t * rf.prepayment t

def pof_PY (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  let c := rf.curs t * sign (Terms.cntrl ct) * rf.yf s.sd t * s.nt
  match ct.penaltyType.getD .PYTP_O with
  | .PYTP_A => rf.curs t * sign (Terms.cntrl ct) * Terms.pyrt ct
  | .PYTP_N => c * Terms.pyrt ct
  | .PYTP_I => c * max 0 (s.ipnr - rf.marketRate t)
  | .PYTP_O => 0

def pof_FP (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  let c := rf.curs t * Terms.fer ct
  match Terms.feb ct with
  | .FEB_A => sign (Terms.cntrl ct) * c
  | .FEB_N => c * rf.yf s.sd t * s.nt + s.feac

def pof_PRD (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  rf.curs t * sign (Terms.cntrl ct) * (-1) *
    (Terms.pprd ct + s.ipac + rf.yf s.sd t * s.ipnr * s.nt)

def pof_TD (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  rf.curs t * sign (Terms.cntrl ct) *
    (Terms.ptd ct + s.ipac + rf.yf s.sd t * s.ipnr * s.nt)

def pof_IP (_ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  rf.curs t * s.isc * (s.ipac + rf.yf s.sd t * s.ipnr * s.nt)

/-- POF dispatcher by event type. -/
def pof (ct : Terms α) (rf : RiskFactorEnv α) (ev : EventType) (t : Time) (s : State α) : α :=
  match ev with
  | .IED => pof_IED ct rf t      | .MD  => pof_MD rf t s
  | .PP  => pof_PP rf t          | .PY  => pof_PY ct rf t s
  | .FP  => pof_FP ct rf t s     | .PRD => pof_PRD ct rf t s
  | .TD  => pof_TD ct rf t s     | .IP  => pof_IP ct rf t s
  | _    => 0   -- AD, IPCI, RR, RRF, SC, CE

-- ---------------------------------------------------------------------------
-- State initialization at t₀  (§7.1)
-- ---------------------------------------------------------------------------

/-- Initial state per the §7.1 initialization table.  `md` is the maturity date
    on the `Time` axis (caller supplies it from `genSchedule`); `t₀` is the
    status date. -/
def init (ct : Terms α) (md t₀ : Time) : State α :=
  { md    := md
    nt    := if t₀ < md then sign (Terms.cntrl ct) * Terms.nt ct else 0
    ipnr  := if t₀ < md then Terms.ipnr ct else 0
    ipac  := sign (Terms.cntrl ct) * (ct.accruedInterest.getD 0)
    feac  := ct.feeAccrued.getD 0
    nsc   := ct.notionalScalingMultiplier.getD 1
    isc   := ct.interestScalingMultiplier.getD 1
    prnxt := Terms.prnxt ct
    ipcb  := 0
    prf   := ct.contractPerformance.getD .PRF_PF
    sd    := t₀ }

-- ---------------------------------------------------------------------------
-- Relational model:  Step  (the readable spec)
-- ---------------------------------------------------------------------------

/-- One-step state-transition relation for PAM: `Step ct rf s s'` holds when the
    contract advances from `s` to `s'` by one scheduled event at time `t ≥ Sd`.
    Each constructor's target is the corresponding functional `stf_*`. -/
inductive Step (ct : Terms α) (rf : RiskFactorEnv α) : State α → State α → Type where
  | ad   : ∀ {s : State α} {t : Time}, s.sd ≤ t → Step ct rf s (stf_AD rf t s)
  | ied  : ∀ {s : State α} {t : Time}, s.sd ≤ t → Step ct rf s (stf_IED ct t s)
  | md   : ∀ {s : State α} {t : Time}, s.sd ≤ t → Step ct rf s (stf_MD t s)
  | pp   : ∀ {s : State α} {t : Time}, s.sd ≤ t → Step ct rf s (stf_PP ct rf t s)
  | py   : ∀ {s : State α} {t : Time}, s.sd ≤ t → Step ct rf s (stf_PY ct rf t s)
  | fp   : ∀ {s : State α} {t : Time}, s.sd ≤ t → Step ct rf s (stf_FP rf t s)
  | prd  : ∀ {s : State α} {t : Time}, s.sd ≤ t → Step ct rf s (stf_PRD ct rf t s)
  | td   : ∀ {s : State α} {t : Time}, s.sd ≤ t → Step ct rf s (stf_TD t s)
  | ip   : ∀ {s : State α} {t : Time}, s.sd ≤ t → Step ct rf s (stf_IP ct rf t s)
  | ipci : ∀ {s : State α} {t : Time}, s.sd ≤ t → Step ct rf s (stf_IPCI ct rf t s)
  | rr   : ∀ {s : State α} {t : Time}, s.sd ≤ t → Step ct rf s (stf_RR ct rf t s)
  | rrf  : ∀ {s : State α} {t : Time}, s.sd ≤ t → Step ct rf s (stf_RRF ct rf t s)
  | sc   : ∀ {s : State α} {t : Time}, s.sd ≤ t → Step ct rf s (stf_SC ct rf t s)
  | ce   : ∀ {s : State α} {t : Time}, s.sd ≤ t → Step ct rf s (stf_CE rf t s)

@[inherit_doc] notation:50 s " ↝[" ct ", " rf "] " s' => Step ct rf s s'

/-- Execution trace: zero-or-more PAM steps. -/
abbrev Trace (ct : Terms α) (rf : RiskFactorEnv α) := Star (Step ct rf)

-- ---------------------------------------------------------------------------
-- Cashflow extraction
-- ---------------------------------------------------------------------------

/-- The cashflow of one PAM step: event time is the post-state status date
    (`= t`), the payoff is the matching `pof_*` applied to the *pre*-state. -/
def getCashflow (ct : Terms α) (rf : RiskFactorEnv α) {s s' : State α}
    (h : Step ct rf s s') : Event × α :=
  match h with
  | .ad _   => ((s'.sd, .AD),  pof_AD)
  | .ied _  => ((s'.sd, .IED), pof_IED ct rf s'.sd)
  | .md _   => ((s'.sd, .MD),  pof_MD rf s'.sd s)
  | .pp _   => ((s'.sd, .PP),  pof_PP rf s'.sd)
  | .py _   => ((s'.sd, .PY),  pof_PY ct rf s'.sd s)
  | .fp _   => ((s'.sd, .FP),  pof_FP ct rf s'.sd s)
  | .prd _  => ((s'.sd, .PRD), pof_PRD ct rf s'.sd s)
  | .td _   => ((s'.sd, .TD),  pof_TD ct rf s'.sd s)
  | .ip _   => ((s'.sd, .IP),  pof_IP ct rf s'.sd s)
  | .ipci _ => ((s'.sd, .IPCI), 0)
  | .rr _   => ((s'.sd, .RR),  0)
  | .rrf _  => ((s'.sd, .RRF), 0)
  | .sc _   => ((s'.sd, .SC),  0)
  | .ce _   => ((s'.sd, .CE),  0)

/-- Collect cashflows along a full execution trace. -/
def getCashflows (ct : Terms α) (rf : RiskFactorEnv α) :
    ∀ {s s' : State α}, Trace ct rf s s' → List (Event × α)
  | _, _, .refl        => []
  | _, _, .step h rest => getCashflow ct rf h :: getCashflows ct rf rest

-- ---------------------------------------------------------------------------
-- PAM as an ActusContract / StateTransition  (the executable `Float` interface)
-- ---------------------------------------------------------------------------

def PAM_contract : ActusContract := { Terms := Terms Float, State := State Float }

/-- Witness that PAM satisfies the abstract `StateTransition` interface. -/
def PAM_impl (ct : Terms Float) (rf : RiskFactorEnv Float) (s₀ : State Float) :
    StateTransition PAM_contract :=
  { s₀          := s₀
    rel          := Step ct rf
    getCashflow  := fun h r =>
      -- the abstract interface threads a `RiskFactor`; PAM's settlement factor
      -- is already captured in `rf`, so the extra argument is unused here.
      let _ := r
      getCashflow ct rf h }

end Actus.Contract.PAM
