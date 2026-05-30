/-
## PAM — Principal at Maturity  (§7.1)

#### Description
Principal paid in full at the Initial Exchange Date `IED` and repaid in a lump
sum at the Maturity Date `MD`; fixed or variable interest in between.

#### Real-world instruments
Bonds, term deposits, bullet loans and mortgages, etc.

### Modeling
This module gives PAM **both** models the user asked for:

* a *functional* model — one `stf_*`/`pof_*` per event from the §7.1
  STF/POF tables, plus the dispatchers `stf`/`pof`.  These are reused verbatim
  by LAM/NAM/ANN (the "Same as PAM" / `STF_X_PAM()` table entries).
* a *relational* model — the inductive `Step`, the readable spec, whose every
  constructor concludes `Step s (stf_X …)`.  The two are proven to agree in
  `Actus.Contract.Lending.Agree`.

Convention helpers `sign`, `Y`, fee/interest accrual are shared via
`Actus.Contract.Lending.Common`.
-/

import Actus.Protocol
import Actus.Abstract
import Actus.Closures
import Actus.Contract.Lending.Common
import Actus.Util.Conventions

namespace Actus.Contract.PAM

open Actus.Protocol
open Actus.Abstract
open Actus.Closures
open Actus.Contract.Lending
open Actus.Util.Conventions (sign)

abbrev Terms := Lending.Terms
abbrev State := Lending.State

-- ---------------------------------------------------------------------------
-- Shared accrual sub-formulas
-- ---------------------------------------------------------------------------

/-- Interest accrual `Ipac_{t-} + Y(Sd_{t-}, t)·Ipnr_{t-}·Nt_{t-}`. -/
def ipacAccr (ct : Terms) (t : Time) (s : State) : Float :=
  s.ipac + yf ct s.sd t * s.ipnr * s.nt

/-- Fee accrual `Feac_{t+}` (§7.1).  The `FEB_N` branch is exact; the absolute
    (`FEB_A`) branch's proration over the fee period is omitted because the
    state does not carry the fee-period boundaries `t^{FP±}`. -/
def feacNext (ct : Terms) (t : Time) (s : State) : Float :=
  match Terms.feb ct with
  | .FEB_N => s.feac + yf ct s.sd t * s.nt * Terms.fer ct
  | .FEB_A => s.feac

-- ---------------------------------------------------------------------------
-- State Transition Functions  (STF, §7.1)
-- ---------------------------------------------------------------------------

def stf_AD (ct : Terms) (t : Time) (s : State) : State :=
  { s with ipac := ipacAccr ct t s, sd := t }

def stf_IED (ct : Terms) (t : Time) (s : State) : State :=
  { s with
    nt   := sign (Terms.cntrl ct) * Terms.nt ct
    ipnr := Terms.ipnr ct
    ipac := ct.accruedInterest.getD 0.0
    sd   := t }

def stf_MD (_ct : Terms) (t : Time) (s : State) : State :=
  { s with nt := 0.0, ipac := 0.0, feac := 0.0, sd := t }

def stf_PP (ct : Terms) (rf : RiskFactorEnv) (t : Time) (s : State) : State :=
  { s with ipac := ipacAccr ct t s, feac := feacNext ct t s
           nt := s.nt - rf.prepayment t, sd := t }

def stf_PY (ct : Terms) (t : Time) (s : State) : State :=
  { s with ipac := ipacAccr ct t s, feac := feacNext ct t s, sd := t }

def stf_FP (ct : Terms) (t : Time) (s : State) : State :=
  { s with ipac := ipacAccr ct t s, feac := 0.0, sd := t }

def stf_PRD (ct : Terms) (t : Time) (s : State) : State :=
  { s with ipac := ipacAccr ct t s, feac := feacNext ct t s, sd := t }

def stf_TD (_ct : Terms) (t : Time) (s : State) : State :=
  { s with nt := 0.0, ipac := 0.0, feac := 0.0, ipnr := 0.0, sd := t }

def stf_IP (ct : Terms) (t : Time) (s : State) : State :=
  { s with ipac := 0.0, feac := feacNext ct t s, sd := t }

def stf_IPCI (ct : Terms) (t : Time) (s : State) : State :=
  { s with nt := s.nt + ipacAccr ct t s, ipac := 0.0
           feac := feacNext ct t s, sd := t }

/-- Rate reset: `Ipnr_{t+} = min(max(Ipnr+Δr, RRLF), RRLC)` with
    `Δr = min(max(Oʳᶠ(RRMO,t)·RRMLT + RRSP − Ipnr, RRPF), RRPC)`. -/
def stf_RR (ct : Terms) (rf : RiskFactorEnv) (t : Time) (s : State) : State :=
  let dr := min (max (rf.marketRate t * Terms.rrmlt ct + Terms.rrsp ct - s.ipnr)
                     (Terms.rrpf ct)) (Terms.rrpc ct)
  let newRate := min (max (s.ipnr + dr) (Terms.rrlf ct)) (Terms.rrlc ct)
  { s with ipac := ipacAccr ct t s, feac := feacNext ct t s, ipnr := newRate, sd := t }

def stf_RRF (ct : Terms) (t : Time) (s : State) : State :=
  { s with ipac := ipacAccr ct t s, feac := feacNext ct t s
           ipnr := Terms.rrnxt ct, sd := t }

/-- Scaling (§7.1): `Nsc`/`Isc` are reset to `(Oʳᶠ(SCMO,t) − SCIED)/SCIED` for
    the dimensions the `SCEF` code scales (notional and/or interest). -/
def stf_SC (ct : Terms) (rf : RiskFactorEnv) (t : Time) (s : State) : State :=
  let factor := rf.scalingIndex t / Terms.scied ct
  { s with ipac := ipacAccr ct t s, feac := feacNext ct t s
           nsc := if scalesNotional (Terms.scief ct) then factor else s.nsc
           isc := if scalesInterest (Terms.scief ct) then factor else s.isc
           sd := t }

/-- Credit event uses `STF_AD_PAM()`. -/
def stf_CE (ct : Terms) (t : Time) (s : State) : State := stf_AD ct t s

/-- STF dispatcher by event type (events not in the PAM schedule just advance
    the status date). -/
def stf (ct : Terms) (rf : RiskFactorEnv) (ev : EventType) (t : Time) (s : State) : State :=
  match ev with
  | .AD   => stf_AD ct t s      | .IED  => stf_IED ct t s
  | .MD   => stf_MD ct t s      | .PP   => stf_PP ct rf t s
  | .PY   => stf_PY ct t s      | .FP   => stf_FP ct t s
  | .PRD  => stf_PRD ct t s     | .TD   => stf_TD ct t s
  | .IP   => stf_IP ct t s      | .IPCI => stf_IPCI ct t s
  | .RR   => stf_RR ct rf t s   | .RRF  => stf_RRF ct t s
  | .SC   => stf_SC ct rf t s   | .CE   => stf_CE ct t s
  | _     => { s with sd := t }

-- ---------------------------------------------------------------------------
-- Payoff Functions  (POF, §7.1)
-- ---------------------------------------------------------------------------

def pof_AD : Payoff := 0.0

def pof_IED (ct : Terms) (rf : RiskFactorEnv) (t : Time) : Payoff :=
  rf.curs t * sign (Terms.cntrl ct) * (-1.0) * (Terms.nt ct + Terms.pdied ct)

def pof_MD (rf : RiskFactorEnv) (t : Time) (s : State) : Payoff :=
  rf.curs t * (s.nsc * s.nt + s.isc * s.ipac + s.feac)

def pof_PP (rf : RiskFactorEnv) (t : Time) : Payoff :=
  rf.curs t * rf.prepayment t

def pof_PY (ct : Terms) (rf : RiskFactorEnv) (t : Time) (s : State) : Payoff :=
  let c := rf.curs t * sign (Terms.cntrl ct) * yf ct s.sd t * s.nt
  match ct.penaltyType.getD .PYTP_O with
  | .PYTP_A => rf.curs t * sign (Terms.cntrl ct) * Terms.pyrt ct
  | .PYTP_N => c * Terms.pyrt ct
  | .PYTP_I => c * max 0.0 (s.ipnr - rf.marketRate t)
  | .PYTP_O => 0.0

def pof_FP (ct : Terms) (rf : RiskFactorEnv) (t : Time) (s : State) : Payoff :=
  let c := rf.curs t * Terms.fer ct
  match Terms.feb ct with
  | .FEB_A => sign (Terms.cntrl ct) * c
  | .FEB_N => c * yf ct s.sd t * s.nt + s.feac

def pof_PRD (ct : Terms) (rf : RiskFactorEnv) (t : Time) (s : State) : Payoff :=
  rf.curs t * sign (Terms.cntrl ct) * (-1.0) *
    (Terms.pprd ct + s.ipac + yf ct s.sd t * s.ipnr * s.nt)

def pof_TD (ct : Terms) (rf : RiskFactorEnv) (t : Time) (s : State) : Payoff :=
  rf.curs t * sign (Terms.cntrl ct) *
    (Terms.ptd ct + s.ipac + yf ct s.sd t * s.ipnr * s.nt)

def pof_IP (ct : Terms) (rf : RiskFactorEnv) (t : Time) (s : State) : Payoff :=
  rf.curs t * s.isc * (s.ipac + yf ct s.sd t * s.ipnr * s.nt)

/-- POF dispatcher by event type. -/
def pof (ct : Terms) (rf : RiskFactorEnv) (ev : EventType) (t : Time) (s : State) : Payoff :=
  match ev with
  | .IED => pof_IED ct rf t      | .MD  => pof_MD rf t s
  | .PP  => pof_PP rf t          | .PY  => pof_PY ct rf t s
  | .FP  => pof_FP ct rf t s     | .PRD => pof_PRD ct rf t s
  | .TD  => pof_TD ct rf t s     | .IP  => pof_IP ct rf t s
  | _    => 0.0   -- AD, IPCI, RR, RRF, SC, CE

-- ---------------------------------------------------------------------------
-- State initialization at t₀  (§7.1)
-- ---------------------------------------------------------------------------

/-- Initial state per the §7.1 initialization table.  `md` is the maturity date
    on the `Time` axis (caller supplies it from `genSchedule`); `t₀` is the
    status date. -/
def init (ct : Terms) (md t₀ : Time) : State :=
  { md    := md
    nt    := if t₀ < md then sign (Terms.cntrl ct) * Terms.nt ct else 0.0
    ipnr  := if t₀ < md then Terms.ipnr ct else 0.0
    ipac  := ct.accruedInterest.getD 0.0
    feac  := ct.feeAccrued.getD 0.0
    nsc   := ct.notionalScalingMultiplier.getD 1.0
    isc   := ct.interestScalingMultiplier.getD 1.0
    prnxt := Terms.prnxt ct
    ipcb  := 0.0
    prf   := ct.contractPerformance.getD .PRF_PF
    sd    := t₀ }

-- ---------------------------------------------------------------------------
-- Relational model:  Step  (the readable spec)
-- ---------------------------------------------------------------------------

/-- One-step state-transition relation for PAM: `Step ct rf s s'` holds when the
    contract advances from `s` to `s'` by one scheduled event at time `t ≥ Sd`.
    Each constructor's target is the corresponding functional `stf_*`. -/
inductive Step (ct : Terms) (rf : RiskFactorEnv) : State → State → Type where
  | ad   : ∀ {s : State} {t : Time}, s.sd ≤ t → Step ct rf s (stf_AD ct t s)
  | ied  : ∀ {s : State} {t : Time}, s.sd ≤ t → Step ct rf s (stf_IED ct t s)
  | md   : ∀ {s : State} {t : Time}, s.sd ≤ t → Step ct rf s (stf_MD ct t s)
  | pp   : ∀ {s : State} {t : Time}, s.sd ≤ t → Step ct rf s (stf_PP ct rf t s)
  | py   : ∀ {s : State} {t : Time}, s.sd ≤ t → Step ct rf s (stf_PY ct t s)
  | fp   : ∀ {s : State} {t : Time}, s.sd ≤ t → Step ct rf s (stf_FP ct t s)
  | prd  : ∀ {s : State} {t : Time}, s.sd ≤ t → Step ct rf s (stf_PRD ct t s)
  | td   : ∀ {s : State} {t : Time}, s.sd ≤ t → Step ct rf s (stf_TD ct t s)
  | ip   : ∀ {s : State} {t : Time}, s.sd ≤ t → Step ct rf s (stf_IP ct t s)
  | ipci : ∀ {s : State} {t : Time}, s.sd ≤ t → Step ct rf s (stf_IPCI ct t s)
  | rr   : ∀ {s : State} {t : Time}, s.sd ≤ t → Step ct rf s (stf_RR ct rf t s)
  | rrf  : ∀ {s : State} {t : Time}, s.sd ≤ t → Step ct rf s (stf_RRF ct t s)
  | sc   : ∀ {s : State} {t : Time}, s.sd ≤ t → Step ct rf s (stf_SC ct rf t s)
  | ce   : ∀ {s : State} {t : Time}, s.sd ≤ t → Step ct rf s (stf_CE ct t s)

@[inherit_doc] notation:50 s " ↝[" ct ", " rf "] " s' => Step ct rf s s'

/-- Execution trace: zero-or-more PAM steps. -/
abbrev Trace (ct : Terms) (rf : RiskFactorEnv) := Star (Step ct rf)

-- ---------------------------------------------------------------------------
-- Cashflow extraction
-- ---------------------------------------------------------------------------

/-- The cashflow of one PAM step: event time is the post-state status date
    (`= t`), the payoff is the matching `pof_*` applied to the *pre*-state. -/
def getCashflow (ct : Terms) (rf : RiskFactorEnv) {s s' : State}
    (h : Step ct rf s s') : Cashflow :=
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
  | .ipci _ => ((s'.sd, .IPCI), 0.0)
  | .rr _   => ((s'.sd, .RR),  0.0)
  | .rrf _  => ((s'.sd, .RRF), 0.0)
  | .sc _   => ((s'.sd, .SC),  0.0)
  | .ce _   => ((s'.sd, .CE),  0.0)

/-- Collect cashflows along a full execution trace. -/
def getCashflows (ct : Terms) (rf : RiskFactorEnv) :
    ∀ {s s' : State}, Trace ct rf s s' → Cashflows
  | _, _, .refl        => []
  | _, _, .step h rest => getCashflow ct rf h :: getCashflows ct rf rest

-- ---------------------------------------------------------------------------
-- PAM as an ActusContract / StateTransition
-- ---------------------------------------------------------------------------

def PAM_contract : ActusContract := { Terms := Terms, State := State }

/-- Witness that PAM satisfies the abstract `StateTransition` interface. -/
def PAM_impl (ct : Terms) (rf : RiskFactorEnv) (s₀ : State) :
    StateTransition PAM_contract :=
  { s₀          := s₀
    rel          := Step ct rf
    getCashflow  := fun h r =>
      -- the abstract interface threads a `RiskFactor`; PAM's settlement factor
      -- is already captured in `rf`, so the extra argument is unused here.
      let _ := r
      getCashflow ct rf h }

end Actus.Contract.PAM
