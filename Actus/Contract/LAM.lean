/-
## LAM — Linear Amortizer  (§7.2)

Principal is paid out at `IED` and paid back in fixed instalments `Prnxt` on a
principal-redemption (`PR`) cycle.  LAM is defined in §7.2 almost entirely as
deltas over PAM: most STFs are `STF_X_PAM()` and most POFs `POF_X_PAM()`.

The genuinely LAM-specific pieces are:

* a **PR** event (linear principal redemption) and an **IPCB** event (interest
  calculation base fixing);
* interest accrual on the *interest calculation base* `Ipcb` rather than `Nt`
  for the redemption/capitalization events;
* `Md`/`Prnxt`/`Ipcb` initialization.

Events whose accrual base is `Nt` reuse the PAM STF/POF directly (valid in the
common `IPCB = 'NT'` case where `Ipcb` tracks `Nt`).

Generic over the amount type `α`; `redeemed` needs a decidable order, supplied
by `Float` (computably) and `ℝ` (classically, for the spec).
-/

import Actus.Protocol
import Actus.Abstract
import Actus.Closures
import Actus.Contract.Common
import Actus.Contract.PAM
import Actus.Util.Conventions

namespace Actus.Contract.LAM

open Actus.Protocol
open Actus.Abstract
open Actus.Closures
open Actus.Contract
open Actus.Util.Conventions (sign)
open Actus (Amount)

variable {α : Type} [Amount α] [DecidableLE α]

/-- Interest-calculation-base value: tracks `Nt` when `IPCB = 'NT'` (or absent),
    otherwise the fixed `R(CNTRL)·IPCBA`. -/
def lamIpcb (ct : Terms α) (nt : α) : α :=
  match ct.interestCalculationBase with
  | some .IPCB_NTL => sign (Terms.cntrl ct) * Terms.ipcba ct   -- fixed at IPCBA, stepped at IPCB events
  | _              => nt                                       -- NT / NTIED / none track the notional

/-- Interest accrual on the interest calculation base `Ipcb`. -/
def ipacAccrIpcb (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  s.ipac + rf.yf s.sd t * s.ipnr * s.ipcb

-- ---------------------------------------------------------------------------
-- LAM-specific STFs
-- ---------------------------------------------------------------------------

def stf_IED (ct : Terms α) (t : Time) (s : State α) : State α :=
  let b := PAM.stf_IED ct t s
  { b with ipcb := lamIpcb ct b.nt }

/-- The actual principal redeemed: the instalment `Prnxt`, but capped at the
    remaining notional so a redemption never overshoots `0` (the final
    instalment is partial; once `Nt = 0` it pays nothing).  `Prnxt` and `Nt`
    share the contract-role sign. -/
def redeemed (nt prnxt : α) : α :=
  if Amount.abs nt ≤ Amount.abs prnxt then nt else prnxt

/-- Principal redemption: pay back `Prnxt` (capped at the remaining notional),
    accruing interest on `Ipcb`.  `Prnxt` already carries the contract-role sign
    (set in `lamInit`/`init`). -/
def stf_PR (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  let nt' := s.nt - redeemed s.nt s.prnxt
  { s with ipac := ipacAccrIpcb rf t s
           feac := PAM.feacNext ct rf t s
           nt   := nt'
           ipcb := match ct.interestCalculationBase with
                   | some .IPCB_NTL => s.ipcb   -- NTL: base fixed (stepped at IPCB)
                   | _              => nt'      -- NT / NTIED / none track the notional
           sd   := t }

def stf_IPCB (t : Time) (s : State α) : State α :=
  { s with ipcb := s.nt, sd := t }

def stf_IPCI (ct : Terms α) (rf : RiskFactorEnv α) (t : Time) (s : State α) : State α :=
  let nt' := s.nt + ipacAccrIpcb rf t s
  { s with nt := nt', ipac := 0, feac := PAM.feacNext ct rf t s
           ipcb := match ct.interestCalculationBase with
                   | some .IPCB_NTL => s.ipcb   -- NTL: base fixed (stepped at IPCB)
                   | _              => nt'      -- NT / NTIED / none track the notional
           sd := t }

/-- STF dispatcher: LAM-specific events plus PAM delegation. -/
def stf (ct : Terms α) (rf : RiskFactorEnv α) (ev : EventType) (t : Time) (s : State α) : State α :=
  match ev with
  | .IED  => stf_IED ct t s
  | .PR   => stf_PR ct rf t s
  | .IPCB => stf_IPCB t s
  | .IPCI => stf_IPCI ct rf t s
  | _     => PAM.stf ct rf ev t s

-- ---------------------------------------------------------------------------
-- LAM-specific POF
-- ---------------------------------------------------------------------------

def pof_PR (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  rf.curs t * s.nsc * redeemed s.nt s.prnxt

/-- Interest payment accrues on the interest calculation base `Ipcb` (which may
    differ from `Nt` when `IPCB ≠ 'NT'`), unlike PAM which accrues on `Nt`. -/
def pof_IP (rf : RiskFactorEnv α) (t : Time) (s : State α) : α :=
  rf.curs t * s.isc * (s.ipac + rf.yf s.sd t * s.ipnr * s.ipcb)

def pof (ct : Terms α) (rf : RiskFactorEnv α) (ev : EventType) (t : Time) (s : State α) : α :=
  match ev with
  | .PR => pof_PR rf t s
  | .IP => pof_IP rf t s
  | _   => PAM.pof ct rf ev t s

-- ---------------------------------------------------------------------------
-- Initialization at t₀  (§7.2)
-- ---------------------------------------------------------------------------

/-- Initial state.  `Prnxt` defaults to the term `PRNXT`, falling back to the
    full notional when absent (the annuity-style fallback needs the redemption
    schedule, omitted here). -/
def init (ct : Terms α) (md t₀ : Time) : State α :=
  let b := PAM.init ct md t₀
  { b with
    prnxt := if ct.nextPrincipalRedemptionPayment.isSome then Terms.prnxt ct else Terms.nt ct
    ipcb  := if t₀ < md then lamIpcb ct b.nt else 0 }

-- ---------------------------------------------------------------------------
-- Relational model
-- ---------------------------------------------------------------------------

/-- One-step LAM transition.  Constructors target the LAM dispatcher `stf`. -/
inductive Step (ct : Terms α) (rf : RiskFactorEnv α) : State α → State α → Type where
  | ev : ∀ {s : State α} (e : EventType) {t : Time}, s.sd ≤ t →
         Step ct rf s (stf ct rf e t s)

abbrev Trace (ct : Terms α) (rf : RiskFactorEnv α) := Star (Step ct rf)

def getCashflow (ct : Terms α) (rf : RiskFactorEnv α) {s s' : State α}
    (h : Step ct rf s s') : Event × α :=
  match h with
  | .ev e _ => ((s'.sd, e), pof ct rf e s'.sd s)

def getCashflows (ct : Terms α) (rf : RiskFactorEnv α) :
    ∀ {s s' : State α}, Trace ct rf s s' → List (Event × α)
  | _, _, .refl        => []
  | _, _, .step h rest => getCashflow ct rf h :: getCashflows ct rf rest

def LAM_contract : ActusContract := { Terms := Terms Float, State := State Float }

def LAM_impl (ct : Terms Float) (rf : RiskFactorEnv Float) (s₀ : State Float) :
    StateTransition LAM_contract :=
  { s₀ := s₀, rel := Step ct rf
    getCashflow := fun h r => let _ := r; getCashflow ct rf h }

end Actus.Contract.LAM
