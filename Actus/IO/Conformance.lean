/-
## Conformance harness

Reads the ACTUS Foundation reference test files (`actus-tests/actus-tests-*.json`)
from disk, runs each contract through the lending engine under its own observed
risk factors, and diffs the computed cashflows against the file's expected
`results`.

Run with:  `lake exe conformance [tests-dir]`  (default dir: `actus-tests`).

Comparison focuses on *monetary* cashflows: events with |payoff| ≤ tolerance
(IED-coincident interest, analysis events, bookkeeping markers) are dropped on
both sides before matching, so the report reflects real cash differences rather
than zero-valued schedule artifacts.  Events are matched by (event type, date);
payoffs must agree within a 1-cent tolerance.  Exits non-zero if any contract
in the lending family fails to match.
-/

import Actus.IO.Parse

open Lean (Json)
open Actus.Protocol
open Actus.Contract.Lending
open Actus.IO.Parse

namespace Actus.IO.Conformance

/-- A cashflow keyed by (time, event type). -/
abbrev CF := (Time × EventType) × Float

private def tol : Float := 0.01

private def sameKey (a b : Time × EventType) : Bool :=
  a.1 == b.1 && eventTypePriority a.2 == eventTypePriority b.2

private def keyStr (k : Time × EventType) : String := s!"{eventTypeToString k.2}@{k.1}"

private def isCash (c : CF) : Bool := Float.abs c.2 > tol

/-- Outcome of comparing one contract's computed vs expected cashflows. -/
structure Diff where
  matched  : Nat := 0
  mismatch : Array String := #[]
  missing  : Array String := #[]
  extra    : Array String := #[]

/-- Remove the first computed cashflow whose key matches `key`, returning its
    payoff and the rest. -/
private def popKey (key : Time × EventType) : List CF → Option (Float × List CF)
  | []      => none
  | c :: cs =>
    if sameKey c.1 key then some (c.2, cs)
    else (popKey key cs).map (fun (v, rest) => (v, c :: rest))

/-- Greedy key-matching diff of expected against computed cashflows. -/
private def diffCF : List CF → List CF → Diff → Diff
  | [], rem, d =>
      { d with extra := d.extra ++ (rem.map (fun c => s!"{keyStr c.1}={c.2}")).toArray }
  | e :: es, comp, d =>
    match popKey e.1 comp with
    | some (v, comp') =>
        let msg := s!"{keyStr e.1}: expected {e.2}, got {v}"
        let d := if Float.abs (v - e.2) ≤ tol then { d with matched := d.matched + 1 }
                 else { d with mismatch := d.mismatch.push msg }
        diffCF es comp' d
    | none => diffCF es comp { d with missing := d.missing.push s!"{keyStr e.1}={e.2}" }

private def toFP (s : String) : System.FilePath := s

/-- Tally: contracts seen / matched, expected cash events / matched. -/
structure Tally where
  contracts : Nat := 0
  pass      : Nat := 0
  events    : Nat := 0
  evMatched : Nat := 0

instance : Add Tally where
  add a b := { contracts := a.contracts + b.contracts, pass := a.pass + b.pass
               events := a.events + b.events, evMatched := a.evMatched + b.evMatched }

/-- Run one reference file. -/
private def runFile (dir : System.FilePath) (fname : String) : IO Tally := do
  let path := dir / (toFP fname)
  if !(← path.pathExists) then
    IO.println s!"  [skip] {fname}: not found"
    return {}
  let content ← IO.FS.readFile path
  match Json.parse content with
  | .error e => IO.println s!"  [error] {fname}: {e}"; return {}
  | .ok (.obj kvs) => do
    let mut total := 0
    let mut pass := 0
    let mut evTotal := 0
    let mut evMatched := 0
    for kv in kvs.toList do
      let id := kv.1
      match testCaseFromJson kv.2 with
      | .error e => total := total + 1; IO.println s!"    [{id}] parse error: {e}"
      | .ok tc =>
        total := total + 1
        let rf := (riskFactorsFromJson kv.2 tc.terms).toOption.getD {}
        let horizon := tc.to.map Actus.Contract.Lending.Execution.toTime
        let inHorizon := fun (t : Time) =>
          match horizon with | some h => t ≤ h | none => true
        let expected : List CF :=
          tc.events.filterMap fun ev =>
            let key := (Actus.Contract.Lending.Execution.toTime ev.time, ev.type)
            let c : CF := (key, ev.payoff)
            if isCash c && inHorizon key.1 then some c else none
        let computed : List CF :=
          (cashflowsOf tc.terms rf).filter (fun c => isCash c && inHorizon c.1.1)
        let d := diffCF expected computed {}
        evTotal := evTotal + expected.length
        evMatched := evMatched + d.matched
        if d.missing.isEmpty && d.mismatch.isEmpty && d.extra.isEmpty then
          pass := pass + 1
        else
          IO.println s!"    [FAIL {id}] matched {d.matched}/{expected.length} (mismatch {d.mismatch.size}, missing {d.missing.size}, extra {d.extra.size})"
          for m in d.mismatch.toList.take 3 do IO.println s!"        ≠ {m}"
          for m in d.missing.toList.take 2  do IO.println s!"        − {m}"
          for m in d.extra.toList.take 2    do IO.println s!"        + {m}"
    IO.println s!"  {fname}: {pass}/{total} contracts exact, {evMatched}/{evTotal} cash events match"
    return { contracts := total, pass := pass, events := evTotal, evMatched := evMatched }
  | .ok _ => IO.println s!"  [error] {fname}: top level is not an object"; return {}

end Actus.IO.Conformance

open Actus.IO.Conformance in
/-- Entry point (top-level `main` for the `conformance` executable). -/
def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.head?.getD "actus-tests"
  IO.println s!"ACTUS conformance — lending family (tolerance {tol})"
  IO.println s!"reading from: {dir}"
  let files := ["actus-tests-pam.json", "actus-tests-lam.json",
                "actus-tests-nam.json", "actus-tests-ann.json"]
  let mut g : Tally := {}
  for f in files do
    g := g + (← runFile dir f)
  IO.println s!"────────────────────────────────────────"
  IO.println s!"TOTAL: {g.pass}/{g.contracts} contracts exact, {g.evMatched}/{g.events} cash events match"
  return (if g.contracts > 0 && g.pass == g.contracts then 0 else 1)
