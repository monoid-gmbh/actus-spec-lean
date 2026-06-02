/-
# ACTUS Formal Specification

Lean 4 formalization of the ACTUS technical specification.  Layers:

* `Actus.Protocol` — domain types (contract/event types, conventions, terms).
* `Actus.Abstract` / `Actus.Closures` — abstract contract interface + closures.
* `Actus.Util.*` — date arithmetic, conventions (sign/EOM/BDC), day-count
  year-fraction, schedule generation, annuity amount.
* `Actus.Contract.{PAM,LAM,NAM,ANN}` — the lending family, each with a relational
  `Step` model and an executable functional STF/POF model, sharing
  `Actus.Contract.Common`.
* `Actus.Contract.{Agree,Properties,Execution}` — relational↔functional
  agreement, metatheorems, and the schedule-driven cashflow pipeline.
* `Actus.Execution` — generic schedule-folding engine.
-/

import «Actus».Protocol
import «Actus».Closures
import «Actus».Abstract
import «Actus».Execution

-- Utility layer
import «Actus».Util.Date
import «Actus».Util.Conventions
import «Actus».Util.DayCount
import «Actus».Util.Schedule

-- Contract types
import «Actus».Contract.Common
import «Actus».Contract.PAM
import «Actus».Contract.LAM
import «Actus».Contract.NAM
import «Actus».Contract.ANN
import «Actus».Contract.CLM
import «Actus».Contract.Agree
import «Actus».Contract.Properties
import «Actus».Contract.Execution

-- JSON parser (actus-tests format) for the lending family
import «Actus».IO.Parse

-- Tests live in the separate `Test` library target (see `Test.lean`), kept out
-- of the documented API surface.
