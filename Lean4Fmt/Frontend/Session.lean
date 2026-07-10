/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // LEAN4FMT // FRONTEND // SESSION
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    THE OPEN QUESTION (DESIGN_V2 §0.5, §14.7): formatting requires running the
    elaborator over some — as-yet-undetermined — portion of the full artifact,
    because a file's own syntax is extended as it elaborates (notation / macro /
    scoped / open register parser tables; `Type*` only exists post-elaboration).

    The command-loop parser with hand-tracked scope was proven insufficient
    (251/319 commands missing on Mathlib/Logic/Basic). The real path is the
    interleaved parse+elaborate frontend (à la `Lean.Elab.Frontend`), collecting
    each command's `Syntax` as it is elaborated far enough to keep the tables
    current.

    This module will own:
      • the interleaved loop (parse → elaborate-enough → collect syntax),
      • the "how little elaboration" strategy (§14.7: skip proof bodies? a
        parser-tables-only fast path? a per-file budget?),
      • the parse-parallelism strategy (§12: superset-env vs process-per-file).

    Deferred with mathlib. SCAFFOLD ONLY.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import Lean4Fmt.Frontend.Parse

namespace Lean4Fmt.Frontend.Session

open Lean

/-- How much of a file to elaborate to keep parsing faithful (§14.7). -/
inductive ElabDepth
  | importsOnly       -- floor: load imports; enough for import-provided notation
  | tablesOnly        -- elaborate just far enough to extend parser tables (skip proofs)
  | full              -- fully elaborate (heaviest; always faithful)
  deriving Repr, Inhabited, BEq

/-- Interleaved parse+elaborate a module against an already-imported `env`: run the
    real frontend (`Lean.Elab.IO.processCommands`), which parses each command with
    the current parser tables and elaborates it far enough to extend them before
    parsing the next — so notation/macros a file introduces (and import-provided
    forms like `Type*`) parse faithfully. Returns a reconstructed `Module.module`
    node `[header, commands]` for the emitter, or `none` if anything is missing.

    This is the `full` depth. It is CPU-heavy (elaborates proof bodies too); the
    caller (`parseFull?`) only reaches it when the cheap parser can't. `tablesOnly`
    (skip proofs) is the planned optimization; the thread pool (Driver.Pool) is the
    planned throughput lever (§12). The env must already be built (imports loaded)
    ONCE per process — re-importing per call is what breaks in-process reuse. -/
unsafe def parseModule? (env : Environment) (path contents : String) : IO (Option Lean.Syntax) := do
  let ictx := Parser.mkInputContext contents path
  let (hdr, mps, msgs) ← Parser.parseHeader ictx
  quietly do
    try
      let s ← Lean.Elab.IO.processCommands ictx mps (Lean.Elab.Command.mkState env msgs {})
      if s.commands.any (·.hasMissing) then pure none
      else pure (some (Syntax.node .none ``Lean.Parser.Module.module #[hdr, mkNullNode s.commands]))
    catch _ => pure none

end Lean4Fmt.Frontend.Session
