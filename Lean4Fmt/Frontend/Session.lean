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

namespace Lean4Fmt.Frontend.Session

/-- How much of a file to elaborate to keep parsing faithful (§14.7). -/
inductive ElabDepth
  | importsOnly       -- floor: load imports; enough for import-provided notation
  | tablesOnly        -- elaborate just far enough to extend parser tables (skip proofs)
  | full              -- fully elaborate (heaviest; always faithful)
  deriving Repr, Inhabited, BEq

/-- Placeholder: the interleaved parse+elaborate module parser that unblocks
    mathlib. To be implemented (§0.5). -/
def parseInterleaved? (_depth : ElabDepth) (_path _contents : String) : IO (Option Lean.Syntax) :=
  pure none  -- SCAFFOLD

end Lean4Fmt.Frontend.Session
