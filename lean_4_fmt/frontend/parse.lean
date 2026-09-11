/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // LEAN4FMT // FRONTEND // PARSE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    source → Environment → Syntax, quietly. Current impl uses `testParseModule`
    (the "floor", §0.5): sufficient for import-provided-notation trees, degrades
    to `none` on anything it can't parse (incl. mathlib's `Type*`). The
    interleaved parse+elaborate frontend that lifts the floor lives in
    `Frontend/Session` (§14.7) and is deferred with mathlib.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import lean_4_fmt.syntax.query

namespace Lean4Fmt.Frontend

open Lean

/-- Run an action with stdout redirected to a scratch buffer, so lenient parser
    diagnostics can never pollute our output. -/
def quietly {valueType} (act : IO valueType) : IO valueType := do
  let buf ← IO.mkRef { : IO.FS.Stream.Buffer }
  IO.withStdout (IO.FS.Stream.ofBuffer buf) act

/-- Parse a module quietly; `none` if it does not parse cleanly in `env`. -/
unsafe
def parse_module? (env : Environment) (path contents : String) : IO (Option Lean.Syntax) :=
  quietly do
    try
      let stx ← Parser.testParseModule env path contents
      if stx.hasMissing then pure none else pure (some stx)
    catch _ => pure none

/-- Import tokens of a module header (used to confirm imports stay at the top). -/
def header_toks (stx : Lean.Syntax) : Array String :=
  match stx.getArgs[0]? with
  | some headSyntax => Lean4Fmt.Syntax.leaf_toks headSyntax
  | none            => #[]

end Lean4Fmt.Frontend
