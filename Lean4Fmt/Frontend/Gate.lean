/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // FRONTEND // GATE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The runtime safety gate (DESIGN_V2 §4.2): format, then keep the result only
    if it reparses, preserves the token stream, keeps imports in the header, and
    is a fixed point — otherwise emit the original unchanged. Never worse than
    input, on any file.

    Drives the v2 `Emit → Doc → Render` spine (`Lean4Fmt.Emit.format`), which on
    the continuity corpus is correctness-parity with v1 (0 mangled / 0
    non-idempotent, 100% token-preserving over 234 files) and strictly better on
    layout (roughly half v1's over-width lines; preserves doc comments v1 dropped).
    The gate contract is unchanged: keep the active output only if it reparses,
    preserves the token stream, keeps imports in the header, and is a fixed point.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import Lean4Fmt.Emit
import Lean4Fmt.Style
import Lean4Fmt.Rules
import Lean4Fmt.Frontend.Parse
import Lean4Fmt.Frontend.Session
import Lean4Fmt.Syntax.Query

namespace Lean4Fmt.Frontend

open Lean

/-- Parse a module against `env`, cheap path first: the fast `testParseModule`
    (no elaboration) handles the vast majority; only when it can't (a file whose
    own/imported notation needs elaboration to parse, e.g. `Type*`) do we pay for
    the interleaved elaborating frontend (`Session.parseModule?`, `full` depth).
    `env` is imported once per process by `formatFile`; both the source parse and
    the fixed-point reparse reuse it (re-importing per call is what breaks). -/
unsafe def parseFull? (env : Environment) (path contents : String) : IO (Option Lean.Syntax) := do
  match ← parseModule? env path contents with
  | some stx => pure (some stx)
  | none => Session.parseModule? env path contents

/-- The safety gate: return the text to emit — the actively-formatted output when
    it provably preserves meaning and is a fixed point, else the original — paired
    with the lint diagnostics for the source (the lint pass runs on the parsed
    syntax regardless of whether the reformat is kept). -/
unsafe def formatSafe (env : Environment) (path contents : String)
    (style : Lean4Fmt.Style.Style := Lean4Fmt.Style.default) :
    IO (String × Array Lean4Fmt.Rules.Diagnostic) := do
  match ← parseFull? env path contents with
  | none => pure (contents, #[])
  | some stx =>
    let diags := Lean4Fmt.Rules.lint stx
    let (active, _) := Lean4Fmt.Emit.format style stx.updateLeading
    if active == contents then pure (contents, diags)
    else match ← parseFull? env path active with
    | none => pure (contents, diags)
    | some stx2 =>
      let (active2, _) := Lean4Fmt.Emit.format style stx2.updateLeading
      let ok := Lean4Fmt.Syntax.leafToks stx == Lean4Fmt.Syntax.leafToks stx2  -- tokens preserved
            && headerToks stx == headerToks stx2                                -- imports in header
            && active2 == active                                                -- fixed point
      pure ((if ok then active else contents), diags)

/-- Build the environment for a file (loads its imports) and format it. -/
unsafe def formatFile (path contents : String)
    (style : Lean4Fmt.Style.Style := Lean4Fmt.Style.default) :
    IO (String × Array Lean4Fmt.Rules.Diagnostic) := do
  let ictx := Parser.mkInputContext contents path
  let (hdr, _, msgs) ← Parser.parseHeader ictx
  let (env, _) ← Elab.processHeader hdr {} msgs ictx (trustLevel := 1024)
  formatSafe env path contents style

end Lean4Fmt.Frontend
