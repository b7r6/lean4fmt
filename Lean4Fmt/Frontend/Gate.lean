/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // FRONTEND // GATE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The runtime safety gate (DESIGN_V2 §4.2): format, then keep the result only
    if it reparses, preserves the token stream, keeps imports in the header, and
    is a fixed point — otherwise emit the original unchanged. Never worse than
    input, on any file.

    Currently drives the v1 emitter (`Lean4Fmt.format`), which is at behavioural
    parity on the continuity corpus. It switches to the v2 `Emit → Doc → Render`
    spine (`Lean4Fmt.Emit.format`) once that reaches parity — the gate contract
    is unchanged by the swap.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import Lean4Fmt.Emitter
import Lean4Fmt.Frontend.Parse
import Lean4Fmt.Syntax.Query

namespace Lean4Fmt.Frontend

open Lean

/-- The safety gate: return the text to emit — the actively-formatted output when
    it provably preserves meaning and is a fixed point, else the original. -/
unsafe def formatSafe (env : Environment) (path contents : String)
    (cfg : StyleConfig := {}) : IO String := do
  match ← parseModule? env path contents with
  | none => pure contents
  | some stx =>
    let (active, _) := Lean4Fmt.format stx.updateLeading cfg
    if active == contents then pure contents
    else match ← parseModule? env path active with
    | none => pure contents
    | some stx2 =>
      let (active2, _) := Lean4Fmt.format stx2.updateLeading cfg
      let ok := Lean4Fmt.Syntax.leafToks stx == Lean4Fmt.Syntax.leafToks stx2  -- tokens preserved
            && headerToks stx == headerToks stx2                                -- imports in header
            && active2 == active                                                -- fixed point
      pure (if ok then active else contents)

/-- Build the environment for a file (loads its imports) and format it. -/
unsafe def formatFile (path contents : String) (cfg : StyleConfig := {}) : IO String := do
  let ictx := Parser.mkInputContext contents path
  let (hdr, _, msgs) ← Parser.parseHeader ictx
  let (env, _) ← Elab.processHeader hdr {} msgs ictx (trustLevel := 1024)
  formatSafe env path contents cfg

end Lean4Fmt.Frontend
