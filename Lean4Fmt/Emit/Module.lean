/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // EMIT // MODULE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Header + per-command dispatch. THIS is the passthrough seam: each top-level
    command is independently routed through `walk` — a handled kind (e.g. a
    declaration) is actively formatted, everything else is reproduced verbatim,
    with byte-exact tiling of leading trivia. Per-top-level-form granularity.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Emit.Monad

namespace Lean4Fmt.Emit.Module

open Lean Lean4Fmt.Doc

/-- Emit a whole module: each form (header + commands) as
    `leading ++ walk(bare) ++ trailing`. Since leading[next] and trailing[prev]
    partition the inter-form gap exactly, forms tile byte-exactly — handled kinds
    are actively formatted, the rest reproduced verbatim. Per-form granularity.

    Note (blank-line policy): inter-form trivia is emitted BYTE-EXACT, so
    `Style.blankLines` (normalize / betweenTopLevelDecls / maxConsecutive) is not
    applied here — straylight's `.normalize` currently behaves as `.preserve`
    (verified: straylight and mathlib presets produce identical output; 17/234
    corpus files carry >1 consecutive blank line). This is deliberate: blank runs
    can sit INSIDE block comments (e.g. `/- … -/` banners), and the safety gate
    (§4.2) validates tokens/reparse/fixed-point but NOT comment content — so a
    trivia rewrite that touched a comment interior would escape the gate. Applying
    the policy safely requires clamping only whitespace-region blanks (comment-
    aware) and is deferred until that can be done without risking comment/banner
    content. -/
def emit (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.EmitM Doc := do
  let args := stx.getArgs
  let unit (c : Lean.Syntax) : Lean4Fmt.Emit.EmitM Doc := do
    pure (Lean4Fmt.Emit.leadingRaw c ++ (← walk c) ++ Lean4Fmt.Emit.trailingRaw c)
  let mut acc : Doc := .nil
  match args[0]? with
  | some h => acc := (← unit h)
  | none => pure ()
  let cmds := (args[1]?.map (·.getArgs)).getD #[]
  for c in cmds do
    if c.getKind == ``Lean.Parser.Command.eoi then continue
    acc := acc ++ (← unit c)
  return acc

end Lean4Fmt.Emit.Module
