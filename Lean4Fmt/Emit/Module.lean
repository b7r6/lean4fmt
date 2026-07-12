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

/-- Active layout for the module header: one `import X` line per import, the
    line reproduced token-for-token (trimmed, single-spaced — `public`/`meta`
    markers ride inside the import node's span), inter-import comment/blank
    lines placed structurally, same-line trailing comments re-appended. The
    FIRST import's leading is the header's outer leading (the file banner —
    `unit` places it byte-exact); the LAST import's trailing is the header's
    trailing, likewise. `none` (verbatim) on a `module`/`prelude` marker, a
    multi-line import span, or a seamless comment. -/
private def headerDoc?
            (h : Lean.Syntax)
            : Option Doc := Id.run do
  if h.getKind != ``Lean.Parser.Module.header then return none
  let a := h.getArgs
  if a.size != 3 then return none
  if !((a[0]?.map Lean4Fmt.Emit.bareSrc).getD "").trimAscii.toString.isEmpty then return none
  if !((a[1]?.map Lean4Fmt.Emit.bareSrc).getD "").trimAscii.toString.isEmpty then return none
  let imps := (a[2]?.map (·.getArgs)).getD #[]
  if imps.isEmpty then return none
  let mut acc : Doc := .nil
  for i in [0:imps.size] do
    let imp := imps[i]!
    let t := (Lean4Fmt.Emit.bareSrc imp).trimAscii.toString
    if t.isEmpty || t.any (· == '\n') then return none
    let last := i + 1 == imps.size
    let trailT := ((Lean4Fmt.Syntax.trailing? imp).getD "").trimAscii.toString
    if !last && trailT.any (· == '\n') then return none
    let trailDoc : Doc := if !last && !trailT.isEmpty then .text (" " ++ trailT) else .nil
    let sep : Doc ← do
      if i == 0 then pure Doc.nil   -- head leading = the file banner, placed by `unit`
      else match Lean4Fmt.Emit.leadingSep? ((Lean4Fmt.Syntax.leading? imp).getD "") with
        | some s => pure s
        | none => return none
    acc := acc ++ sep ++ .text t ++ trailDoc
  return some acc

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
def emit
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.EmitM Doc := do
  let args := stx.getArgs
  let unit (c : Lean.Syntax) : Lean4Fmt.Emit.EmitM Doc := do
    pure (Lean4Fmt.Emit.leadingRaw c ++ (← walk c) ++ Lean4Fmt.Emit.trailingRaw c)
  let mut acc : Doc := .nil
  match args[0]? with
  | some h =>
    match headerDoc? h with
    | some d => acc := Lean4Fmt.Emit.leadingRaw h ++ d ++ Lean4Fmt.Emit.trailingRaw h
    | none => acc := (← unit h)
  | none => pure ()
  let cmds := (args[1]?.map (·.getArgs)).getD #[]
  for c in cmds do
    if c.getKind == ``Lean.Parser.Command.eoi then continue
    acc := acc ++ (← unit c)
  return acc

end Lean4Fmt.Emit.Module
