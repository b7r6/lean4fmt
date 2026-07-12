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

    Blank-line policy (`blankLines.policy = .normalize`): a PURE-WHITESPACE
    inter-form gap containing a newline, where either neighbor is a multi-line
    form, is replaced by exactly `blankLines.betweenTopLevelDecls` blank lines —
    the top-level rhythm is imposed, not preserved. Everything else stays
    byte-exact: gaps carrying comments (banners, section markers), same-line
    gaps, and gaps between single-line forms (runs of one-line defs keep their
    hand grouping). `.preserve` keeps every gap byte-exact. -/
def emit
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.EmitM Doc := do
  let style ← read
  let args := stx.getArgs
  -- multi-line form ⇢ participates in the imposed top-level rhythm. Decided
  -- from the EMITTED doc, not the source shape (a one-liner that the active
  -- layout breaks — or vice versa — must count as its OUTPUT shape, or the
  -- second pass disagrees with the first): flatWidth is exact (T2), so
  -- "fits the line width" is precisely "renders single-line" at indent 0.
  let multi (body : Doc) : Bool :=
    match Lean4Fmt.Doc.flatWidth body with
    | some w => w > style.layout.lineWidth
    | none => true
  -- normalizable gap: whitespace-only, has a newline, a multi-line neighbor
  let gapOk (p c : Lean.Syntax) (pBody cBody : Doc) : Bool := Id.run do
    if style.blankLines.policy != Lean4Fmt.Style.BlankPolicy.normalize then
      return false
    let gap := ((Lean4Fmt.Syntax.trailing? p).getD "")
      ++ ((Lean4Fmt.Syntax.leading? c).getD "")
    let nls := (gap.toList.filter (· == '\n')).length
    return gap.toList.all (·.isWhitespace) && nls ≥ 1
      && (multi pBody || multi cBody || nls ≥ 2)
  let mut acc : Doc := .nil
  let mut prev : Option (Lean.Syntax × Doc) := none   -- previous form + its body; trailing HELD
  let mut pendTrail : Doc := .nil
  match args[0]? with
  | some h =>
    let body ← match headerDoc? h with
      | some d => pure d
      | none => walk h
    acc := Lean4Fmt.Emit.leadingRaw h ++ body
    prev := some (h, body)
    pendTrail := Lean4Fmt.Emit.trailingRaw h
  | none => pure ()
  let cmds := (args[1]?.map (·.getArgs)).getD #[]
  for c in cmds do
    if c.getKind == ``Lean.Parser.Command.eoi then continue
    let body ← walk c
    match prev with
    | some (p, pBody) =>
      if gapOk p c pBody body then
        -- swallow prev trailing + c leading (both pure ws): impose the rhythm
        acc := acc ++ .blank style.blankLines.betweenTopLevelDecls ++ body
      else
        -- adjacent ONE-LINER pair (ws-only gap, no blank line): adjacency is
        -- content, but the gap bytes canonicalize to a single newline
        let gap := ((Lean4Fmt.Syntax.trailing? p).getD "")
          ++ ((Lean4Fmt.Syntax.leading? c).getD "")
        if style.blankLines.policy == Lean4Fmt.Style.BlankPolicy.normalize
            && gap.toList.all (·.isWhitespace)
            && (gap.toList.filter (· == '\n')).length == 1 then
          acc := acc ++ .hardline ++ body
        else
          acc := acc ++ pendTrail ++ Lean4Fmt.Emit.leadingRaw c ++ body
    | none =>
      acc := acc ++ Lean4Fmt.Emit.leadingRaw c ++ body
    prev := some (c, body)
    pendTrail := Lean4Fmt.Emit.trailingRaw c
  return acc ++ pendTrail

end Lean4Fmt.Emit.Module
