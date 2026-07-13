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

/-- Structural placement of MODULE-LEVEL trivia with block-comment awareness:
    comment chunks (line comments; balanced `/- … -/` blocks INCLUDING their
    interior blank lines — comment text is content) ride byte-exact; the
    whitespace runs between chunks become structural separators (blank runs
    clamp to policy). `none` when the trivia has a shape no seam owns
    (a same-line head segment with content). -/
private def moduleTrivia?
    (lead : String)
    (atFileStart : Bool)
    : Option Doc := Id.run do
  let ls := lead.splitOn "\n"
  if ls.isEmpty then return some .nil
  -- head segment: remainder of the previous line (must be ws) — except at
  -- file start, where the first segment IS the first line of the file
  let mut i := 0
  if !atFileStart then
    if !(ls[0]!.toList.all (·.isWhitespace)) then return none
    i := 1
  let mut d : Doc := .nil
  let mut blanks := 0
  let mut sawAny := false
  let mut depth := 0
  let mut chunk : Array String := #[]
  let n := ls.length
  let flushChunk (d : Doc) (blanks : Nat) (sawAny : Bool) (chunk : Array String) : Doc :=
    if chunk.isEmpty then d
    else
      let sep : Doc :=
        if atFileStart && !sawAny then .nil
        else if blanks > 0 then .blank blanks else .hardline
      d ++ sep ++ .textRaw (String.intercalate "\n"
        (chunk.toList.map (fun l => l.trimAsciiEnd.toString)))
  while i < n do
    let l := ls[i]!
    let last := i + 1 == n
    let t := l.trimAscii.toString
    if depth > 0 then
      chunk := chunk.push l
      depth := depth + (t.splitOn "/-").length - 1 - ((t.splitOn "-/").length - 1)
    else if t.isEmpty then
      if last then
        -- tail segment: the form's own indentation — the renderer re-indents
        i := i + 1
        continue
      if !chunk.isEmpty then
        d := flushChunk d blanks sawAny chunk
        sawAny := true
        chunk := #[]
        blanks := 1   -- THIS blank line counts toward the next separator
      else
        blanks := blanks + 1
    else if t.startsWith "--" || t.startsWith "/-" then
      if !chunk.isEmpty && t.startsWith "/-" then
        d := flushChunk d blanks sawAny chunk
        sawAny := true
        chunk := #[]
        blanks := 0
      chunk := chunk.push (l.trimAsciiEnd.toString)
      if t.startsWith "/-" then
        depth := depth + (t.splitOn "/-").length - 1 - ((t.splitOn "-/").length - 1)
    else
      return none   -- content line that is not a comment: no seam owns it
    i := i + 1
  if depth != 0 then return none
  if !chunk.isEmpty then
    d := flushChunk d blanks sawAny chunk
    sawAny := true
    blanks := 0
  -- final separator before the form
  let finalSep : Doc :=
    if atFileStart && !sawAny then .nil
    else if blanks > 0 then .blank blanks else .hardline
  return some (d ++ finalSep)

/-- Drop the leftmost separator of a seam doc (the file head has no previous
    line — a leading hardline/blank would open the file with a stray newline). -/
private partial def dropLeadingSep : Doc → Doc
  | .cat a b => .cat (dropLeadingSep a) b
  | .hardline => .nil
  | .blank _ => .nil
  | d => d

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
  -- file-head leading (banner comments, blanks): structural under normalize —
  -- prepending a virtual newline makes the seam kit treat every banner line
  -- as a full line; the artificial first separator is dropped
  let fileHead (lead : String) : Doc :=
    if style.blankLines.policy == Lean4Fmt.Style.BlankPolicy.normalize then
      match moduleTrivia? lead (atFileStart := true) with
      | some d => d
      | none => .textRaw lead
    else .textRaw lead
  let mut acc : Doc := .nil
  let mut prev : Option (Lean.Syntax × Doc) := none   -- previous form + its body; trailing HELD
  let mut pendTrail : Doc := .nil
  match args[0]? with
  | some h =>
    let body ← match headerDoc? h with
      | some d => pure d
      | none => walk h
    acc := fileHead ((Lean4Fmt.Syntax.leading? h).getD "") ++ body
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
        let trailS := (Lean4Fmt.Syntax.trailing? p).getD ""
        let leadS := (Lean4Fmt.Syntax.leading? c).getD ""
        let gap := trailS ++ leadS
        let normalize := style.blankLines.policy == Lean4Fmt.Style.BlankPolicy.normalize
        if normalize && gap.toList.all (·.isWhitespace)
            && (gap.toList.filter (· == '\n')).length == 1 then
          acc := acc ++ .hardline ++ body
        else
          -- COMMENT-BEARING gap: canonicalize structurally — the prev form's
          -- same-line trailing comment re-appends, the full comment/blank
          -- lines place via the seam kit (T3: content-exact; blank runs clamp
          -- to the policy). Byte-exact only when no seam owns the shape.
          let trailT := trailS.trimAscii.toString
          let gapDoc? : Option Doc := Id.run do
            if !normalize then return none
            if trailS.any (· == '\n') then return none
            if trailT.startsWith "/-" && !trailT.startsWith "/--" then
              return none   -- same-line block comment: opaque
            let some sep := moduleTrivia? leadS (atFileStart := false)
              | return none
            let trailD : Doc := if trailT.isEmpty then .nil else .text (" " ++ trailT)
            return some (trailD ++ sep)
          match gapDoc? with
          | some g => acc := acc ++ g ++ body
          | none => acc := acc ++ pendTrail ++ Lean4Fmt.Emit.leadingRaw c ++ body
    | none =>
      acc := acc ++ fileHead ((Lean4Fmt.Syntax.leading? c).getD "") ++ body
    prev := some (c, body)
    pendTrail := Lean4Fmt.Emit.trailingRaw c
  return acc ++ pendTrail

end Lean4Fmt.Emit.Module
