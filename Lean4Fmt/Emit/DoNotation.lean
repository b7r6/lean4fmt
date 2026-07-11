/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // EMIT // DoNotation
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Open-recursion emitter for the DoNotation category (DESIGN_V2 §11): the `do`
    block itself plus its binding statements (`doLet`, `doLetArrow`, `doReassign`,
    `doReassignArrow`, `doExpr` — their values walked so they lay out actively).

    The statement loop OWNS the inter-statement trivia (the seam model, §0.3):
    each statement's leading comment/blank lines are placed structurally before
    it (re-anchored to the statement indent), and a same-line trailing comment is
    re-appended after it — so a do-block with comments BETWEEN statements formats
    actively instead of forcing the whole value verbatim. A comment INSIDE a
    statement still reproduces that one statement verbatim (its span carries the
    comment). Everything else (`doIf`, `for`, pattern-arrow lets with an `| else`
    tail, …) reproduces verbatim, guarded by the safety gate so every
    intermediate state stays correct.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Emit.Monad

namespace Lean4Fmt.Emit.DoNotation

open Lean Lean4Fmt.Doc

/-- `x (: τ)? ← v` — the monadic-bind decl inside doLetArrow / doReassignArrow.
    The arrow atom is reproduced from source (`←` or `<-` — the token gate cares);
    the value inside the `doExpr` is walked, flat on the arrow line when it fits,
    else on the next line at +2. A `do` value glues to the arrow (its body brings
    its own hardline). `none` on any structural surprise or a value carrying a
    multi-line opaque block — the caller reproduces the whole statement verbatim. -/
private def idDeclDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (d : Lean.Syntax)
            : Lean4Fmt.Emit.EmitM (Option Doc) := do
  if d.getKind != ``Lean.Parser.Term.doIdDecl then return none
  let a := d.getArgs
  if a.size != 4 then return none
  let idT := (Lean4Fmt.Emit.bareSrc a[0]!).trimAscii.toString
  let tyT := (Lean4Fmt.Emit.bareSrc a[1]!).trimAscii.toString
  let arrowT := (Lean4Fmt.Emit.bareSrc a[2]!).trimAscii.toString
  let head := String.intercalate " " ([idT, tyT].filter (fun s => !s.isEmpty))
  if head.isEmpty || head.any (· == '\n') || arrowT.any (· == '\n') then return none
  let ex := a[3]!
  if ex.getKind != ``Lean.Parser.Term.doExpr then return none
  let some v := ex.getArgs[0]? | return none
  let vdoc ← walk v
  if Lean4Fmt.Doc.hasMultilineVerbatim vdoc then return none
  if v.getKind == ``Lean.Parser.Term.do then
    return some (.text head ++ .text (" " ++ arrowT ++ " ") ++ vdoc)
  return some (.text head ++ .text (" " ++ arrowT) ++ .group (.nest 2 (.line ++ vdoc)))

/-- Structural placement of a statement's leading trivia, as the separator doc
    that goes BEFORE the statement: each full line of the trivia is either a
    blank line (a `.blank` request, §8-clamped) or comment content (line or block
    comment — emitted `textRaw`, dedented by the run's minimum indent so relative
    offsets survive, re-anchored at the statement indent). Two partial lines are
    dropped: the HEAD segment before the first newline (the remainder of the
    previous token's line — its newline IS the separator; leading trivia starts
    before it, the previous trailing does not consume it) and the TAIL segment
    (the statement's own indentation — the renderer re-indents). Pure
    single-newline trivia degenerates to the plain `.hardline` separator.
    `none` when the head segment carries content (a comment the previous line's
    trailing did not capture — no seam for it here; the caller goes verbatim). -/
private def leadingSep?
            (lead : String)
            : Option Doc := Id.run do
  let ls := lead.splitOn "\n"
  let isWs (l : String) : Bool := l.all (fun c => c == ' ' || c == '\t')
  if !isWs (ls.headD "") then return none
  let full := (ls.drop 1).dropLast
  let content := full.filter (fun l => !isWs l)
  let indentOf (l : String) : Nat := (l.toList.takeWhile (· == ' ')).length
  let base := content.foldl (fun m l => Nat.min m (indentOf l)) 1000000
  let mut d : Doc := .nil
  let mut blanks := 0
  for l in full do
    if isWs l then blanks := blanks + 1
    else
      let ded := if l.length ≥ base then String.ofList (l.toList.drop base) else l
      d := d ++ (if blanks > 0 then .blank blanks else .hardline)
        ++ .textRaw ded.trimAsciiEnd.toString
      blanks := 0
  return some (d ++ (if blanks > 0 then .blank blanks else .hardline))

/-- Emit `do <seq>` — one statement per line indented by 2, leading comment/blank
    lines placed structurally, same-line trailing comments re-appended — or one of
    the binding statements (see module header). Only the plain `doSeqIndent` shape
    of `do` is handled; the bracketed `{ … }` shape and any structural surprise
    fall back to verbatim so no token (or comment) is dropped. -/
def emit
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.EmitM Doc := do
  let kind := stx.getKind
  let a := stx.getArgs
  if kind == ``Lean.Parser.Term.doLet || kind == ``Lean.Parser.Term.doLetArrow then
    -- `let (mut)? (config)? decl` = [let, mut?, letConfig, decl] where decl is a
    -- letDecl (`:=`, walked — Term handles the 5-slot shape) or a doIdDecl (`←`).
    -- The pattern-arrow form (doPatDecl, with its optional `| else` tail) stays
    -- verbatim. Only INTERIOR comments force verbatim — the statement's outer
    -- leading/trailing are the do-loop's to place.
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    if a.size != 4 then return (← Lean4Fmt.Emit.verbatim stx)
    let mutT := (Lean4Fmt.Emit.bareSrc a[1]!).trimAscii.toString
    let cfgT := (Lean4Fmt.Emit.bareSrc a[2]!).trimAscii.toString
    if mutT.any (· == '\n') || cfgT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let headD : Doc := .text "let " ++ (if mutT.isEmpty then .nil else .text (mutT ++ " "))
      ++ (if cfgT.isEmpty then .nil else .text (cfgT ++ " "))
    if kind == ``Lean.Parser.Term.doLet then
      let dDoc ← walk a[3]!
      if Lean4Fmt.Doc.hasMultilineVerbatim dDoc then return (← Lean4Fmt.Emit.verbatim stx)
      return headD ++ dDoc
    else
      match ← idDeclDoc? walk a[3]! with
      | some d => return headD ++ d
      | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == ``Lean.Parser.Term.doReassign then
    -- bare `x := v` = [letIdDeclNoBinders] — the inner decl IS the statement
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    let some inner := a[0]? | return (← Lean4Fmt.Emit.verbatim stx)
    let dDoc ← walk inner
    if Lean4Fmt.Doc.hasMultilineVerbatim dDoc then return (← Lean4Fmt.Emit.verbatim stx)
    return dDoc
  else if kind == ``Lean.Parser.Term.doReassignArrow then
    -- bare `x ← v` = [doIdDecl]
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    let some inner := a[0]? | return (← Lean4Fmt.Emit.verbatim stx)
    match ← idDeclDoc? walk inner with
    | some d => return d
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == ``Lean.Parser.Term.doReturn then
    -- `return` or `return v` = ["return", null(term?)] — the value is walked,
    -- flat on the return line when it fits, else on the next line at +2
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    match ((a[1]?.map (·.getArgs)).getD #[])[0]? with
    | none => return (Doc.text "return")
    | some v =>
      let vdoc ← walk v
      if Lean4Fmt.Doc.hasMultilineVerbatim vdoc then return (← Lean4Fmt.Emit.verbatim stx)
      return Doc.text "return" ++ .group (.nest 2 (.line ++ vdoc))
  else if kind == ``Lean.Parser.Term.doExpr then
    -- a plain expression statement: the term IS the statement
    match a[0]? with
    | some t => return (← walk t)
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind != ``Lean.Parser.Term.do then
    return (← Lean4Fmt.Emit.verbatim stx)
  else
  -- a comment on the `do` line itself (`do -- setup`) has no home in the layout
  let doKwTrail := ((Lean4Fmt.Syntax.trailing? (a[0]?.getD .missing)).getD "").trimAscii.toString
  if !doKwTrail.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
  let some seq := a[1]? | return (← Lean4Fmt.Emit.verbatim stx)
  if seq.getKind != ``Lean.Parser.Term.doSeqIndent then
    return (← Lean4Fmt.Emit.verbatim stx)
  let mut items : Array Lean.Syntax := #[]
  for g in seq.getArgs do
    for c in g.getArgs do
      if c.getKind == ``Lean.Parser.Term.doSeqItem then items := items.push c
  if items.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
  -- Guard: a doSeqItem with a non-empty terminator (explicit `;`) would lose that
  -- token if we walked only the statement — bail to verbatim for those.
  for it in items do
    let ia := it.getArgs
    if ia.size > 1 && !((Lean4Fmt.Emit.bareSrc (ia[ia.size-1]!)).trimAscii.toString.isEmpty) then
      return (← Lean4Fmt.Emit.verbatim stx)
  let mut body : Doc := .nil
  for h : i in [0:items.size] do
    let stmt := items[i].getArgs[0]?.getD .missing
    -- trailing comment (same line, `x := 1 -- note`). The LAST statement's
    -- trailing is the whole do's trailing — the enclosing seam owns it. A
    -- multi-line trailing (a block comment spanning lines) has no seam here.
    let trailT := ((Lean4Fmt.Syntax.trailing? stmt).getD "").trimAscii.toString
    let last := i + 1 == items.size
    if !last && trailT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let trailDoc : Doc := if !last && !trailT.isEmpty then .text (" " ++ trailT) else .nil
    let some sep := leadingSep? ((Lean4Fmt.Syntax.leading? stmt).getD "")
      | return (← Lean4Fmt.Emit.verbatim stx)
    let sDoc ← walk stmt
    body := body ++ sep ++ sDoc ++ trailDoc
  return .text "do" ++ .nest 2 body

end Lean4Fmt.Emit.DoNotation
