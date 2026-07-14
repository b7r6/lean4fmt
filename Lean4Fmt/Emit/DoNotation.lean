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
import Lean4Fmt.Emit.Tokens

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

/-- The statements of a plain `doSeqIndent`, provided no item carries an explicit
    `;` terminator (walking only the statement would lose that token). `none` on
    the bracketed `{ … }` shape or any structural surprise. -/
private def stmts?
            (seq : Lean.Syntax)
            : Option (Array Lean.Syntax) := Id.run do
  if seq.getKind != ``Lean.Parser.Term.doSeqIndent then return none
  let mut items : Array Lean.Syntax := #[]
  for g in seq.getArgs do
    for c in g.getArgs do
      if c.getKind == ``Lean.Parser.Term.doSeqItem then items := items.push c
  if items.isEmpty then return none
  for it in items do
    let ia := it.getArgs
    if ia.size > 1 && !((Lean4Fmt.Emit.bareSrc (ia[ia.size-1]!)).trimAscii.toString.isEmpty) then
      return none
  return some (items.map (fun it => it.getArgs[0]?.getD Lean.Syntax.missing))

/-- The statement LINES of a sequence: each statement preceded by its structural
    leading (comments/blanks — `leadingSep?`) and followed by its same-line
    trailing comment. `lastOwned`: when true, the LAST statement's trailing
    belongs to the enclosing seam and is skipped (a whole `do`, whose do-loop
    caller re-appends it; a final if-branch, whose statement seam follows); when
    false there is NO seam for it (a then-branch before `else`) — any content
    there aborts to `none`. -/
def seqLinesDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (ss : Array Lean.Syntax)
            (lastOwned : Bool)
            : Lean4Fmt.Emit.EmitM (Option Doc) := do
  let mut body : Doc := .nil
  for h : i in [0:ss.size] do
    let stmt := ss[i]
    let trailT := ((Lean4Fmt.Syntax.trailing? stmt).getD "").trimAscii.toString
    let last := i + 1 == ss.size
    if !last && trailT.any (· == '\n') then return none
    if last && !lastOwned && !trailT.isEmpty then return none
    let trailDoc : Doc := if !last && !trailT.isEmpty then .text (" " ++ trailT) else .nil
    let some sep := Lean4Fmt.Emit.leadingSep? ((Lean4Fmt.Syntax.leading? stmt).getD "") | return none
    let sDoc ← walk stmt
    body := body ++ sep ++ sDoc ++ trailDoc
  return some body

/-- A nested statement sequence (an if-branch), placed directly after its keyword:
    a single clean statement (no comment/blank lines above it, no trailing
    comment, flattenable) becomes a width-aware `group` — inline when it fits
    (`if c then return 1`), else on its own line at +2; anything else goes one
    statement per line at +2. `none` when the sequence has no safe layout. -/
private def branchDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (seq : Lean.Syntax)
            (lastOwned : Bool)
            : Lean4Fmt.Emit.EmitM (Option Doc) := do
  let some ss := stmts? seq | return none
  if ss.size == 1 then
    let lead := (Lean4Fmt.Syntax.leading? ss[0]!).getD ""
    let plainLead := ((lead.splitOn "\n").drop 1).dropLast.isEmpty
    let srcInline := !lead.any (· == '\n')
    let trailT := ((Lean4Fmt.Syntax.trailing? ss[0]!).getD "").trimAscii.toString
    if plainLead && (lastOwned || trailT.isEmpty)
        && (!(← read).breaking.preserveLineBreaks || srcInline) then
      let sDoc ← walk ss[0]!
      if (Lean4Fmt.Doc.flatWidth sDoc).isSome && !Lean4Fmt.Doc.hasMultilineVerbatim sDoc then
        return some (.group (.nest 2 (.line ++ sDoc)))
  match ← seqLinesDoc? walk ss lastOwned with
  | some body => return some (.nest 2 body)
  | none => return none

/-- Emit `do <seq>` — one statement per line indented by 2, leading comment/blank
    lines placed structurally, same-line trailing comments re-appended — or one of
    the binding statements (see module header). Only the plain `doSeqIndent` shape
    of `do` is handled; the bracketed `{ … }` shape and any structural surprise
    fall back to verbatim so no token (or comment) is dropped. -/
def emit
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.EmitM Doc := do
  -- preserveLineBreaks: a single-line do-statement is byte-exact (the
  -- author's `let x: T ← …` spacing survives); the do BLOCK itself and
  -- multi-line statements stay structural
  if (← read).breaking.preserveLineBreaks && stx.getKind != ``Lean.Parser.Term.do then
    let t := Lean4Fmt.Emit.bareSrc stx
    if !t.isEmpty && !t.any (· == '\n') then return .text t

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
  else if kind == ``Lean.Parser.Term.doIf then
    -- [if, cond, then, seq, (else-if group)*, else?]. Conditions (doIfProp /
    -- if-let, with an optional `h :` binder) are reproduced token-for-token,
    -- single-line. Every line comment must live INSIDE one of the branch
    -- sequences (the accounting below) — a comment around a keyword or in a
    -- condition has no seam here and forces verbatim. Only the FINAL branch may
    -- end in a trailing comment (the statement seam follows it); a comment
    -- before an `else` has no seam.
    if a.size != 6 then return (← Lean4Fmt.Emit.verbatim stx)
    let condT := (Lean4Fmt.Emit.bareSrc a[1]!).trimAscii.toString
    if condT.isEmpty || condT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let mut branches : Array (String × Lean.Syntax) := #[("if " ++ condT ++ " then", a[3]!)]
    for g in a[4]!.getArgs do
      let ga := g.getArgs
      if ga.size != 4 then return (← Lean4Fmt.Emit.verbatim stx)
      let cT := (Lean4Fmt.Emit.bareSrc ga[1]!).trimAscii.toString
      if cT.isEmpty || cT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
      branches := branches.push ("else if " ++ cT ++ " then", ga[3]!)
    let elseArgs := a[5]!.getArgs
    if !elseArgs.isEmpty then
      if elseArgs.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
      branches := branches.push ("else", elseArgs[1]!)
    -- comments only inside branch seqs (the statement's own leading is the
    -- do-loop's and exempt; its trailing is inside the final seq's count)
    let seqCmts := branches.foldl
      (fun n b => n + Lean4Fmt.Syntax.countSubtreeLineComments b.2) 0
    let ownLead := Lean4Fmt.Syntax.countLineComments ((Lean4Fmt.Syntax.leading? stx).getD "")
    if Lean4Fmt.Syntax.countSubtreeLineComments stx != seqCmts + ownLead then
      return (← Lean4Fmt.Emit.verbatim stx)
    let mut d : Doc := .nil
    for h : i in [0:branches.size] do
      let (kw, seq) := branches[i]
      let some bD ← branchDoc? walk seq (i + 1 == branches.size)
        | return (← Lean4Fmt.Emit.verbatim stx)
      d := d ++ (if i == 0 then Doc.nil else .hardline) ++ .text kw ++ bD
    return d
  else if kind == ``Lean.Parser.Term.doMatch then
    -- [match, generalizing?, motive?, ?, discrs, "with", matchAlts] — the head
    -- `match <discrs> with` reproduced token-for-token, single-line; each arm
    -- `| pat =>` with its doSeq body via branchDoc? (inline when a single clean
    -- statement fits). Seam accounting as for doIf: every line comment must sit
    -- inside an arm's sequence; only the FINAL arm may end in a trailing
    -- comment (the statement seam follows it).
    if a.size != 7 then return (← Lean4Fmt.Emit.verbatim stx)
    let midParts := ((a.extract 1 5).map
      (fun s => Lean4Fmt.Emit.canonTok s)).filter (fun s => !s.isEmpty)
    let head := "match " ++ String.intercalate " " midParts.toList ++ " with"
    if head.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let mut alts : Array Lean.Syntax := #[]
    for g in a[6]!.getArgs do
      for c in g.getArgs do
        if c.getKind == ``Lean.Parser.Term.matchAlt then alts := alts.push c
    if alts.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
    for alt in alts do
      if alt.getArgs.size != 4 then return (← Lean4Fmt.Emit.verbatim stx)
    let seqCmts := alts.foldl
      (fun n alt => n + Lean4Fmt.Syntax.countSubtreeLineComments (alt.getArgs[3]!)) 0
    let ownLead := Lean4Fmt.Syntax.countLineComments ((Lean4Fmt.Syntax.leading? stx).getD "")
    if Lean4Fmt.Syntax.countSubtreeLineComments stx != seqCmts + ownLead then
      return (← Lean4Fmt.Emit.verbatim stx)
    let mut d : Doc := .text head
    for h : i in [0:alts.size] do
      let aa := alts[i].getArgs
      let patDoc ← walk aa[1]!
      if Lean4Fmt.Doc.hasMultilineVerbatim patDoc then return (← Lean4Fmt.Emit.verbatim stx)
      let some bD ← branchDoc? walk aa[3]! (i + 1 == alts.size)
        | return (← Lean4Fmt.Emit.verbatim stx)
      let armSrc := (Lean4Fmt.Emit.bareSrc alts[i]).trimAscii.toString
      let armD : Doc :=
        if (← read).breaking.preserveLineBreaks && !armSrc.isEmpty
            && !armSrc.any (· == '\n') then
          .text armSrc
        else .text "| " ++ patDoc ++ .text " =>" ++ bD
      d := d ++ .hardline ++ armD
    return d
  else if kind == ``Lean.Parser.Term.doFor || kind == `Lean.Parser.Term.doWhile
      || kind == `Lean.Parser.Term.doUnless then
    -- `for x in xs do` / `while c do` / `unless c do` — head tokens
    -- single-line (canonically respaced), the body sequence one statement
    -- per line at +2 with the seam loop owning inter-statement trivia
    if a.size < 2 then return (← Lean4Fmt.Emit.verbatim stx)
    let mut head := ""
    for c in a.extract 0 (a.size - 1) do
      if Lean4Fmt.Syntax.countSubtreeLineComments c > 0 then
        return (← Lean4Fmt.Emit.verbatim stx)
      let t := Lean4Fmt.Emit.canonTok c
      if t.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
      if !t.isEmpty then head := if head.isEmpty then t else head ++ " " ++ t
    if head.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
    let some ss := stmts? a[a.size - 1]! | return (← Lean4Fmt.Emit.verbatim stx)
    match ← seqLinesDoc? walk ss true with
    | some body => return .text head ++ .nest 2 body
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind != ``Lean.Parser.Term.do && kind != ``Lean.Parser.Term.doNested then
    return (← Lean4Fmt.Emit.verbatim stx)
  else
  -- a comment on the `do` line itself (`do -- setup`) has no home in the layout
  let doKwTrail := ((Lean4Fmt.Syntax.trailing? (a[0]?.getD .missing)).getD "").trimAscii.toString
  if !doKwTrail.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
  let some seq := a[1]? | return (← Lean4Fmt.Emit.verbatim stx)
  let some ss := stmts? seq | return (← Lean4Fmt.Emit.verbatim stx)
  -- trailing comments per statement placed by the loop; the LAST statement's
  -- trailing is the whole do's trailing — the enclosing seam owns it
  match ← seqLinesDoc? walk ss true with
  | some body => return .text "do" ++ .nest 2 body
  | none => return (← Lean4Fmt.Emit.verbatim stx)

end Lean4Fmt.Emit.DoNotation
