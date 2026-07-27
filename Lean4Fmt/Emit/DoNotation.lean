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
private
def id_decl_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (d : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let a := d.getArgs
  -- doIdDecl = [id, type?, "←", doExpr]; doPatDecl = [pat, type?, "←",
  -- doExpr, else?] — same arrow/expr slots; the pattern joins flat and the
  -- optional `| else` tail bails
  let head ← do
    if d.getKind == ``Lean.Parser.Term.doIdDecl then
      if a.size != 4 then return none
      let idT := Lean4Fmt.Emit.canon_tok a[0]!
      let tyT := Lean4Fmt.Emit.canon_tok a[1]!
      pure (String.intercalate " " ([idT, tyT].filter (fun s => !s.isEmpty)))
    else if d.getKind == ``Lean.Parser.Term.doPatDecl then
      if a.size != 5 then return none
      if !((a[4]?.map (fun s =>
          (Lean4Fmt.Emit.bare_src s).trimAscii.toString.isEmpty)).getD true) then
        return none
      let patT := Lean4Fmt.Emit.canon_tok a[0]!
      let tyT := Lean4Fmt.Emit.canon_tok a[1]!
      pure (String.intercalate " " ([patT, tyT].filter (fun s => !s.isEmpty)))
    else return none
  let arrowT := (Lean4Fmt.Emit.bare_src a[2]!).trimAscii.toString
  if head.isEmpty || head.any (· == '\n') || arrowT.any (· == '\n') then
    return none
  let ex := a[3]!
  if ex.getKind != ``Lean.Parser.Term.doExpr then
    return none
  let some v := ex.getArgs[0]? | return none
  let vdoc ← walk v
  -- a bare whole-verbatim value gains nothing; otherwise the ASSEMBLED
  -- layout decides (hasMidlineReanchor — interior verbatims at hardline
  -- seams re-anchor deterministically): a do/by/match value GLUES to the
  -- arrow (its members bring their own hardlines — `let x ← match e with`
  -- + arms below, the ApplyFun shape), anything else width-aware at +2
  if (match vdoc with | .verbatim _ _ => true | _ => false) then return none
  -- ANY multi-line value glues (`x ← cachedBuild args do`, `x ← match e
  -- with` — the house shape hangs the value head on the arrow line; its own
  -- doc breaks below); a FLAT value keeps the width-aware group (inline
  -- when it fits, else own line at +2 — unchanged)
  let glue := v.getKind == ``Lean.Parser.Term.do
    || v.getKind == ``Lean.Parser.Term.byTactic
    || v.getKind == ``Lean.Parser.Term.match
    || (Lean4Fmt.Doc.flat_width vdoc).isNone
  let layout : Doc :=
    if glue then .text head ++ .text (" " ++ arrowT ++ " ") ++ vdoc
    else .text head ++ .text (" " ++ arrowT) ++ .group (.nest 2 (.line ++ vdoc))
  if Lean4Fmt.Doc.has_midline_reanchor layout then return none
  return some layout

/-- The statements of a plain `doSeqIndent`, provided no item carries an explicit
    `;` terminator (walking only the statement would lose that token). `none` on
    the bracketed `{ … }` shape or any structural surprise. -/
private
def stmts? (seq : Lean.Syntax) : Option (Array Lean.Syntax) :=
  Id.run do
    if seq.getKind != ``Lean.Parser.Term.doSeqIndent then
      return none
    let mut items : Array Lean.Syntax := #[]
    for g in seq.getArgs do
      for c in g.getArgs do
        if c.getKind == ``Lean.Parser.Term.doSeqItem then items := items.push c
    if items.isEmpty then
      return none
    for it in items do
      let ia := it.getArgs
      if ia.size > 1 && !((Lean4Fmt.Emit.bare_src (ia[ia.size-1]!)).trimAscii.toString.isEmpty) then
        return none
    return some (items.map (fun it => it.getArgs[0]?.getD Lean.Syntax.missing))

/-- The statement LINES of a sequence: each statement preceded by its structural
    leading (comments/blanks — `leadingSep?`) and followed by its same-line
    trailing comment. `lastOwned`: when true, the LAST statement's trailing
    belongs to the enclosing seam and is skipped (a whole `do`, whose do-loop
    caller re-appends it; a final if-branch, whose statement seam follows); when
    false there is NO seam for it (a then-branch before `else`) — any content
    there aborts to `none`. -/
def seq_lines_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (ss : Array Lean.Syntax)
    (lastOwned : Bool)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let mut body : Doc := .nil
  for h : idx in [0:ss.size] do
    let stmt := ss[idx]
    let trailT := ((Lean4Fmt.Syntax.trailing? stmt).getD "").trimAscii.toString
    let last := idx + 1 == ss.size
    if !last && trailT.any (· == '\n') then
      return none
    if last && !lastOwned && !trailT.isEmpty then
      return none
    let trailDoc : Doc := if !last && !trailT.isEmpty then .text (" " ++ trailT) else .nil
    let lead := (Lean4Fmt.Syntax.leading? stmt).getD ""
    -- FIRST statement: a comment-free blank run between the block opener and
    -- the first statement is LAYOUT, not content — drop it and let the style
    -- re-add its own (bodyOwnLine/glueBodyBlank). Without this, one style's
    -- injected blank reads as content to the next (the wash-test leak).
    let sep ← if idx == 0 && lead.toList.all (·.isWhitespace) then pure Doc.hardline
      else match Lean4Fmt.Emit.leading_sep? lead with
        | some s => pure s
        | none => return none
    let sDoc ← walk stmt
    body := body ++ sep ++ sDoc ++ trailDoc
  return some body

/-- A nested statement sequence (an if-branch), placed directly after its keyword:
    a single clean statement (no comment/blank lines above it, no trailing
    comment, flattenable) becomes a width-aware `group` — inline when it fits
    (`if c then return 1`), else on its own line at +2; anything else goes one
    statement per line at +2. `none` when the sequence has no safe layout. -/
private
def branch_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (seq : Lean.Syntax)
    (lastOwned : Bool)
    (guardBreak : Bool := false)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let some ss := stmts? seq | return none
  if ss.size == 1 then
    let lead := (Lean4Fmt.Syntax.leading? ss[0]!).getD ""
    let plainLead := ((lead.splitOn "\n").drop 1).dropLast.isEmpty
    let srcInline := !lead.any (· == '\n')
    let trailT := ((Lean4Fmt.Syntax.trailing? ss[0]!).getD "").trimAscii.toString
    if plainLead && (lastOwned || trailT.isEmpty)
        && (!(← read).breaking.preserveLineBreaks || srcInline) then
      let sDoc ← walk ss[0]!
      -- guardIfOwnLine: a CONTROL-FLOW branch (`return`/`throw`) keeps its
      -- own line even when it fits — the guard ladder reads vertically;
      -- effect branches still inline by width (the house distinction)
      let isCtl := ss[0]!.getKind == ``Lean.Parser.Term.doReturn
        || ((Lean4Fmt.Emit.bare_src ss[0]!).trimAscii.toString.startsWith "throw")
      if (← read).breaking.inlineBranches
          && !(guardBreak && isCtl)
          && (Lean4Fmt.Doc.flat_width sDoc).isSome
          && !Lean4Fmt.Doc.hasMultilineVerbatim sDoc then
        return some (.group (.nest 2 (.line ++ sDoc)))
      -- a nested `do` GLUES to the branch keyword (`=> do` / `then do`) —
      -- its statements bring their own hardlines (mirrors the eqns arm rule;
      -- without this the `do` lands alone on its own line)
      let k := ss[0]!.getKind
      if !Lean4Fmt.Doc.hasMultilineVerbatim sDoc
          && (k == ``Lean.Parser.Term.doNested
            || (k == ``Lean.Parser.Term.doExpr
              && (ss[0]!.getArgs[0]?.map (·.getKind)) == some ``Lean.Parser.Term.do)) then
        return some (.text " " ++ sDoc)
  match ← seq_lines_doc? walk ss lastOwned with
  | some body => return some (.nest 2 body)
  | none => return none

/-- Emit `do <seq>` — one statement per line indented by 2, leading comment/blank
    lines placed structurally, same-line trailing comments re-appended — or one of
    the binding statements (see module header). Only the plain `doSeqIndent` shape
    of `do` is handled; the bracketed `{ … }` shape and any structural surprise
    fall back to verbatim so no token (or comment) is dropped. -/
private
def emit_let (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let a := stx.getArgs
  -- `let (mut)? (config)? decl` = [let, mut?, letConfig, decl] where decl is a
  -- letDecl (`:=`, walked — Term handles the 5-slot shape), a doIdDecl (`←`),
  -- or a doPatDecl (`pat ←`; its optional `| else` tail bails inside
  -- idDeclDoc?). Only INTERIOR comments force verbatim — the statement's
  -- outer leading/trailing are the do-loop's to place.
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← Lean4Fmt.Emit.verbatim stx)
  if a.size != 4 then
    return (← Lean4Fmt.Emit.verbatim stx)
  let mutT := (Lean4Fmt.Emit.bare_src a[1]!).trimAscii.toString
  let cfgT := (Lean4Fmt.Emit.bare_src a[2]!).trimAscii.toString
  if mutT.any (· == '\n') || cfgT.any (· == '\n') then
    return (← Lean4Fmt.Emit.verbatim stx)
  let headD : Doc :=
    .text "let " ++ (if mutT.isEmpty then .nil else .text (mutT ++ " "))
        ++ (if cfgT.isEmpty then .nil else .text (cfgT ++ " "))
  if stx.getKind == ``Lean.Parser.Term.doLet then
    let dDoc ← walk a[3]!
    if Lean4Fmt.Doc.hasMultilineVerbatim dDoc then
      return (← Lean4Fmt.Emit.verbatim stx)
    return headD ++ dDoc
  else
    match ← id_decl_doc? walk a[3]! with
    | some d => return headD ++ d
    | none => return (← Lean4Fmt.Emit.verbatim stx)

private
def is_verbatim_doc : Doc → Bool
  | .verbatim _ _ => true
  | _             => false

private
def let_else_head? (args : Array Lean.Syntax) : Option String := do
  if args.size != 9 then none
  let mutToken := (Lean4Fmt.Emit.bare_src args[1]!).trimAscii.toString
  let configToken := (Lean4Fmt.Emit.bare_src args[2]!).trimAscii.toString
  let patternToken := Lean4Fmt.Emit.canon_tok args[3]!
  let assignToken := (Lean4Fmt.Emit.bare_src args[4]!).trimAscii.toString
  if [mutToken, configToken, patternToken, assignToken].any (fun token => token.any (· == '\n'))
      || patternToken.isEmpty || assignToken.isEmpty then none
  return "let " ++ (if mutToken.isEmpty then "" else mutToken ++ " ")
      ++ (if configToken.isEmpty then "" else configToken ++ " ")
      ++ patternToken
      ++ " "
      ++ assignToken

private
def let_else_continuation?
    (walk : Lean4Fmt.Emit.Walk)
    (tail : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let some sequence := tail.getArgs[0]? | return some .nil
  if (Lean4Fmt.Emit.bare_src sequence).trimAscii.toString.isEmpty then
    return some .nil
  let some statements := stmts? sequence | return none
  seq_lines_doc? walk statements true

private
def let_else_layout (head : String) (valueDoc elseDoc continuation : Doc) (width : Nat) : Doc :=
  let valuePart :=
    if (Lean4Fmt.Doc.flat_width valueDoc).isNone then
      .text (head ++ " ") ++ valueDoc
    else
      .text head ++ .group (.nest 2 (.line ++ valueDoc))
  match Lean4Fmt.Doc.flat_width valueDoc, Lean4Fmt.Doc.flat_width elseDoc with
  | some valueWidth, some elseWidth =>
    if head.length + valueWidth + elseWidth + 8 ≤ width then
      .text (head ++ " ") ++ .flatten valueDoc ++ .text " | " ++ .flatten elseDoc ++ continuation
    else
      valuePart ++ .nest 4 (.hardline ++ .text "| " ++ elseDoc) ++ continuation
  | _, _ => valuePart ++ .nest 4 (.hardline ++ .text "| " ++ elseDoc) ++ continuation

private
def emit_let_else (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let a := stx.getArgs
  -- `let pat := v | fallback` — [let, mut?, letConfig, pat, ":="/"←", v,
  -- "|", doSeq, tail?]: head flat, the value width-aware (the idDeclDoc?
  -- treatment), the else arm on its own line at +4 (`    | throwError …`,
  -- the mathlib shape). Single-statement else only this round.
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some head := let_else_head? a | return (← Lean4Fmt.Emit.verbatim stx)
  let vdoc ← walk a[5]!
  if is_verbatim_doc vdoc then return (← Lean4Fmt.Emit.verbatim stx)
  let some ss := stmts? a[7]! | return (← Lean4Fmt.Emit.verbatim stx)
  if ss.size != 1 then return (← Lean4Fmt.Emit.verbatim stx)
  let eDoc ← walk ss[0]!
  if is_verbatim_doc eDoc then return (← Lean4Fmt.Emit.verbatim stx)
  -- a[8] carries the CONTINUATION of the do block (the let-else scopes the
  -- rest): emit it through the statement loop at the let's own column
  let some contD ← let_else_continuation? walk a[8]!
    | return (← Lean4Fmt.Emit.verbatim stx)
  -- width decides flat vs broken (the house one-liner
  -- `let some b := b? | return fallback` stays flat when it fits)
  let width := (← read).layout.lineWidth
  let layout := let_else_layout head vdoc eDoc contD width
  if Lean4Fmt.Doc.has_midline_reanchor layout then
    return (← Lean4Fmt.Emit.verbatim stx)
  return layout

private
def emit_let_rec (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let a := stx.getArgs
  -- `let rec <decl>` = [group[let,rec], letRecDecls, null] — single, plain,
  -- suffix-free binding rides the letDecl machinery (mirrors Term.letrec,
  -- minus the body: the do-loop owns what follows). This statement was a
  -- MUTUAL POISONER: its multi-line verbatim marked the whole enclosing
  -- decl (and any mutual) opaque.
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← Lean4Fmt.Emit.verbatim stx)
  if a.size < 2 || a.size > 3 then
    return (← Lean4Fmt.Emit.verbatim stx)
  let kwT := Lean4Fmt.Emit.canon_tok a[0]!
  if kwT.isEmpty || kwT.any (· == '\n') then
    return (← Lean4Fmt.Emit.verbatim stx)
  if !((a[2]?.map (fun s => (Lean4Fmt.Emit.bare_src s).trimAscii.toString.isEmpty)).getD true) then
    return (← Lean4Fmt.Emit.verbatim stx)
  let decls := ((a[1]!.getArgs[0]?).map (·.getArgs)).getD #[]
  if decls.size != 1 then
    return (← Lean4Fmt.Emit.verbatim stx)
  let rd := decls[0]!
  if rd.getKind != ``Lean.Parser.Term.letRecDecl || rd.getArgs.size != 4 then
    return (← Lean4Fmt.Emit.verbatim stx)
  if !(Lean4Fmt.Emit.bare_src rd.getArgs[0]!).trimAscii.toString.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  if !(Lean4Fmt.Emit.bare_src rd.getArgs[1]!).trimAscii.toString.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  if !(Lean4Fmt.Emit.bare_src rd.getArgs[3]!).trimAscii.toString.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  let declDoc ← walk rd.getArgs[2]!
  if Lean4Fmt.Doc.hasMultilineVerbatim declDoc then
    return (← Lean4Fmt.Emit.verbatim stx)
  return .text (kwT ++ " ") ++ declDoc

private
def emit_reassign (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let a := stx.getArgs
  -- bare `x := v` = [letIdDeclNoBinders] — the inner decl IS the statement
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some inner := a[0]? | return (← Lean4Fmt.Emit.verbatim stx)
  let dDoc ← walk inner
  if Lean4Fmt.Doc.hasMultilineVerbatim dDoc then
    return (← Lean4Fmt.Emit.verbatim stx)
  return dDoc

private
def emit_reassign_arrow
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Doc := do
  let a := stx.getArgs
  -- bare `x ← v` = [doIdDecl]
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some inner := a[0]? | return (← Lean4Fmt.Emit.verbatim stx)
  match ← id_decl_doc? walk inner with
  | some d => return d
  | none => return (← Lean4Fmt.Emit.verbatim stx)

private
def emit_return_value
    (walk : Lean4Fmt.Emit.Walk)
    (stx value : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Doc := do
  let valueDoc ← walk value
  if Lean4Fmt.Doc.hasMultilineVerbatim valueDoc then
    return (← Lean4Fmt.Emit.verbatim stx)
  return .text "return " ++ valueDoc

private
def emit_return (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let a := stx.getArgs
  -- `return` or `return v` = ["return", null(term?)] — the value GLUES to
  -- the keyword line: the argument is OPTIONAL, so a break after `return`
  -- reparses as a bare return plus a stray statement ("must be last element
  -- in a do sequence" — found on Pantograph). A too-wide value breaks
  -- INSIDE itself (its head stays on the line).
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← Lean4Fmt.Emit.verbatim stx)
  match ((a[1]?.map (·.getArgs)).getD #[])[0]? with
  | none => return (Doc.text "return")
  | some value => emit_return_value walk stx value

private
def emit_expr (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let a := stx.getArgs
  -- a plain expression statement: the term IS the statement
  match a[0]? with
  | some t => return (← walk t)
  | none => return (← Lean4Fmt.Emit.verbatim stx)

private
def emit_if (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let a := stx.getArgs
  -- [if, cond, then, seq, (else-if group)*, else?]. Conditions (doIfProp /
  -- if-let, with an optional `h :` binder) are reproduced token-for-token,
  -- single-line. Every line comment must live INSIDE one of the branch
  -- sequences (the accounting below) — a comment around a keyword or in a
  -- condition has no seam here and forces verbatim. Only the FINAL branch may
  -- end in a trailing comment (the statement seam follows it); a comment
  -- before an `else` has no seam.
  if a.size != 6 then
    return (← Lean4Fmt.Emit.verbatim stx)
  let condT := Lean4Fmt.Emit.canon_tok a[1]!
  if condT.isEmpty || condT.any (· == '\n') then
    return (← Lean4Fmt.Emit.verbatim stx)
  let mut branches : Array (String × Lean.Syntax) := #[("if " ++ condT ++ " then", a[3]!)]
  for g in a[4]!.getArgs do
    let ga := g.getArgs
    if ga.size != 4 then
      return (← Lean4Fmt.Emit.verbatim stx)
    let cT := Lean4Fmt.Emit.canon_tok ga[1]!
    if cT.isEmpty || cT.any (· == '\n') then
      return (← Lean4Fmt.Emit.verbatim stx)
    branches := branches.push ("else if " ++ cT ++ " then", ga[3]!)
  let elseArgs := a[5]!.getArgs
  if !elseArgs.isEmpty then
    if elseArgs.size != 2 then
      return (← Lean4Fmt.Emit.verbatim stx)
    branches := branches.push ("else", elseArgs[1]!)
  -- comments only inside branch seqs (the statement's own leading is the
  -- do-loop's and exempt; its trailing is inside the final seq's count)
  let seqCmts := branches.foldl (fun n b => n + Lean4Fmt.Syntax.count_subtree_line_comments b.2) 0
  let ownLead := Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? stx).getD "")
  if Lean4Fmt.Syntax.count_subtree_line_comments stx != seqCmts + ownLead then
    return (← Lean4Fmt.Emit.verbatim stx)
  let mut d : Doc := .nil
  for h : idx in [0:branches.size] do
    let (kw, seq) := branches[idx]
    let some bD ← branch_doc? walk seq (idx + 1 == branches.size)
      (guardBreak := (← read).breaking.guardIfOwnLine)
      | return (← Lean4Fmt.Emit.verbatim stx)
    d := d ++ (if idx == 0 then Doc.nil else .hardline) ++ .text kw ++ bD
  return d

private
def match_alts? (container : Lean.Syntax) : Option (Array Lean.Syntax) :=
  Id.run do
    let mut alternatives := #[]
    for group in container.getArgs do
      for child in group.getArgs do
        if child.getKind == ``Lean.Parser.Term.matchAlt then alternatives := alternatives.push child
    if alternatives.isEmpty then
      return none
    for alternative in alternatives do
      if alternative.getArgs.size != 4 then
        return none
      if (((Lean4Fmt.Syntax.leading? alternative).getD "").splitOn "/-").length > 1 then
        return none
    return some alternatives

private
def match_comments_owned (stx : Lean.Syntax) (alternatives : Array Lean.Syntax) : Bool :=
  let sequenceComments :=
    alternatives.foldl
      (fun count alternative =>
        count + Lean4Fmt.Syntax.count_subtree_line_comments (alternative.getArgs[3]!))
      0
  let leadingComments :=
    alternatives.foldl
      (fun count alternative =>
        count + Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? alternative).getD ""))
      0
  let ownLeading := Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? stx).getD "")
  Lean4Fmt.Syntax.count_subtree_line_comments stx == sequenceComments + leadingComments + ownLeading

private
def match_pattern_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (pattern : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m (Option (Doc × Bool)) := do
  let patternDoc ← walk pattern
  if !Lean4Fmt.Doc.hasMultilineVerbatim patternDoc then
    return some (patternDoc, false)
  Lean4Fmt.Emit.alt_pattern_stack? pattern Lean4Fmt.Emit.token_join_flat?

private
def match_arm_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (alternative : Lean.Syntax)
    (last : Bool)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let args := alternative.getArgs
  let some (patternDoc, patternBroken) ← match_pattern_doc? walk args[1]! | return none
  let some bodyDoc ← branch_doc? walk args[3]! last | return none
  let armSource := (Lean4Fmt.Emit.bare_src alternative).trimAscii.toString
  let preserve := (← read).breaking.preserveLineBreaks
    && !armSource.isEmpty && !armSource.any (· == '\n') && !patternBroken
  let armDoc :=
    if preserve then .text armSource
    else
      let sourceArrow := (Lean4Fmt.Emit.bare_src (args[2]?.getD .missing)).trimAscii.toString
      let arrow := if sourceArrow.isEmpty then "=>" else sourceArrow
      .text "| " ++ patternDoc ++ .text (" " ++ arrow) ++ bodyDoc
  let some separator :=
    Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? alternative).getD "")
    | return none
  return some (separator ++ armDoc)

private
def match_body_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (head : String)
    (alternatives : Array Lean.Syntax)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let mut output := .text head
  for h : idx in [0:alternatives.size] do
    let some armDoc ← match_arm_doc? walk alternatives[idx] (idx + 1 == alternatives.size)
      | return none
    output := output ++ armDoc
  return some output

private
def emit_match (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let a := stx.getArgs
  -- [match, generalizing?, motive?, ?, discrs, "with", matchAlts] — the head
  -- `match <discrs> with` reproduced token-for-token, single-line; each arm
  -- `| pat =>` with its doSeq body via branchDoc? (inline when a single clean
  -- statement fits). Seam accounting as for doIf: every line comment must sit
  -- inside an arm's sequence; only the FINAL arm may end in a trailing
  -- comment (the statement seam follows it).
  if a.size != 7 then
    return (← Lean4Fmt.Emit.verbatim stx)
  let midParts :=
    ((a.extract 1 5).map (fun s => Lean4Fmt.Emit.canon_tok s)).filter (fun s => !s.isEmpty)
  let head := "match " ++ String.intercalate " " midParts.toList ++ " with"
  if head.any (· == '\n') then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some alternatives := match_alts? a[6]!
      | return (← Lean4Fmt.Emit.verbatim stx "doMatch-arm-block-comment")
  if !match_comments_owned stx alternatives then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some body ← match_body_doc? walk head alternatives
    | return (← Lean4Fmt.Emit.verbatim stx)
  return body

private
def emit_loop (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let a := stx.getArgs
  -- `for x in xs do` / `while c do` / `unless c do` — head tokens
  -- single-line (canonically respaced), the body sequence one statement
  -- per line at +2 with the seam loop owning inter-statement trivia
  if a.size < 2 then
    return (← Lean4Fmt.Emit.verbatim stx)
  let mut head := ""
  for h : idx in [0:a.size - 1] do
    let c := a[idx]!
    -- first child's leading = the FORM's own leading — the enclosing seam
    -- owns it (see exampleDoc?); interior comments still bail
    let ownLead :=
      if idx == 0 then
        Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? c).getD "")
      else
        0
    if Lean4Fmt.Syntax.count_subtree_line_comments c > ownLead then
      return (← Lean4Fmt.Emit.verbatim stx)
    let t := Lean4Fmt.Emit.canon_tok c
    if t.any (· == '\n') then
      return (← Lean4Fmt.Emit.verbatim stx)
    if !t.isEmpty then head := if head.isEmpty then t else head ++ " " ++ t
  if head.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some ss := stmts? a[a.size - 1]! | return (← Lean4Fmt.Emit.verbatim stx)
  match ← seq_lines_doc? walk ss true with
  | some body => return .text head ++ .nest 2 body
  | none => return (← Lean4Fmt.Emit.verbatim stx)

private
def emit_do (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let a := stx.getArgs
  -- A comment on the `do` line itself has no home in the layout.
  let doKwTrail := ((Lean4Fmt.Syntax.trailing? (a[0]?.getD .missing)).getD "").trimAscii.toString
  if !doKwTrail.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some seq := a[1]? | return (← Lean4Fmt.Emit.verbatim stx)
  let some ss := stmts? seq | return (← Lean4Fmt.Emit.verbatim stx)
  if (← read).breaking.compactDo && ss.size == 1
      && ((Lean4Fmt.Syntax.leading? ss[0]!).getD "").toList.all (·.isWhitespace) then
    let sDoc ← walk ss[0]!
    if !Lean4Fmt.Doc.hasMultilineVerbatim sDoc then
      return .text "do" ++ .group (.nest 2 (.line ++ sDoc))
  match ← seq_lines_doc? walk ss true with
  | some body => return .text "do" ++ .nest 2 body
  | none => return (← Lean4Fmt.Emit.verbatim stx)

/-- Emit through ordered syntax-family routing. -/
def emit (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  -- preserveLineBreaks: a single-line do-statement is byte-exact (the
  -- author's `let x: T ← …` spacing survives); the do BLOCK itself and
  -- multi-line statements stay structural
  if (← read).breaking.preserveLineBreaks && stx.getKind != ``Lean.Parser.Term.do then
    let t := Lean4Fmt.Emit.bare_src stx
    if !t.isEmpty && !t.any (· == '\n') then
      return .text t
  match stx.getKind with
  | ``Lean.Parser.Term.doLet | ``Lean.Parser.Term.doLetArrow => emit_let walk stx
  | ``Lean.Parser.Term.doLetElse => emit_let_else walk stx
  | ``Lean.Parser.Term.doLetRec => emit_let_rec walk stx
  | ``Lean.Parser.Term.doReassign => emit_reassign walk stx
  | ``Lean.Parser.Term.doReassignArrow => emit_reassign_arrow walk stx
  | ``Lean.Parser.Term.doReturn => emit_return walk stx
  | ``Lean.Parser.Term.doExpr => emit_expr walk stx
  | ``Lean.Parser.Term.doIf => emit_if walk stx
  | ``Lean.Parser.Term.doMatch => emit_match walk stx
  | ``Lean.Parser.Term.doFor | `Lean.Parser.Term.doWhile | `Lean.Parser.Term.doUnless =>
    emit_loop walk stx
  | ``Lean.Parser.Term.do | ``Lean.Parser.Term.doNested => emit_do walk stx
  | _ => Lean4Fmt.Emit.verbatim stx

end Lean4Fmt.Emit.DoNotation
