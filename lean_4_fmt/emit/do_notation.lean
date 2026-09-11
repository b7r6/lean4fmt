/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // EMIT // DoNotation
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Open-recursion emitter for the DoNotation category (doc/design.md §6): the `do`
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

import lean_4_fmt.emit.monad
import lean_4_fmt.emit.tokens

namespace Lean4Fmt.Emit.DoNotation

open Lean Lean4Fmt.Doc

private partial
def syntax_kind_tree (syntaxNode : Lean.Syntax) (fuel : Nat := 3) : String :=
  let name := syntaxNode.getKind.toString
  if fuel == 0 || syntaxNode.getArgs.isEmpty then
    name
  else
    let children := syntaxNode.getArgs.toList.map (syntax_kind_tree · (fuel - 1))
    name ++ "[" ++ String.intercalate ", " children ++ "]"

private
def id_decl_head? (document : Lean.Syntax) : Option String :=
  Id.run do
    let args := document.getArgs
    if document.getKind == ``Lean.Parser.Term.doIdDecl then
      if args.size != 4 then
        return none
    else if document.getKind == ``Lean.Parser.Term.doPatDecl then
      if args.size != 5 then
        return none
      let elseTail := args[4]!.getArgs
      let elsePipe :=
        if elseTail.isEmpty then "" else (Lean4Fmt.Emit.bare_src elseTail[0]!).trimAscii.toString
      if (elseTail[0]?.bind (·.getPos?)).isSome && !elsePipe.isEmpty then
        return none
    else
      return none
    let nameToken := Lean4Fmt.Emit.canon_tok args[0]!
    let typeToken := Lean4Fmt.Emit.canon_tok args[1]!
    return String.intercalate " " ([nameToken, typeToken].filter (fun text => !text.isEmpty))

private
def id_decl_value? (expression : Lean.Syntax) : Option Lean.Syntax :=
  if expression.getKind == ``Lean.Parser.Term.doExpr then
    expression.getArgs[0]?
  else if expression.getKind == ``Lean.Parser.Term.doIf
      || expression.getKind == ``Lean.Parser.Term.doMatch
      || expression.getKind == ``Lean.Parser.Term.do then
    some expression
  else
    none

/-- `x (: τ)? ← v` — the monadic-bind decl inside doLetArrow / doReassignArrow.
    The arrow atom is reproduced from source (`←` or `<-` — the token gate cares);
    the value inside the `doExpr` is walked, flat on the arrow line when it fits,
    else on the next line at +2. A `do` value glues to the arrow (its body brings
    its own hardline). `none` on any structural surprise or a value carrying a
    multi-line opaque block — the caller reproduces the whole statement verbatim. -/
private
def id_decl_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (document : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let args := document.getArgs
  -- doIdDecl = [id, type?, "←", doExpr]; doPatDecl = [pat, type?, "←",
  -- doExpr, else?] — same arrow/expr slots; the pattern joins flat and the
  -- optional `| else` tail bails
  let some head := id_decl_head? document | return none
  let arrowT := (Lean4Fmt.Emit.bare_src args[2]!).trimAscii.toString
  if head.isEmpty || head.any (· == '\n') || arrowT.any (· == '\n') then
    return none
  let some value := id_decl_value? args[3]! | return none
  let vdoc ← walk value
  -- a bare whole-verbatim value gains nothing; otherwise the ASSEMBLED
  -- layout decides (hasMidlineReanchor — interior verbatims at hardline
  -- seams re-anchor deterministically): a do/by/match value GLUES to the
  -- arrow (its members bring their own hardlines — `let x ← match e with`
  -- + arms below, the ApplyFun shape), anything else width-aware at +2
  if (match vdoc with | .verbatim _ _ => true | _ => false) then
    Lean4Fmt.Emit.emit_diag
      { severity := .debug,
        pos      := (value.getPos?.map (·.byteIdx)).getD 0,
        rule     := "do-let-value",
        message  := s!"unhandled do-let value: {syntax_kind_tree value}" }
    return none
  -- ANY multi-line value glues (`x ← cachedBuild args do`, `x ← match e
  -- with` — the house shape hangs the value head on the arrow line; its own
  -- doc breaks below); a FLAT value keeps the width-aware group (inline
  -- when it fits, else own line at +2 — unchanged)
  let glue :=
    value.getKind == ``Lean.Parser.Term.do || value.getKind == ``Lean.Parser.Term.byTactic
        || value.getKind == ``Lean.Parser.Term.match
        || (Lean4Fmt.Doc.flat_width vdoc).isNone
  let layout : Doc :=
    if glue then
      .text head ++ .text (" " ++ arrowT ++ " ") ++ vdoc
    else
      .text head ++ .text (" " ++ arrowT) ++ .group (.nest 2 (.line ++ vdoc))
  if Lean4Fmt.Doc.has_midline_reanchor layout then
    Lean4Fmt.Emit.emit_diag
      { severity := .debug,
        pos      := (value.getPos?.map (·.byteIdx)).getD 0,
        rule     := "do-let-value",
        message  := s!"midline do-let value: {syntax_kind_tree value}" }
    return none
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
    for group in seq.getArgs do
      for child in group.getArgs do
        if child.getKind == ``Lean.Parser.Term.doSeqItem then items := items.push child
    if items.isEmpty then
      return none
    for item in items do
      let itemArgs := item.getArgs
      if itemArgs.size > 1
          && !((Lean4Fmt.Emit.bare_src
            (itemArgs[itemArgs.size-1]!)).trimAscii.toString.isEmpty) then
        return none
    return some (items.map (fun item => item.getArgs[0]?.getD Lean.Syntax.missing))

/-- The statement LINES of a sequence: each statement preceded by its structural
    leading (comments/blanks — `leadingSep?`) and followed by its same-line
    trailing comment. `lastOwned`: when true, the LAST statement's trailing
    belongs to the enclosing seam and is skipped (a whole `do`, whose do-loop
    caller re-appends it; a final if-branch, whose statement seam follows); when
    false there is NO seam for it (a then-branch before `else`) — any content
    there aborts to `none`. -/
def seq_lines_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (strings : Array Lean.Syntax)
    (lastOwned : Bool)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let mut body : Doc := .nil
  for h : idx in [0:strings.size] do
    let stmt := strings[idx]
    let trailT := ((Lean4Fmt.Syntax.trailing? stmt).getD "").trimAscii.toString
    let last := idx + 1 == strings.size
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
    else
      match Lean4Fmt.Emit.leading_sep? lead with
      | some textValue => pure textValue
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
  let some strings := stmts? seq | return none
  if strings.size == 1 then
    let lead := (Lean4Fmt.Syntax.leading? strings[0]!).getD ""
    let plainLead := ((lead.splitOn "\n").drop 1).dropLast.isEmpty
    let srcInline := !lead.any (· == '\n')
    let trailT := ((Lean4Fmt.Syntax.trailing? strings[0]!).getD "").trimAscii.toString
    if plainLead && (lastOwned || trailT.isEmpty)
        && (!(← read).breaking.preserveLineBreaks || srcInline) then
      let sDoc ← walk strings[0]!
      -- guardIfOwnLine: a CONTROL-FLOW branch (`return`/`throw`) keeps its
      -- own line even when it fits — the guard ladder reads vertically;
      -- effect branches still inline by width (the house distinction)
      let isCtl := strings[0]!.getKind == ``Lean.Parser.Term.doReturn
        || ((Lean4Fmt.Emit.bare_src strings[0]!).trimAscii.toString.startsWith "throw")
      if (← read).breaking.inlineBranches
          && !(guardBreak && isCtl)
          && (Lean4Fmt.Doc.flat_width sDoc).isSome
          && !Lean4Fmt.Doc.hasMultilineVerbatim sDoc then
        return some (.group (.nest 2 (.line ++ sDoc)))
      -- a nested `do` GLUES to the branch keyword (`=> do` / `then do`) —
      -- its statements bring their own hardlines (mirrors the eqns arm rule;
      -- without this the `do` lands alone on its own line)
      let kind := strings[0]!.getKind
      if !Lean4Fmt.Doc.hasMultilineVerbatim sDoc
          && (kind == ``Lean.Parser.Term.doNested
            || (kind == ``Lean.Parser.Term.doExpr
              && (strings[0]!.getArgs[0]?.map (·.getKind)) == some ``Lean.Parser.Term.do)) then
        return some (.text " " ++ sDoc)
  match ← seq_lines_doc? walk strings lastOwned with
  | some body => return some (.nest 2 body)
  | none => return none

/-- Emit `do <seq>` — one statement per line indented by 2, leading comment/blank
    lines placed structurally, same-line trailing comments re-appended — or one of
    the binding statements (see module header). Only the plain `doSeqIndent` shape
    of `do` is handled; the bracketed `{ … }` shape and any structural surprise
    fall back to verbatim so no token (or comment) is dropped. -/
private
def emit_let (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let args := stx.getArgs
  -- `let (mut)? (config)? decl` = [let, mut?, letConfig, decl] where decl is a
  -- letDecl (`:=`, walked — Term handles the 5-slot shape), a doIdDecl (`←`),
  -- or a doPatDecl (`pat ←`; its optional `| else` tail bails inside
  -- idDeclDoc?). Only INTERIOR comments force verbatim — the statement's
  -- outer leading/trailing are the do-loop's to place.
  if stx.getKind == ``Lean.Parser.Term.doLet
      && Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← Lean4Fmt.Emit.verbatim stx)
  if args.size != 4 then
    return (← Lean4Fmt.Emit.verbatim stx)
  let mutT := (Lean4Fmt.Emit.bare_src args[1]!).trimAscii.toString
  let cfgT := (Lean4Fmt.Emit.bare_src args[2]!).trimAscii.toString
  if mutT.any (· == '\n') || cfgT.any (· == '\n') then
    return (← Lean4Fmt.Emit.verbatim stx)
  let headD : Doc :=
    .text "let " ++ (if mutT.isEmpty then .nil else .text (mutT ++ " "))
        ++ (if cfgT.isEmpty then .nil else .text (cfgT ++ " "))
  if stx.getKind == ``Lean.Parser.Term.doLet then
    let dDoc ← walk args[3]!
    if Lean4Fmt.Doc.hasMultilineVerbatim dDoc then
      return (← Lean4Fmt.Emit.verbatim stx)
    return headD ++ dDoc
  else
    match ← id_decl_doc? walk args[3]! with
    | some document => return headD ++ document
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
  let args := stx.getArgs
  -- `let pat := v | fallback` — [let, mut?, letConfig, pat, ":="/"←", v,
  -- "|", doSeq, tail?]: head flat, the value width-aware (the idDeclDoc?
  -- treatment), the else arm on its own line at +4 (`    | throwError …`,
  -- the mathlib shape). Single-statement else only this round.
  -- Do not reject comments in the scoped continuation wholesale: its statement
  -- loop owns inter-statement trivia, while the value and else branch fall back
  -- independently if their emitters cannot place an interior comment.
  let some head := let_else_head? args | return (← Lean4Fmt.Emit.verbatim stx "do-let-else-head")
  let vdoc ← walk args[5]!
  if is_verbatim_doc vdoc then
    return (← Lean4Fmt.Emit.verbatim stx "do-let-else-value")
  let some strings := stmts? args[7]!
      | return (← Lean4Fmt.Emit.verbatim stx "do-let-else-branch-shape")
  if strings.size != 1 then
    return (← Lean4Fmt.Emit.verbatim stx "do-let-else-branch-count")
  let elseTrailing := ((Lean4Fmt.Syntax.trailing? strings[0]!).getD "").trimAscii.toString
  if elseTrailing.any (· == '\n') then
    return (← Lean4Fmt.Emit.verbatim stx "do-let-else-branch-trailing")
  let eDoc ← walk strings[0]!
  if is_verbatim_doc eDoc then
    return (← Lean4Fmt.Emit.verbatim stx "do-let-else-branch")
  -- The single else statement's trailing belongs to this branch seam, not to
  -- the scoped continuation. Re-append a same-line comment before the
  -- continuation's structural hardline.
  let eDoc := eDoc ++ if elseTrailing.isEmpty then .nil else .text (" " ++ elseTrailing)
  -- a[8] carries the CONTINUATION of the do block (the let-else scopes the
  -- rest): emit it through the statement loop at the let's own column
  let some contD ← let_else_continuation? walk args[8]!
    | return (← Lean4Fmt.Emit.verbatim stx "do-let-else-continuation")
  -- width decides flat vs broken (the house one-liner
  -- `let some b := b? | return fallback` stays flat when it fits)
  let width := (← read).layout.lineWidth
  let layout := let_else_layout head vdoc eDoc contD width
  if Lean4Fmt.Doc.has_midline_reanchor layout then
    return (← Lean4Fmt.Emit.verbatim stx "do-let-else-reanchor")
  return layout

private
def emit_let_rec (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let args := stx.getArgs
  -- `let rec <decl>` = [group[let,rec], letRecDecls, null] — single, plain,
  -- suffix-free binding rides the letDecl machinery (mirrors Term.letrec,
  -- minus the body: the do-loop owns what follows). This statement was a
  -- MUTUAL POISONER: its multi-line verbatim marked the whole enclosing
  -- decl (and any mutual) opaque.
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← Lean4Fmt.Emit.verbatim stx)
  if args.size < 2 || args.size > 3 then
    return (← Lean4Fmt.Emit.verbatim stx)
  let kwT := Lean4Fmt.Emit.canon_tok args[0]!
  if kwT.isEmpty || kwT.any (· == '\n') then
    return (← Lean4Fmt.Emit.verbatim stx)
  if !((args[2]?.map
    (fun syntaxNode => (Lean4Fmt.Emit.bare_src syntaxNode).trimAscii.toString.isEmpty)).getD true) then
    return (← Lean4Fmt.Emit.verbatim stx)
  let decls := ((args[1]!.getArgs[0]?).map (·.getArgs)).getD #[]
  if decls.size != 1 then
    return (← Lean4Fmt.Emit.verbatim stx)
  let recursiveDecl := decls[0]!
  if recursiveDecl.getKind != ``Lean.Parser.Term.letRecDecl
      || recursiveDecl.getArgs.size != 4 then
    return (← Lean4Fmt.Emit.verbatim stx)
  if !(Lean4Fmt.Emit.bare_src recursiveDecl.getArgs[0]!).trimAscii.toString.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  if !(Lean4Fmt.Emit.bare_src recursiveDecl.getArgs[1]!).trimAscii.toString.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  if !(Lean4Fmt.Emit.bare_src recursiveDecl.getArgs[3]!).trimAscii.toString.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  let declDoc ← walk recursiveDecl.getArgs[2]!
  if Lean4Fmt.Doc.hasMultilineVerbatim declDoc then
    return (← Lean4Fmt.Emit.verbatim stx)
  return .text (kwT ++ " ") ++ declDoc

private
def emit_reassign (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let args := stx.getArgs
  -- bare `x := v` = [letIdDeclNoBinders] — the inner decl IS the statement
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some inner := args[0]? | return (← Lean4Fmt.Emit.verbatim stx)
  let dDoc ← walk inner
  if Lean4Fmt.Doc.hasMultilineVerbatim dDoc then
    return (← Lean4Fmt.Emit.verbatim stx)
  return dDoc

private
def emit_reassign_arrow
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Doc := do
  let args := stx.getArgs
  -- bare `x ← v` = [doIdDecl]
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some inner := args[0]? | return (← Lean4Fmt.Emit.verbatim stx)
  match ← id_decl_doc? walk inner with
  | some document => return document
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
  let args := stx.getArgs
  -- `return` or `return v` = ["return", null(term?)] — the value GLUES to
  -- the keyword line: the argument is OPTIONAL, so a break after `return`
  -- reparses as a bare return plus a stray statement ("must be last element
  -- in a do sequence" — found on Pantograph). A too-wide value breaks
  -- INSIDE itself (its head stays on the line).
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← Lean4Fmt.Emit.verbatim stx)
  match ((args[1]?.map (·.getArgs)).getD #[])[0]? with
  | none => return (Doc.text "return")
  | some value => emit_return_value walk stx value

private
def emit_expr (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let args := stx.getArgs
  -- a plain expression statement: the term IS the statement
  match args[0]? with
  | some trailing => return (← walk trailing)
  | none => return (← Lean4Fmt.Emit.verbatim stx)

private
def emit_if (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let args := stx.getArgs
  -- [if, cond, then, seq, (else-if group)*, else?]. Conditions (doIfProp /
  -- if-let, with an optional `h :` binder) are reproduced token-for-token,
  -- single-line. Every line comment must live INSIDE one of the branch
  -- sequences (the accounting below) — a comment around a keyword or in a
  -- condition has no seam here and forces verbatim. Only the FINAL branch may
  -- end in a trailing comment (the statement seam follows it); a comment
  -- before an `else` has no seam.
  if args.size != 6 then
    return (← Lean4Fmt.Emit.verbatim stx)
  let condT := Lean4Fmt.Emit.canon_tok args[1]!
  if condT.isEmpty || condT.any (· == '\n') then
    return (← Lean4Fmt.Emit.verbatim stx)
  let mut branches : Array (String × Lean.Syntax) := #[("if " ++ condT ++ " then", args[3]!)]
  for group in args[4]!.getArgs do
    let groupArgs := group.getArgs
    if groupArgs.size != 4 then
      return (← Lean4Fmt.Emit.verbatim stx)
    let conditionText := Lean4Fmt.Emit.canon_tok groupArgs[1]!
    if conditionText.isEmpty || conditionText.any (· == '\n') then
      return (← Lean4Fmt.Emit.verbatim stx)
    branches := branches.push ("else if " ++ conditionText ++ " then", groupArgs[3]!)
  let elseArgs := args[5]!.getArgs
  if !elseArgs.isEmpty then
    if elseArgs.size != 2 then
      return (← Lean4Fmt.Emit.verbatim stx)
    branches := branches.push ("else", elseArgs[1]!)
  -- comments only inside branch seqs (the statement's own leading is the
  -- do-loop's and exempt; its trailing is inside the final seq's count)
  let seqCmts :=
    branches.foldl
      (fun count branch => count + Lean4Fmt.Syntax.count_subtree_line_comments branch.2)
      0
  let ownLead := Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? stx).getD "")
  if Lean4Fmt.Syntax.count_subtree_line_comments stx != seqCmts + ownLead then
    return (← Lean4Fmt.Emit.verbatim stx)
  let mut document : Doc := .nil
  for h : idx in [0:branches.size] do
    let (keyword, seq) := branches[idx]
    let some branchDoc ← branch_doc? walk seq (idx + 1 == branches.size)
      (guardBreak := (← read).breaking.guardIfOwnLine)
      | return (← Lean4Fmt.Emit.verbatim stx)
    document :=
      document ++ (if idx == 0 then Doc.nil else .hardline) ++ .text keyword ++ branchDoc
  return document

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
    return some alternatives

private
def match_comments_owned (stx : Lean.Syntax) (alternatives : Array Lean.Syntax) : Bool :=
  let sequenceComments :=
    alternatives.foldl
      (
        fun count alternative =>
          count + Lean4Fmt.Syntax.count_subtree_line_comments (alternative.getArgs[3]!)
      )
      0
  let leadingComments :=
    alternatives.foldl
      (
        fun count alternative =>
          count
              + Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? alternative).getD "")
      )
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
  let args := stx.getArgs
  -- [match, generalizing?, motive?, ?, discrs, "with", matchAlts] — the head
  -- `match <discrs> with` reproduced token-for-token, single-line; each arm
  -- `| pat =>` with its doSeq body via branchDoc? (inline when a single clean
  -- statement fits). Seam accounting as for doIf: every line comment must sit
  -- inside an arm's sequence; only the FINAL arm may end in a trailing
  -- comment (the statement seam follows it).
  if args.size != 7 then
    return (← Lean4Fmt.Emit.verbatim stx)
  let midParts :=
    ((args.extract 1 5).map (fun syntaxNode => Lean4Fmt.Emit.canon_tok syntaxNode)).filter
      (fun text => !text.isEmpty)
  let head := "match " ++ String.intercalate " " midParts.toList ++ " with"
  if head.any (· == '\n') then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some alternatives := match_alts? args[6]!
      | return (← Lean4Fmt.Emit.verbatim stx "doMatch-arm-block-comment")
  if !match_comments_owned stx alternatives then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some body ← match_body_doc? walk head alternatives
    | return (← Lean4Fmt.Emit.verbatim stx)
  return body

private
def emit_loop (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let args := stx.getArgs
  -- `for x in xs do` / `while c do` / `unless c do` — head tokens
  -- single-line (canonically respaced), the body sequence one statement
  -- per line at +2 with the seam loop owning inter-statement trivia
  if args.size < 2 then
    return (← Lean4Fmt.Emit.verbatim stx)
  let mut head := ""
  for h : idx in [0:args.size - 1] do
    let child := args[idx]!
    -- first child's leading = the FORM's own leading — the enclosing seam
    -- owns it (see exampleDoc?); interior comments still bail
    let ownLead :=
      if idx == 0 then
        Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? child).getD "")
      else
        0
    if Lean4Fmt.Syntax.count_subtree_line_comments child > ownLead then
      return (← Lean4Fmt.Emit.verbatim stx)
    let text := Lean4Fmt.Emit.canon_tok child
    if text.any (· == '\n') then
      return (← Lean4Fmt.Emit.verbatim stx)
    if !text.isEmpty then head := if head.isEmpty then text else head ++ " " ++ text
  if head.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some strings := stmts? args[args.size - 1]! | return (← Lean4Fmt.Emit.verbatim stx)
  match ← seq_lines_doc? walk strings true with
  | some body => return .text head ++ .nest 2 body
  | none => return (← Lean4Fmt.Emit.verbatim stx)

private
def emit_do (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let args := stx.getArgs
  -- A comment on the `do` line itself has no home in the layout.
  let doKwTrail := ((Lean4Fmt.Syntax.trailing? (args[0]?.getD .missing)).getD "").trimAscii.toString
  if !doKwTrail.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some seq := args[1]? | return (← Lean4Fmt.Emit.verbatim stx)
  let some strings := stmts? seq | return (← Lean4Fmt.Emit.verbatim stx)
  if (← read).breaking.compactDo && strings.size == 1
      && ((Lean4Fmt.Syntax.leading? strings[0]!).getD "").toList.all (·.isWhitespace) then
    let sDoc ← walk strings[0]!
    if !Lean4Fmt.Doc.hasMultilineVerbatim sDoc then
      return .text "do" ++ .group (.nest 2 (.line ++ sDoc))
  match ← seq_lines_doc? walk strings true with
  | some body => return .text "do" ++ .nest 2 body
  | none => return (← Lean4Fmt.Emit.verbatim stx)

/-- Emit through ordered syntax-family routing. -/
def emit (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do

  -- preserveLineBreaks: a single-line do-statement is byte-exact (the
  -- author's `let x: T ← …` spacing survives); the do BLOCK itself and
  -- multi-line statements stay structural
  if (← read).breaking.preserveLineBreaks && stx.getKind != ``Lean.Parser.Term.do then
    let text := Lean4Fmt.Emit.bare_src stx
    if !text.isEmpty && !text.any (· == '\n') then
      return .text text
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
  | termKind =>
    if termKind == ``Lean.Parser.Term.do || termKind == ``Lean.Parser.Term.doNested then
      emit_do walk stx
    else Lean4Fmt.Emit.verbatim stx

end Lean4Fmt.Emit.DoNotation
