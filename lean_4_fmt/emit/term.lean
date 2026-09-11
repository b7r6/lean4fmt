/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // LEAN4FMT // EMIT // TERM
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Expression constructs. Ported to real `Doc`: applications, binary operators,
    parens/projections, anonymous constructors, list literals, literals — the
    flat, single-line-friendly terms. Recurses via `walk`. Anything carrying a
    line comment (§0.4) or not yet handled falls back to opaque reproduction, so
    it stays token-preserving and idempotent (the gate confirms).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.emit.monad
import lean_4_fmt.emit.tokens
import lean_4_fmt.emit.binders
import lean_4_fmt.syntax.kinds
import lean_4_fmt.syntax.trivia
import lean_4_fmt.syntax.query

namespace Lean4Fmt.Emit.Term

open Lean Lean4Fmt.Doc Lean4Fmt.Emit

/-- Width-aware bracketed comma list `l e₁, e₂, … r`: flat if it fits, else one
    element per line indented by 2 with `l`/`r` on their own lines (the standard
    all-or-nothing `commaList` group). Skips the parser's comma atoms. -/
private
def comma_group
    (walk : Walk)
    (lineValue result : String)
    (children : Array Lean.Syntax)
    : emit_m (Option Doc) := do
  let trailingComma :=
    (children.back?.map (fun child => child.isAtom && (bare_src child).trimAscii.toString == ",")).getD
      false
  let mut documents : Array Doc := #[]
  for child in children do
    if child.isAtom then continue
    let document ← walk child
    if Lean4Fmt.Doc.has_midline_reanchor document then
      return none
    documents := documents.push document
  -- literal pools (§5 fill): many short flat items — byte tables, opcode
  -- lists — pack and wrap at the width instead of exploding one per line
  if !trailingComma && documents.size ≥ 8
      && documents.all (fun document => ((Lean4Fmt.Doc.flat_width document).getD 1000) ≤ 12) then
    let items :=
      ((Array.range documents.size).map
        (fun index =>
          documents[index]!
            ++ (if index + 1 == documents.size then Doc.nil else Doc.text ","))).toList
    return some (.text lineValue ++ .nest 2 (Doc.fillSep items) ++ .text result)
  let body :=
    Lean4Fmt.Doc.sep_by (.text "," ++ .line) documents
        ++ (if trailingComma then .text "," else .nil)
  return some (Lean4Fmt.Doc.brackets lineValue result body)

/-- Comment-bearing comma list, FORCED broken (a line comment cannot flatten,
    §0.4): one element per line at +2, each element's leading comment/blank
    lines placed structurally, the same-line comment after each COMMA (its
    trailing) re-appended, the last element's same-line trailing kept before
    the closer. `none` (caller verbatims) when the closer's leading carries
    content, a trailing spans lines, or a seam has no home. -/
private
def comma_trivia? (comma? : Option Lean.Syntax) : Option (Doc × String) := do
  let some comma := comma? | return (.nil, "")
  let isWhitespace (text : String) : Bool := text.all (fun char => char == ' ' || char == '\t')
  let leading := (Lean4Fmt.Syntax.leading? comma).getD ""
  let separator ← if ((leading.splitOn "\n").drop 1).dropLast.all isWhitespace then some .nil
  else Lean4Fmt.Emit.leading_sep? leading
  return (separator, ((Lean4Fmt.Syntax.trailing? comma).getD "").trimAscii.toString)

private
def seam_comma_list?
    (walk : Walk)
    (lineValue result : String)
    (opener : Lean.Syntax)
    (pairs : Array (Lean.Syntax × Option Lean.Syntax))
    (closer : Lean.Syntax)
    : emit_m (Option Doc) := do
  if pairs.isEmpty then
    return none
  -- a comment on the opener's own line (`[ -- note`) is OUR zone
  let openTrail := ((Lean4Fmt.Syntax.trailing? opener).getD "").trimAscii.toString
  if openTrail.any (· == '\n') then
    return none
  -- comments directly before the closer have no seam yet
  let isWs (text : String) : Bool := text.all (fun char => char == ' ' || char == '\t')
  let closerLead := (Lean4Fmt.Syntax.leading? closer).getD ""
  if !(((closerLead.splitOn "\n").drop 1).dropLast.all isWs) then
    return none
  if !isWs ((closerLead.splitOn "\n").headD "") then
    return none
  let mut body : Doc := .nil
  for h : idx in [0:pairs.size] do
    let (elementBinding, comma?) := pairs[idx]
    let last := idx + 1 == pairs.size
    let some sep := Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? elementBinding).getD "")
        | return none
    let eDoc ← walk elementBinding
    -- the same-line comment can trail the ELEMENT (comma-leading style:
    -- `elementBinding  -- note` with `, e₂` on the next line) or the COMMA (`elementBinding, -- note`);
    -- own both zones. Content in a comma's own LEADING has no seam — bail.
    let eTrail := ((Lean4Fmt.Syntax.trailing? elementBinding).getD "").trimAscii.toString
    -- inter-element comments in LEADING-COMMA style live in the COMMA's
    -- leading full lines — own them via the seam kit (placed after this
    -- element's comma, before the next element; pend collapse merges the
    -- separators). Plain whitespace comma-leading contributes nothing.
    let some (commaLeadSep, cTrail) := comma_trivia? comma? | return none
    let trailT := String.intercalate " " (([eTrail, cTrail].filter (fun text => !text.isEmpty)))
    if trailT.any (· == '\n') then
      return none
    -- when the comma is the LAST element's trailing zone owner, drop through:
    let _ := ()
    let commaD : Doc := if last then .nil else .text ","
    let trailD : Doc := if trailT.isEmpty then .nil else .text (" " ++ trailT)
    body := body ++ sep ++ eDoc ++ commaD ++ trailD ++ commaLeadSep
  let openD : Doc := if openTrail.isEmpty then .nil else .text (" " ++ openTrail)
  return some (.text lineValue ++ openD ++ .nest 2 body ++ .hardline ++ .text result)

/-- A `do`/`by` DESCENDANT — NEWLINE-BLIND: this feeds a layout decision,
    and "is it multi-line in the SOURCE" flips pass-to-pass (the DualNumber
    fixed-point: pass 1 glued the chain flat, pass 2 saw the now-single-line
    `by` and broke at the ops). Statement hardlines re-anchor at the
    placement's nest column on the broken chain layout, which can cross the
    parse floor and re-associate the block (the ApplyAt lesson — an
    elaboration-level tree change the gate caught as tokens). let/structInst
    newline semantics ride safely inside their own self-anchored docs. -/
private partial
def contains_do_by (source : Lean.Syntax) : Bool :=
  source.getKind == ``Lean.Parser.Term.do || source.getKind == ``Lean.Parser.Term.byTactic
      || source.getKind == `Lean.Parser.Term.byTactic'
      || source.getArgs.any contains_do_by

private
def paren_doc (walk : Walk) (stx content : Lean.Syntax) : emit_m Doc := do
  let doc ← walk content
  if Lean4Fmt.Doc.has_midline_reanchor doc then
    return (← verbatim stx "paren-multiline-piece")
  return Lean4Fmt.Doc.brackets "(" ")" doc

/-- A chain TAIL that is SAFE to glue after the flat head: a by/do block, or
    a spine of app/fun/show ENDING in one — the glued doc's only hardlines
    are the block's members, which anchor nest-relative below the line. A
    container with its OWN column discipline (calc: later steps must sit at
    the first step's column, which rides the glued line) re-associates on
    reparse (gate-caught on OmegaLimit: `<| calc` glued flat, the step list
    ended early — tokens). -/
private partial
def tail_glue_safe (source : Lean.Syntax) : Bool :=
  let kind := source.getKind
  if kind == ``Lean.Parser.Term.byTactic || kind == `Lean.Parser.Term.byTactic'
      || kind == ``Lean.Parser.Term.do then
    true
  else if kind == ``Lean.Parser.Term.app then
    ((source.getArgs[1]?.bind (·.getArgs.back?)).map tail_glue_safe).getD false
  else if kind == ``Lean.Parser.Term.fun then
    match source.getArgs[1]? with
    | some bodyForm => ((bodyForm.getArgs.back?).map tail_glue_safe).getD false
    | none          => false
  else if kind == ``Lean.Parser.Term.show then
    (
      (source.getArgs.back?).map
        (
          fun result =>
            result.getKind == `Lean.Parser.Term.byTactic'
                || result.getKind == ``Lean.Parser.Term.byTactic
                || (
                  result.getKind == ``Lean.Parser.Term.fromTerm
                      && ((result.getArgs.back?).map tail_glue_safe).getD false
                )
        )
    ).getD
      false
  else
    false

/-- Whether the subtree contains a COMMA-form structInst — the one doc shape
    whose broken layout carries FIRST-LINE-ANCHORED interior columns (later
    fields must sit colGe the first field, which rides the `{ ` line). Glued
    after `lval := ` that anchor is deep and the parser closes the inner
    list early on reparse (home Preset.lean). Every other multi-line value
    is nest-relative and re-anchors deterministically. -/
private partial
def contains_comma_struct_inst (source : Lean.Syntax) : Bool :=
  (source.getKind == ``Lean.Parser.Term.structInst && (bare_src source).any (· == ','))
      || source.getArgs.any contains_comma_struct_inst

/-- Flatten a subtree into single-line canonTok PIECES (the binder groups of
    a wide quantifier head): a single-line node is one piece, a multi-line
    container contributes its children's pieces recursively; `none` when a
    leaf itself spans lines (nothing to wrap on). -/
private partial
def head_pieces? (source : Lean.Syntax) : Option (Array String) :=
  let text := Lean4Fmt.Emit.canon_tok source
  if !text.any (· == '\n') then
    if text.isEmpty then some #[] else some #[text]
  else if source.getArgs.isEmpty then
    none
  else
    Id.run do
      let mut pieces : Array String := #[]
      for child in source.getArgs do
        match head_pieces? child with
        | some piecesBinding => pieces := pieces ++ piecesBinding
        | none => return none
      return some pieces

/-- A CHAIN value (let/letrec/have) whose doc breaks: its body rides
    hardline seams that anchor at the CURRENT indent — safe at own-line
    placements, a column hazard when glued at a field/binding column
    (doc-derived test: flatWidth none is pass-stable). -/
private
def chain_own_line (value : Lean.Syntax) (vdoc : Doc) : Bool :=
  (
    value.getKind == ``Lean.Parser.Term.let || value.getKind == ``Lean.Parser.Term.letrec
        || value.getKind == ``Lean.Parser.Term.have
        || value.getKind == ``Lean.Parser.Term.letI
        || value.getKind == ``Lean.Parser.Term.haveI
  )
      && (Lean4Fmt.Doc.flat_width vdoc).isNone

/-- A multiline opaque field value cannot follow `field :=` mid-line: its
    source-column re-anchor would become additive on the next pass. Give that
    value an explicit line-start seam while leaving the field and its enclosing
    structure active. -/
private
def opaque_field_value_own_line (vdoc : Doc) : Bool :=
  match vdoc with
  | .verbatim source _ => source.any (· == '\n')
  | _ => Lean4Fmt.Doc.has_midline_reanchor vdoc

/-- A single `structInstField` = [structInstLVal, «rest»]. The LVal (field name /
    path) is reproduced verbatim; the value (the term after `:=`, found inside the
    `structInstFieldDef` in «rest») is walked so it lays out actively. A shorthand
    field `{ x }` (no `:=`) is just its LVal. -/
private partial
def struct_field_value_doc
    (walk : Walk)
    (field lvalStx : Lean.Syntax)
    (lval : Doc)
    (rest : Array Lean.Syntax)
    (fd : Lean.Syntax)
    : emit_m Doc := do
  let defArgs := fd.getArgs
  let value := defArgs[defArgs.size - 1]?.getD Lean.Syntax.missing -- [":=", null?, value]
  -- a field with BINDERS or type ascription (`symm _ _ h := …`) carries
  -- tokens between the lval and the value — the lval++":="++value shape
  -- would DELETE them (gate-caught on mathlib): join the HEAD (lval +
  -- binders + type) single-line and walk the VALUE, same shape as the
  -- plain field. The old whole-field token join required the VALUE
  -- single-line too — the functor-instance idiom (`map {X Y} f := <app
  -- with (by …)>`) rode verbatim on it.
  let expected := Lean4Fmt.Syntax.leaf_toks lvalStx ++ #[":="] ++ Lean4Fmt.Syntax.leaf_toks value
  if Lean4Fmt.Syntax.leaf_toks field != expected then
    let mut headT := Lean4Fmt.Emit.canon_tok lvalStx
    let mut valid := !headT.isEmpty && !headT.any (· == '\n')
    for remaining in rest do
      if !valid then break
      if remaining.getKind == ``Lean.Parser.Term.structInstFieldDef then continue
      let text := Lean4Fmt.Emit.canon_tok remaining
      if text.any (· == '\n') then valid := false
      else if !text.isEmpty then headT := headT ++ " " ++ text
    -- the def node must be exactly the assign shape (`:=` + value)
    if valid
        && Lean4Fmt.Syntax.leaf_toks fd == #[":="] ++ Lean4Fmt.Syntax.leaf_toks value then
      let vdoc ← walk value
      if chain_own_line value vdoc || opaque_field_value_own_line vdoc then
        return .text (headT ++ " :=") ++ .nest 2 (.hardline ++ vdoc)
      return .text (headT ++ " := ") ++ vdoc
    let text := Lean4Fmt.Emit.canon_tok field
    if text.isEmpty || text.any (· == '\n') then
      return (← verbatim field)
    return .text text
  let vdoc ← walk value
  -- a LET-chain value's body sits at hardline seams that ANCHOR AT THE
  -- CURRENT INDENT — glued after `lval := ` that is the FIELD column, so
  -- the comma-less field list ends at the chain body on reparse (the
  -- sepByIndent colGe law; gate-caught on Configuration as a hidden
  -- reparse-fail). A breaking chain value goes OWN-LINE at +2 instead
  -- (the mathlib source shape); flat ones still glue.
  if chain_own_line value vdoc || opaque_field_value_own_line vdoc then
    return lval ++ .text " :=" ++ .nest 2 (.hardline ++ vdoc)
  return lval ++ .text " := " ++ vdoc

private partial
def struct_field_doc (walk : Walk) (field : Lean.Syntax) : emit_m Doc := do
  let fieldArgs := field.getArgs
  let lvalStx := fieldArgs[0]?.getD .missing
  let lvalT := bare_src lvalStx
  let lval ← if !lvalT.isEmpty && !lvalT.any (· == '\n') then
    pure (Doc.text (Lean4Fmt.Emit.canon_tok lvalStx))
  else verbatim lvalStx
  let rest := (fieldArgs[1]?.getD Lean.Syntax.missing).getArgs
  let fd? := rest.find? (·.getKind == ``Lean.Parser.Term.structInstFieldDef)
  match fd? with
  | some fd => struct_field_value_doc walk field lvalStx lval rest fd
  | none => return lval

private partial
def collection_literal_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do
  let left := if kind == Lean4Fmt.Syntax.list_lit_kind then "[" else "#["
  let children := (args[1]?.map (·.getArgs)).getD #[]
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    let mut pairs : Array (Lean.Syntax × Option Lean.Syntax) := #[]
    for child in children do
      if child.isAtom then
        if !pairs.isEmpty then
          pairs := pairs.set! (pairs.size - 1) (pairs[pairs.size - 1]!.1, some child)
      else pairs := pairs.push (child, none)
    match ← seam_comma_list? walk left "]" (args[0]?.getD .missing) pairs
        (args[2]?.getD .missing) with
    | some doc => return doc
    | none => return (← verbatim stx)
  match ← comma_group walk left "]" children with
  | some doc => return doc
  | none => return (← verbatim stx "collection-multiline-piece")

/-- Mathlib's `{ binder | predicate }` extended set-builder notation. -/
private partial
def set_builder_doc (walk : Walk) (stx : Lean.Syntax) (args : Array Lean.Syntax) : emit_m Doc := do
  if args.size != 5 || Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← verbatim stx "set-builder-shape")
  let left := (bare_src args[0]!).trimAscii.toString
  let some binder := Lean4Fmt.Emit.token_join_flat? args[1]!
      | return (← verbatim stx "set-builder-binder")
  let separator := (bare_src args[2]!).trimAscii.toString
  let right := (bare_src args[4]!).trimAscii.toString
  if left.isEmpty || binder.isEmpty || separator.isEmpty || right.isEmpty then
    return (← verbatim stx "set-builder-tokens")
  let predicateDoc ← walk args[3]!
  if (predicateDoc matches .verbatim _ _)
      || Lean4Fmt.Doc.has_midline_reanchor predicateDoc then
    return (← verbatim stx "set-builder-predicate")
  let head := left ++ binder ++ " " ++ separator
  return .text head ++ .group (.nest 2 (.line ++ predicateDoc)) ++ .text right

private partial
def match_term_doc (walk : Walk) (stx : Lean.Syntax) (args : Array Lean.Syntax) : emit_m Doc := do
  let middleParts :=
    (#[args[1]?, args[2]?, args[3]?].filterMap id).toList.filterMap fun termSyntax =>
      let text := Lean4Fmt.Emit.canon_tok termSyntax
      if text.isEmpty then none else some text
  let head := "match " ++ String.intercalate " " middleParts ++ " with"
  let some alternativesNode := args[5]? | return (← verbatim stx)
  let alternatives := Lean4Fmt.Emit.match_alts_of alternativesNode
  if alternatives.isEmpty || head.any (· == '\n') then
    return (← verbatim stx)
  let some pieces ←
      Lean4Fmt.Emit.arm_pieces? walk alternatives Lean4Fmt.Emit.token_join_flat?
    | return (← verbatim stx)
  let alignment := (← read).alignment
  return .text head
    ++ Lean4Fmt.Emit.arms_aligned_runs alignment.matchArms alignment.maxDelta pieces

private
structure tuple_state where
  elements : Array Lean.Syntax := #[]
  cursor   : Lean.Syntax
  steps    : Nat := 0
  docs     : Array Doc := #[]

private partial
def tuple_doc (walk : Walk) (stx : Lean.Syntax) (args : Array Lean.Syntax) : emit_m Doc := do
  let mut state : tuple_state := { cursor := args[1]?.getD .missing }
  while state.cursor.getKind == `null && state.cursor.getArgs.size == 3
      && state.steps < 1000 do
    state :=
      { state with
        elements := state.elements.push state.cursor.getArgs[0]!
        cursor := state.cursor.getArgs[2]!
        steps := state.steps + 1 }
  if state.cursor.getKind == `null && state.cursor.getArgs.size == 1 then
    state := { state with cursor := state.cursor.getArgs[0]! }
  if state.elements.isEmpty then
    return (← verbatim stx)
  state := { state with elements := state.elements.push state.cursor }
  for element in state.elements do
    state := { state with docs := state.docs.push (← walk element) }
  return Lean4Fmt.Doc.comma_list "(" ")" state.docs

private partial
def ite_doc (walk : Walk) (stx : Lean.Syntax) (args : Array Lean.Syntax) : emit_m Doc := do
  for slot in [args[1]?, args[3]?] do
    let text := ((slot.bind Lean4Fmt.Syntax.last_token_trailing?).getD "").trimAscii.toString
    if !text.isEmpty then
      return (← verbatim stx)
  for slot in [args[3]?, args[5]?] do
    if Lean4Fmt.Syntax.count_line_comments ((slot.bind Lean4Fmt.Syntax.leading?).getD "") > 0 then
      return (← verbatim stx "ite-branch-leading-comment")
  let condition ← walk (args[1]?.getD .missing)
  let thenBranch ← walk (args[3]?.getD .missing)
  let elseBranch ← walk (args[5]?.getD .missing)
  let elseIsIte :=
    (
      args[5]?.map fun branch =>
        branch.getKind == Lean4Fmt.Syntax.ite_kind || branch.getKind == Lean4Fmt.Syntax.dite_kind
    ).getD
      false
  let elseTail :=
    if (← read).breaking.elseIfChain && elseIsIte then
      .text "else " ++ elseBranch
    else
      .text "else" ++ .nest 2 (.line ++ elseBranch)
  return .group
    (
      .text "if " ++ condition ++ .text " then" ++ .nest 2 (.line ++ thenBranch) ++ .line
          ++ elseTail
    )

private
structure let_chain_state where
  doc    : Doc := .nil
  cursor : Lean.Syntax
  first  : Bool := true
  steps  : Nat := 0

private partial
def let_chain_step? (walk : Walk) (state : let_chain_state) : emit_m (Option let_chain_state) := do
  let args := state.cursor.getArgs
  if args.size < 5 then
    return none
  let leading := (Lean4Fmt.Syntax.leading? state.cursor).getD ""
  let mut doc := state.doc
  if !state.first then
    let some separator := Lean4Fmt.Emit.leading_sep? leading | return none
    doc := doc ++ separator
  else
    let whitespaceOnly (line : String) : Bool := line.all fun char => char == ' ' || char == '\t'
    if !(((leading.splitOn "\n").drop 1).dropLast.all whitespaceOnly) then
      let some separator := Lean4Fmt.Emit.leading_sep? leading | return none
      doc := doc ++ separator
  let configText := (((args[1]?.map bare_src).getD "").trimAscii.toString)
  if configText.any (· == '\n') then
    return none
  let declaration := args[2]?.getD .missing
  let declarationDoc ← walk declaration
  if (match declarationDoc with | .verbatim _ _ => true | _ => false)
      || Lean4Fmt.Doc.has_midline_reanchor declarationDoc then return none
  let separatorText := (((args[3]?.map bare_src).getD "").trimAscii.toString)
  if separatorText.any (· == '\n') || separatorText == ";" then
    return none
  let trailingText := ((Lean4Fmt.Syntax.trailing? declaration).getD "").trimAscii.toString
  if trailingText.any (· == '\n') then
    return none
  let configDoc := if configText.isEmpty then .nil else .text configText ++ .space
  let keywordText := (bare_src (args[0]?.getD .missing)).trimAscii.toString
  if keywordText.isEmpty then
    return none
  doc :=
    doc ++ .text (keywordText ++ " ") ++ configDoc ++ declarationDoc ++ .text separatorText
        ++ (if trailingText.isEmpty then .nil else .text (" " ++ trailingText))
  return some
    {
      doc
      cursor := args[args.size - 1]?.getD .missing
      first := false
      steps := state.steps + 1
    }

private partial
def let_chain_doc (walk : Walk) (stx : Lean.Syntax) : emit_m Doc := do
  let mut state : let_chain_state := { cursor := stx }
  while (state.cursor.getKind == ``Lean.Parser.Term.let
      || state.cursor.getKind == ``Lean.Parser.Term.have
      || state.cursor.getKind == ``Lean.Parser.Term.letI
      || state.cursor.getKind == ``Lean.Parser.Term.haveI)
      && state.steps < 10000 do
    let some next ← let_chain_step? walk state | return (← verbatim stx)
    state := next
  let some bodySeparator :=
    Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? state.cursor).getD "")
      | return (← verbatim stx)
  return state.doc ++ bodySeparator ++ (← walk state.cursor)

private partial
def let_decl_doc (walk : Walk) (stx : Lean.Syntax) (args : Array Lean.Syntax) : emit_m Doc := do
  match args[0]? with
  | some inner => return (← walk inner)
  | none => return (← verbatim stx)

/-- Bounded syntax-kind tree for actionable structural fallback diagnostics. -/
private partial
def syntax_kind_tree (syntaxNode : Lean.Syntax) (fuel : Nat := 4) : String :=
  if fuel == 0 || syntaxNode.getArgs.isEmpty then
    syntaxNode.getKind.toString
  else
    let children := syntaxNode.getArgs.toList.map (syntax_kind_tree · (fuel - 1))
    s!"{syntaxNode.getKind}[{String.intercalate "," children}]"

private partial
def binding_head_doc? (walk : Walk) (args : Array Lean.Syntax) : emit_m (Option Doc) := do
  if args.size != 5 || (bare_src args[3]!).trimAscii.toString != ":=" then
    return none
  let headParts := ((args.extract 0 2).map Lean4Fmt.Emit.canon_tok).filter fun text => !text.isEmpty
  let head := String.intercalate " " headParts.toList
  if head.any (· == '\n') then
    return none
  let typeText := Lean4Fmt.Emit.canon_tok (args[2]?.getD .missing)
  if head.isEmpty && typeText.isEmpty then
    return some .nil
  if typeText.isEmpty then
    return some (.text head)
  if !typeText.any (· == '\n') then
    return some (.text (if head.isEmpty then typeText else head ++ " " ++ typeText))
  let wrappedType := args[2]!
  let typeSpec :=
    if wrappedType.getKind == Lean.nullKind && wrappedType.getArgs.size == 1 then
      wrappedType.getArgs[0]!
    else
      wrappedType
  let typeNode :=
    if typeSpec.getKind == ``Lean.Parser.Term.typeSpec then
      typeSpec.getArgs[1]?.getD .missing
    else
      .missing
  if typeNode.isMissing then
    return none
  let typeDoc ← walk typeNode
  if (match typeDoc with | .verbatim _ _ => true | _ => false)
      || Lean4Fmt.Doc.hasMultilineVerbatim typeDoc then
    emit_diag
      { severity := .debug,
        pos := (typeNode.getPos?.map (·.byteIdx)).getD 0,
        rule := "binding-type",
        message := s!"unhandled binding type: {syntax_kind_tree typeNode}" }
    return none
  return some
    (.text (if head.isEmpty then ":" else head ++ " :") ++ .group (.nest 4 (.line ++ typeDoc)))

private partial
def multiline_binding_value_doc
    (stx : Lean.Syntax)
    (head valueDoc : Doc)
    (anonymous : Bool)
    : emit_m Doc := do
  if Lean4Fmt.Doc.has_midline_reanchor valueDoc then
    return (← verbatim stx)
  -- A whole opaque multiline value is safe at this explicit line-start seam:
  -- its stored base indent re-anchors under the binding's +2 nest. Reject only
  -- opaque pieces embedded after active mid-line content (the check above).
  return head ++ .text (if anonymous then ":=" else " :=") ++ .nest 2 (.hardline ++ valueDoc)

private partial
def binding_value_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (head : Doc)
    (value : Lean.Syntax)
    (anonymous : Bool)
    : emit_m Doc := do
  let valueDoc ← walk value
  let inlineAssign := if anonymous then ":= " else " := "
  let breakAssign := if anonymous then ":=" else " :="
  if value.getKind == ``Lean.Parser.Term.do || value.getKind == ``Lean.Parser.Term.byTactic then
    return head ++ .text inlineAssign ++ valueDoc
  if Lean4Fmt.Syntax.is_fun_block_value value
      && !(match valueDoc with | .verbatim _ _ => true | _ => false) then
    return head ++ .text inlineAssign ++ valueDoc
  if ((Lean4Fmt.Doc.left_edge_text? valueDoc).map (·.startsWith "{")).getD false
      && !Lean4Fmt.Doc.hasMultilineVerbatim valueDoc then
    return head ++ .text inlineAssign ++ valueDoc
  if Lean4Fmt.Doc.hasMultilineVerbatim valueDoc then
    return (← multiline_binding_value_doc stx head valueDoc anonymous)
  return head ++ .text breakAssign ++ .group (.nest 2 (.line ++ valueDoc))

private partial
def binding_doc (walk : Walk) (stx : Lean.Syntax) (args : Array Lean.Syntax) : emit_m Doc := do
  let some head ← binding_head_doc? walk args | return (← verbatim stx)
  let anonymous := (args.extract 0 3).all (Lean4Fmt.Emit.canon_tok · |>.isEmpty)
  binding_value_doc walk stx head args[4]! anonymous

private partial
def letrec_doc (walk : Walk) (stx : Lean.Syntax) (args : Array Lean.Syntax) : emit_m Doc := do
  if args.size != 4 then
    return (← verbatim stx)
  let keywordText := (bare_src args[0]!).trimAscii.toString
  if keywordText.any (· == '\n') then
    return (← verbatim stx)
  let declarations := ((args[1]!.getArgs[0]?).map (·.getArgs)).getD #[]
  if declarations.size != 1 then
    return (← verbatim stx)
  let declaration := declarations[0]!
  if declaration.getKind != ``Lean.Parser.Term.letRecDecl || declaration.getArgs.size != 4 then
    return (← verbatim stx)
  if !(bare_src declaration.getArgs[0]!).trimAscii.toString.isEmpty
      || !(bare_src declaration.getArgs[1]!).trimAscii.toString.isEmpty
      || !(bare_src declaration.getArgs[3]!).trimAscii.toString.isEmpty then
    return (← verbatim stx)
  let declarationDoc ← walk declaration.getArgs[2]!
  if Lean4Fmt.Doc.hasMultilineVerbatim declarationDoc then
    return (← verbatim stx)
  let separatorText := (((args[2]?.map bare_src).getD "").trimAscii.toString)
  if separatorText.any (· == '\n') then
    return (← verbatim stx)
  let body := args[3]!
  let some bodySeparator := Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? body).getD "")
      | return (← verbatim stx)
  return .text (keywordText ++ " ") ++ declarationDoc ++ .text separatorText ++ bodySeparator
      ++ (← walk body)

private partial
def forall_doc (walk : Walk) (stx : Lean.Syntax) (args : Array Lean.Syntax) : emit_m Doc := do
  if args.size != 5 then
    return (← verbatim stx)
  let keywordText := (bare_src args[0]!).trimAscii.toString
  if keywordText.isEmpty then
    return (← verbatim stx)
  let mut head : Doc := .text keywordText
  for binder in args[1]!.getArgs do
    let binderDoc ← Lean4Fmt.Emit.binder_doc walk binder
    if Lean4Fmt.Doc.hasMultilineVerbatim binderDoc then
      return (← verbatim stx)
    head := head ++ .space ++ binderDoc
  let optionalText := (bare_src args[2]!).trimAscii.toString
  if optionalText.any (· == '\n') then
    return (← verbatim stx)
  if !optionalText.isEmpty then head := head ++ .text (" " ++ optionalText)
  let bodyDoc ← walk args[4]!
  if Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc then
    return (← verbatim stx)
  let continuationIndent := (← read).layout.continuationIndent
  return head ++ .text "," ++ .group (.nest continuationIndent (.line ++ bodyDoc))

private
structure struct_fields where
  fields : Array Lean.Syntax := #[]
  pairs  : Array (Lean.Syntax × Option Lean.Syntax) := #[]
  commas : Nat := 0

private
def collect_struct_fields (args : Array Lean.Syntax) : struct_fields :=
  Id.run do
    let mut state : struct_fields := {}
    for group in ((args[2]?.map (·.getArgs)).getD #[]) do
      for child in group.getArgs do
        if child.getKind == ``Lean.Parser.Term.structInstField then
          state := { state with
            fields := state.fields.push child
            pairs := state.pairs.push (child, none)
          }
        else if child.isAtom && bare_src child == "," then
          let pairs :=
            if state.pairs.isEmpty then
              state.pairs
            else
              state.pairs.set!
                (state.pairs.size - 1)
                (state.pairs[state.pairs.size - 1]!.1, some child)
          state := { state with pairs, commas := state.commas + 1 }
    return state

private partial
def vertical_struct_doc?
    (walk : Walk)
    (stx : Lean.Syntax)
    (sourceText : String)
    (fields : Array Lean.Syntax)
    : emit_m (Option Doc) := do
  for field in fields do
    if Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? field).getD "") > 0
        || Lean4Fmt.Syntax.count_line_comments
          ((Lean4Fmt.Syntax.last_token_trailing? field).getD "") > 0 then
      return none
  let mut body : Doc := .nil
  for field in fields do
    let fieldDoc ← struct_field_doc walk field
    if contains_comma_struct_inst field
        || (match fieldDoc with | .verbatim _ _ => true | _ => false)
        || Lean4Fmt.Doc.has_midline_reanchor fieldDoc then
      return none
    body := body ++ .hardline ++ fieldDoc
  if sourceText.isEmpty then
    return some (.text "{" ++ .nest 2 body ++ .hardline ++ .text "}")
  return some (.text ("{ " ++ sourceText) ++ .nest 2 body ++ .hardline ++ .text "}")

private partial
def aligned_struct_row?
    (walk : Walk)
    (field : Lean.Syntax)
    (idx size : Nat)
    : emit_m (Option (List Doc)) := do
  let fieldArgs := field.getArgs
  let lvalueText := Lean4Fmt.Emit.canon_tok (fieldArgs[0]?.getD .missing)
  if lvalueText.isEmpty || lvalueText.any (· == '\n') then
    return none
  let rest := (fieldArgs[1]?.getD Lean.Syntax.missing).getArgs
  let some definition := rest.find? (·.getKind == ``Lean.Parser.Term.structInstFieldDef)
      | return none
  let value := (definition.getArgs[definition.getArgs.size - 1]?).getD .missing
  let valueDoc ← walk value
  if (Lean4Fmt.Doc.flat_width valueDoc).isNone then
    return none
  let last := idx + 1 == size
  return some
    [
      .text ((if idx == 0 then "{ " else "  ") ++ lvalueText),
      .text ":=",
      valueDoc ++ .text (if last then " }" else ",")
    ]

private partial
def aligned_struct_doc?
    (walk : Walk)
    (fields : Array Lean.Syntax)
    (groupForm : Doc)
    : emit_m (Option Doc) := do
  let alignment := (← read).alignment
  if alignment.recordFields == .never || fields.size < 2 then
    return none
  let mut rows : List (List Doc) := []
  let mut valid := true
  for h : idx in [0:fields.size] do
    let some row ← aligned_struct_row? walk fields[idx]! idx fields.size
      | valid := false; continue
    rows := rows ++ [row]
  if !valid then
    return none
  let cap := if alignment.recordFields == .always then 1000000 else alignment.maxDelta
  return some (Doc.align_or { sep := " ", maxDelta := cap } rows groupForm)

/-- A struct instance the active layout cannot own: a multi-line `with`
    source spread, an ellipsis, or occupied slots between the fields and the
    closer. -/
private
def struct_inst_unportable (args : Array Lean.Syntax) (sourceText : String) : Bool :=
  Id.run do
    let ellipsisEmpty := ((args[3]?.map bare_src).getD "").trimAscii.toString.isEmpty
    if sourceText.any (· == '\n') || !ellipsisEmpty then
      return true
    for idx in [4:args.size - 1] do
      if !((args[idx]?.map bare_src).getD "").trimAscii.toString.isEmpty then
        return true
    return false

private partial
def struct_inst_doc (walk : Walk) (stx : Lean.Syntax) (args : Array Lean.Syntax) : emit_m Doc := do
  if Lean4Fmt.Syntax.subtree_has_block_comment stx
      || Lean4Fmt.Syntax.has_block_comment (bare_src stx) then
    return (← verbatim stx "struct-block-comment")
  let sourceEmpty := ((args[1]?.map bare_src).getD "").trimAscii.toString.isEmpty
  let sourceText := if sourceEmpty then "" else Lean4Fmt.Emit.canon_tok (args[1]?.getD .missing)
  if struct_inst_unportable args sourceText then
    return (← verbatim stx)
  let parsed := collect_struct_fields args
  if parsed.fields.isEmpty then
    return (← verbatim stx)
  if parsed.fields.size > 1 && parsed.commas + 1 != parsed.fields.size then
    if parsed.commas != 0 then
      return (← verbatim stx)
    let some doc ← vertical_struct_doc? walk stx sourceText parsed.fields
      | return (← verbatim stx)
    return doc
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    if !sourceText.isEmpty then
      return (← verbatim stx)
    let some doc ← seam_comma_list? walk "{" "}" (args[0]?.getD .missing) parsed.pairs
        (args[args.size - 1]?.getD .missing)
      | return (← verbatim stx)
    return doc
  let mut docs : Array Doc := #[]
  for field in parsed.fields do
    docs := docs.push (← struct_field_doc walk field)
  let groupForm :=
    if sourceText.isEmpty then
      .group (.text "{ " ++ .nest 2 (Lean4Fmt.Doc.sep_by (.text "," ++ .line) docs) ++ .text " }")
    else
      .group
        (
          .text ("{ " ++ sourceText)
              ++ .nest 2 (.line ++ Lean4Fmt.Doc.sep_by (.text "," ++ .line) docs)
              ++ .text " }"
        )
  if sourceText.isEmpty then
    let some aligned ← aligned_struct_doc? walk parsed.fields groupForm | return groupForm
    return aligned
  return groupForm

private partial
def paren_term_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do

  -- "(" content ")" — content is args[1] (may be empty for unit)
  match args[1]? with
  | some content => return (← paren_doc walk stx content)
  | none => return .text "()"

private partial
def projection_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do

  -- obj "." field   (args[0]=obj, args[1]=".", args[2]=field)
  return (← walk args[0]!) ++ .text "." ++ (← walk (args[2]?.getD .missing))

private partial
def dot_ident_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do return .text "." ++ (← walk (args[1]?.getD .missing))

private partial
def anonymous_ctor_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do
  let children := (args[1]?.map (·.getArgs)).getD #[]
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    let mut pairs : Array (Lean.Syntax × Option Lean.Syntax) := #[]
    for child in children do
      if child.isAtom then
        if !pairs.isEmpty then
          pairs := pairs.set! (pairs.size - 1) (pairs[pairs.size - 1]!.1, some child)
      else pairs := pairs.push (child, none)
    match ← seam_comma_list? walk "⟨" "⟩" (args[0]?.getD .missing) pairs (args[2]?.getD .missing) with
    | some document => return document
    | none => return (← verbatim stx)
  match ← comma_group walk "⟨" "⟩" children with
  | some document => return document
  | none => return (← verbatim stx "anonymous-ctor-multiline-piece")

private partial
def dependent_ite_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do

  -- [if, binderIdent, :, cond, then, thenBranch, else, elseBranch] — the
  -- dependent `if h : c then … else …`; same layout as termIfThenElse,
  -- same interior-tail comment bail (no seam for `… then x -- note`).
  for slot in [args[3]?, args[5]?] do
    let trailingText :=
      ((slot.bind Lean4Fmt.Syntax.last_token_trailing?).getD "").trimAscii.toString
    if !trailingText.isEmpty then
      return (← verbatim stx)
  -- and the branch-LEADING comment bail (see termIfThenElse)
  for slot in [args[5]?, args[args.size - 1]?] do
    if Lean4Fmt.Syntax.count_line_comments ((slot.bind Lean4Fmt.Syntax.leading?).getD "") > 0 then
      return (← verbatim stx "ite-branch-leading-comment")
  let binder ← walk (args[1]?.getD .missing)
  let cond ← walk (args[3]?.getD .missing)
  let thenB ← walk (args[5]?.getD .missing)
  let elseB ← walk (args[args.size-1]?.getD .missing)
  -- else-if CHAIN (breaking.elseIfChain): a nested ite in the else slot
  -- glues (`else if … then`) instead of breaking to `else` + line
  let elseIsIte :=
    (
      args[args.size-1]?.map
        (
          fun expression =>
            expression.getKind == Lean4Fmt.Syntax.ite_kind
                || expression.getKind == Lean4Fmt.Syntax.dite_kind
        )
    ).getD
      false
  let elseTail : Doc :=
    if (← read).breaking.elseIfChain && elseIsIte then
      .text "else " ++ elseB
    else
      .text "else" ++ .nest 2 (.line ++ elseB)
  return .group
    (
      .text "if " ++ binder ++ .text " : " ++ cond ++ .text " then" ++ .nest 2 (.line ++ thenB)
          ++ .line
          ++ elseTail
    )

private partial
def function_alternatives_doc
    (walk : Walk)
    (stx functionSyntax : Lean.Syntax)
    (args : Array Lean.Syntax)
    : emit_m Doc := do
  match Lean4Fmt.Emit.token_join_flat? stx with
  | some text =>
    if !text.any (· == '\n') && text.length + 4 ≤ (← read).layout.lineWidth then
      return .text text
  | none => pure ()
  let keyword := (bare_src args[0]!).trimAscii.toString
  if keyword.isEmpty then
    return (← verbatim stx)
  let alternatives := Lean4Fmt.Emit.match_alts_of functionSyntax
  if alternatives.isEmpty then
    return (← verbatim stx)
  let some pieces ←
      Lean4Fmt.Emit.arm_pieces? walk alternatives Lean4Fmt.Emit.token_join_flat?
    | return (← verbatim stx)
  let alignment := (← read).alignment
  return .text keyword
    ++ .nest 2
      (Lean4Fmt.Emit.arms_aligned_runs alignment.matchArms alignment.maxDelta pieces)

private
def basic_function_head?
    (args basicArgs : Array Lean.Syntax)
    : Option (String × String × Lean.Syntax) :=
  Id.run do
    if basicArgs.size != 4 then
      return none
    let mut head := (bare_src args[0]!).trimAscii.toString
    if head.isEmpty then
      return none
    for binder in ((basicArgs[0]?).map (·.getArgs)).getD #[] do
      let text := Lean4Fmt.Emit.canon_tok binder
      if text.isEmpty || text.any (· == '\n') then
        return none
      head := head ++ " " ++ text
    let typeText := (basicArgs[1]?.map Lean4Fmt.Emit.canon_tok).getD ""
    if typeText.any (· == '\n') then
      return none
    if !typeText.isEmpty then head := head ++ " " ++ typeText
    let arrowText := (bare_src basicArgs[2]!).trimAscii.toString
    let arrowText := if arrowText.isEmpty then "=>" else arrowText
    return some (head, arrowText, basicArgs[3]!)

private partial
def multiline_function_body_doc
    (stx : Lean.Syntax)
    (head arrowText : String)
    (bodyDoc : Doc)
    : emit_m Doc := do
  if let .verbatim _ _ := bodyDoc then
    return (← verbatim stx)
  if Lean4Fmt.Doc.has_midline_reanchor bodyDoc then
    return (← verbatim stx)
  return .text (head ++ " " ++ arrowText) ++ .nest 2 (.hardline ++ bodyDoc)

private partial
def function_body_doc
    (walk : Walk)
    (stx body : Lean.Syntax)
    (head arrowText : String)
    : emit_m Doc := do
  let bodyDoc ← walk body
  if body.getKind == ``Lean.Parser.Term.do || body.getKind == ``Lean.Parser.Term.byTactic then
    -- glued do/by body: members at sequence seams; a bare-verbatim
    -- block bails (mid-line glue is the master fixed-point class)
    match bodyDoc with
    | .verbatim _ _ => return (← verbatim stx)
    | _ => return .text (head ++ " " ++ arrowText ++ " ") ++ bodyDoc
  -- the vertical structInst body glues by its unconditional `{` left
  -- edge — house shape `fun a b => {` … `}` (same seam as letIdDecl)
  if ((Lean4Fmt.Doc.left_edge_text? bodyDoc).map (·.startsWith "{")).getD false
      && !Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc then
    return .text (head ++ " " ++ arrowText ++ " ") ++ bodyDoc
  -- a MATCH body glues too (`fun s => match s with` riding, arms at
  -- their hardline seams below at +2 — the house shape)
  if body.getKind == ``Lean.Parser.Term.match
      && !Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc
      && !(match bodyDoc with | .verbatim _ _ => true | _ => false) then
    return .text (head ++ " " ++ arrowText ++ " ") ++ .nest 2 bodyDoc
  if Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc then
    -- multi-line opaque body: OWN-LINE at +2 is a deterministic seam
    -- (the fun class was 26KB of the wide census and the interior piece
    -- of half the chain bails)
    return (← multiline_function_body_doc stx head arrowText bodyDoc)
  return .text (head ++ " " ++ arrowText) ++ .group (.nest 2 (.line ++ bodyDoc))

private partial
def function_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (_kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do
  let some functionSyntax := args[1]? | return (← verbatim stx)
  if functionSyntax.getKind == ``Lean.Parser.Term.matchAlts then
    return (← function_alternatives_doc walk stx functionSyntax args)
  if functionSyntax.getKind != ``Lean.Parser.Term.basicFun then
    return (← verbatim stx)
  let some (head, arrowText, body) := basic_function_head? args functionSyntax.getArgs
      | return (← verbatim stx)
  function_body_doc walk stx body head arrowText

private partial
def negation_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do

  -- prefix negation over a (possibly multi-line) operand; GLUED (`¬p`,
  -- `¬(a = b)`) — the community convention, and mathlib's at 60:1
  let opT := (bare_src args[0]!).trimAscii.toString
  if opT.isEmpty || opT.any (· == '\n') then
    return (← verbatim stx)
  let document ← walk args[1]!
  if Lean4Fmt.Doc.hasMultilineVerbatim document then
    return (← verbatim stx)
  return .text opT ++ document

private partial
def hole_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do return .text "_"

private partial
def literal_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do

  -- literal: exact token; multi-line strings are CONTENT (quiet — not an
  -- actionable opt-out)
  let text := bare_src stx
  if !text.isEmpty && !text.any (· == '\n') then
    return .text text
  return (← verbatim_quiet stx)

private partial
def commented_application_doc
    (walk : Walk)
    (stx function : Lean.Syntax)
    (functionDoc : Doc)
    (arguments : Array Lean.Syntax)
    (indent : Nat)
    : emit_m Doc := do
  if Lean4Fmt.Syntax.interior_has_line_comment function then
    return (← verbatim stx)
  let mut argumentsDoc : Doc := .nil
  for h : idx in [0:arguments.size] do
    let argument := arguments[idx]
    let last := idx + 1 == arguments.size
    let some separator := Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? argument).getD "")
        | return (← verbatim stx)
    let trailingText := ((Lean4Fmt.Syntax.trailing? argument).getD "").trimAscii.toString
    if !last && trailingText.any (· == '\n') then
      return (← verbatim stx)
    let trailingDoc := if !last && !trailingText.isEmpty then .text (" " ++ trailingText) else .nil
    argumentsDoc := argumentsDoc ++ separator ++ (← walk argument) ++ trailingDoc
  return functionDoc ++ .nest indent argumentsDoc

private partial
def glued_application_doc?
    (walk : Walk)
    (functionDoc : Doc)
    (arguments : Array Lean.Syntax)
    : emit_m (Option Doc) := do
  if arguments.isEmpty then
    return none
  let lastArgument := arguments[arguments.size - 1]!
  let glue :=
    lastArgument.getKind == ``Lean.Parser.Term.do
        || lastArgument.getKind == ``Lean.Parser.Term.byTactic
        || ((← read).breaking.glueFun && lastArgument.getKind == ``Lean.Parser.Term.fun)
  if !glue then
    return none
  let lastDoc ← walk lastArgument
  let hazard :=
    lastArgument.getKind == ``Lean.Parser.Term.fun && Lean4Fmt.Doc.has_midline_reanchor lastDoc
  if (match lastDoc with | .verbatim _ _ => true | _ => false) || hazard then
    return none
  let mut head := functionDoc
  let mut flat := (Lean4Fmt.Doc.flat_width functionDoc).isSome
  for h : idx in [0:arguments.size - 1] do
    let argumentDoc ← walk arguments[idx]!
    if (Lean4Fmt.Doc.flat_width argumentDoc).isNone then flat := false
    head := head ++ .space ++ argumentDoc
  if !flat then
    return none
  return some (.flatten head ++ .space ++ lastDoc)

private partial
def has_struct_shorthand_field (stx : Lean.Syntax) : Bool :=
  if stx.getKind == ``Lean.Parser.Term.structInstField then
    !(stx.getArgs.any fun child =>
      child.getArgs.any (·.getKind == ``Lean.Parser.Term.structInstFieldDef))
  else
    stx.getArgs.any has_struct_shorthand_field

private partial
def contains_jsx_term (stx : Lean.Syntax) : Bool :=
  stx.getKind == `ProofWidgets.Jsx.term_ || stx.getArgs.any contains_jsx_term

/-- The parser-classified seam of every argument: `true` where the gap to the
    previous token is zero-width (unbreakably glued custom postfix syntax such
    as `L⟦n⟧`), `false` where whitespace gives a breakable application seam.
    The seam vector is syntax-derived, so routing and layout are stable across
    passes. -/
private
def argument_adjacency (function : Lean.Syntax) (arguments : Array Lean.Syntax) : Array Bool :=
  Id.run do
    let mut adjacency : Array Bool := #[]
    let mut previous := function
    for argument in arguments do
      let gap :=
        (Lean4Fmt.Syntax.last_token_trailing? previous).getD ""
            ++ (Lean4Fmt.Syntax.leading? argument).getD ""
      adjacency := adjacency.push gap.isEmpty
      previous := argument
    return adjacency

private partial
def application_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (_kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do
  let function := args[0]!
  let arguments := (args[1]?.map (·.getArgs)).getD #[]
  let indent := (← read).layout.indent
  -- A direct structure argument has an owned closing-brace seam. Keep nested
  -- shorthand-shaped subtrees inside custom syntax opaque: their outer macro
  -- may assign whitespace semantics not represented by ordinary application.
  if arguments.any fun argument =>
        argument.getKind != ``Lean.Parser.Term.structInst &&
        argument.getKind != `choice &&
        has_struct_shorthand_field argument &&
        (contains_jsx_term argument ||
          !argument.getArgs.any (fun child => child.getArgs.any has_struct_shorthand_field)) then
    return (← verbatim stx "nested-application-struct-shorthand")
  -- Preserve the parser-classified seam of every argument: whitespace gives a
  -- breakable application line; zero-width remains unbreakably glued.
  let adjacency := argument_adjacency function arguments
  let hasAdjacency := adjacency.any id
  let functionDoc ← walk function
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← commented_application_doc walk stx function functionDoc arguments indent)
  if !hasAdjacency then
    if let some glued ← glued_application_doc? walk functionDoc arguments then
      return glued
  let mut argumentsDoc : Doc := .nil
  for h : idx in [0:arguments.size] do
    let separator : Doc := if adjacency[idx]! then .nil else .line
    argumentsDoc := argumentsDoc ++ separator ++ (← walk arguments[idx]!)
  return .group (functionDoc ++ .nest indent argumentsDoc)

private
def binary_operator_text (args : Array Lean.Syntax) : String :=
  Lean4Fmt.Emit.canon_tok (Lean.mkNullNode (args.extract 1 (args.size - 1)))

private
def binary_operator_shape_safe (args : Array Lean.Syntax) : Bool :=
  let text :=
    if args.size == 3 then (bare_src args[1]!).trimAscii.toString else binary_operator_text args
  let forbidden := (text.toList.headD ' ') ∈ ['[', '(', '{', '⁻', '!', '?']
  if args.size == 3 then !forbidden else !text.isEmpty && !text.any (· == '\n') && !forbidden

private partial
def binary_operator_token? (walk : Walk) (args : Array Lean.Syntax) : emit_m (Option Doc) := do
  if args.size == 3 then
    return some (← walk args[1]!)
  let text := binary_operator_text args
  if text.isEmpty || text.any (· == '\n') then
    return none
  return some (.text text)

private
structure binary_chain_state where
  tail             : Doc
  previousOperator : Doc
  cursor           : Lean.Syntax
  steps            : Nat

private partial
def unroll_binary_chain?
    (walk : Walk)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    (operator : Doc)
    : emit_m (Option binary_chain_state) := do
  let mut state : binary_chain_state :=
    { tail := .nil, previousOperator := operator
      cursor := args[args.size - 1]!, steps := 0 }
  while state.cursor.getKind == kind
      && state.cursor.getArgs.size == args.size && state.steps < 64 do
    let childArgs := state.cursor.getArgs
    let some linkOperator ← binary_operator_token? walk childArgs
      | return none
    let piece ← walk childArgs[0]!
    state := {
      tail := state.tail ++ .line ++ state.previousOperator ++ .space ++ piece
      previousOperator := linkOperator
      cursor := childArgs[childArgs.size - 1]!
      steps := state.steps + 1
    }
  return some state

private
structure binary_layout where
  lhs      : Doc
  operator : Doc
  chain    : binary_chain_state
  rhs      : Doc

private
def binary_head (layout : binary_layout) : Doc :=
  layout.lhs ++ layout.chain.tail ++ .line ++ layout.chain.previousOperator

private
def glued_binary_layout? (layout : binary_layout) (lineWidth : Nat) : Option Doc :=
  let cursor := layout.chain.cursor
  let rhsDoBy := contains_do_by cursor
  let headFits :=
    match Lean4Fmt.Doc.flat_width (binary_head layout) with
    | some width => width + 12 ≤ lineWidth
    | none       => false
  let tailCanGlue :=
    cursor.getKind == ``Lean.Parser.Term.byTactic || cursor.getKind == ``Lean.Parser.Term.do
        || (rhsDoBy && headFits && tail_glue_safe cursor)
  let piecesFlat :=
    (Lean4Fmt.Doc.flat_width layout.lhs).isSome && (Lean4Fmt.Doc.flat_width layout.operator).isSome
        && (Lean4Fmt.Doc.flat_width layout.chain.tail).isSome
  let rhsSafe :=
    !(match layout.rhs with | .verbatim _ _ => true | _ => false)
        && !Lean4Fmt.Doc.has_midline_reanchor layout.rhs
  if tailCanGlue && piecesFlat && rhsSafe then
    some (.flatten (binary_head layout) ++ .space ++ layout.rhs)
  else
    none

private
def calc_binary_layout? (layout : binary_layout) (continuationIndent : Nat) : Option Doc :=
  let head := binary_head layout
  let rhsSafe :=
    !(match layout.rhs with | .verbatim _ _ => true | _ => false)
        && !Lean4Fmt.Doc.has_midline_reanchor layout.rhs
  if (Lean4Fmt.Doc.flat_width head).isSome && rhsSafe then
    some (.flatten head ++ .nest continuationIndent (.hardline ++ layout.rhs))
  else
    none

private
structure trailing_chain_state where
  tail   : Doc
  cursor : Lean.Syntax
  steps  : Nat

private partial
def trailing_binary_layout
    (walk : Walk)
    (stx : Lean.Syntax)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    (layout : binary_layout)
    : emit_m Doc := do
  let mut state : trailing_chain_state :=
    { tail := .nil, cursor := args[args.size - 1]!, steps := 0 }
  while state.cursor.getKind == kind
      && state.cursor.getArgs.size == args.size && state.steps < 64 do
    let childArgs := state.cursor.getArgs
    let some linkOperator ← binary_operator_token? walk childArgs
      | return (← verbatim stx "chain-op-shape")
    let piece ← walk childArgs[0]!
    state := {
      tail := state.tail ++ .line ++ piece ++ .space ++ linkOperator
      cursor := childArgs[childArgs.size - 1]!
      steps := state.steps + 1
    }
  let continuationIndent := (← read).layout.continuationIndent
  let result :=
    layout.lhs ++ .space ++ layout.operator
        ++ .nest continuationIndent (state.tail ++ .line ++ layout.rhs)
  if Lean4Fmt.Doc.has_midline_reanchor result then
    return (← verbatim stx "chain-multiline-piece")
  return .group result

private partial
def leading_binary_layout (stx : Lean.Syntax) (layout : binary_layout) : emit_m Doc := do
  let continuationIndent := (← read).layout.continuationIndent
  let result :=
    layout.lhs
        ++ .nest
          continuationIndent
          (layout.chain.tail ++ .line ++ layout.chain.previousOperator ++ .space ++ layout.rhs)
  if Lean4Fmt.Doc.has_midline_reanchor result then
    return (← verbatim stx "chain-multiline-piece")
  return .group result

private partial
def binary_operator_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do

  -- Child comments belong to the child walkers. Comments attached to an
  -- operator seam need a dedicated binary-chain placement law.
  let childComments :=
    Lean4Fmt.Syntax.count_subtree_line_comments args[0]!
        + Lean4Fmt.Syntax.count_subtree_line_comments args[args.size - 1]!
  let rhsLeadingComment :=
    Lean4Fmt.Syntax.has_line_comment ((Lean4Fmt.Syntax.leading? args[args.size - 1]!).getD "")
  if rhsLeadingComment then
    let lead := (Lean4Fmt.Syntax.leading? args[args.size - 1]!).getD ""
    let some separator := Lean4Fmt.Emit.leading_sep? lead
        | return (← verbatim stx "chain-rhs-comment-shape")
    let lhs ← walk args[0]!
    let some operator ← binary_operator_token? walk args
      | return (← verbatim stx "chain-op-shape")
    let rhs ← walk args[args.size - 1]!
    let continuationIndent := (← read).layout.continuationIndent
    return .group (lhs ++ .space ++ operator ++ .nest continuationIndent (separator ++ rhs))
  if Lean4Fmt.Syntax.count_subtree_line_comments stx > childComments then
    return (← verbatim stx "chain-operator-comment")
  if args.size >= 3 && !binary_operator_shape_safe args then
    return (← verbatim stx)
  let lhs ← walk args[0]!
  let some operator ← binary_operator_token? walk args
    | return (← verbatim stx "chain-op-shape")
  let some chain ← unroll_binary_chain? walk kind args operator
    | return (← verbatim stx "chain-op-shape")
  let rhs ← walk chain.cursor
  let layout : binary_layout := { lhs, operator, chain, rhs }
  let config ← read
  if let some glued := glued_binary_layout? layout config.layout.lineWidth then
    return glued
  -- Keep multiline calc steps anchored to a line-start seam.
  if chain.cursor.getKind == `Lean.calc && (bare_src chain.cursor).any (· == '\n') then
    if let some calcLayout :=
        calc_binary_layout? layout config.layout.continuationIndent then
      return calcLayout
    return (← verbatim stx "chain-calc-tail")
  -- Choose the configured broken form after all special tails are resolved.
  if config.breaking.opBreak == .trailing then
    return (← trailing_binary_layout walk stx kind args layout)
  leading_binary_layout stx layout

private partial
def show_type_doc?
    (walk : Walk)
    (typeSyntax : Lean.Syntax)
    (width : Nat)
    : emit_m (Option Doc) := do
  match Lean4Fmt.Emit.token_join_flat? typeSyntax with
  | some text =>
    if !text.isEmpty && !text.any (· == '\n') && text.length + 12 ≤ width then
      return some (.text text)
  | none => pure ()
  -- Long `show` types compose with the ordinary term emitter. Accept only a
  -- fully structural document: an opaque or midline-reanchoring type has no
  -- trustworthy seam before `from`/`by` and keeps the whole form verbatim.
  let typeNode :=
    if typeSyntax.getKind == Lean.nullKind && typeSyntax.getArgs.size == 1 then
      typeSyntax.getArgs[0]!
    else
      typeSyntax
  let typeDoc ← walk typeNode
  if (typeDoc matches .verbatim _ _) || Lean4Fmt.Doc.has_midline_reanchor typeDoc then
    return none
  return some typeDoc

private partial
def show_by_doc
    (walk : Walk)
    (stx rhs : Lean.Syntax)
    (keyword : String)
    (typeDoc : Doc)
    : emit_m Doc := do
  if !(((Lean4Fmt.Syntax.leading? rhs).getD "").trimAscii.toString.isEmpty) then
    return (← verbatim stx "show-by-lead-comment")
  let bodyDoc ← walk rhs
  let layout := .text (keyword ++ " ") ++ typeDoc ++ .text " " ++ bodyDoc
  if Lean4Fmt.Doc.has_midline_reanchor layout then
    return (← verbatim stx "show-by-shape")
  return layout

private partial
def show_from_doc
    (walk : Walk)
    (stx rhs : Lean.Syntax)
    (keyword : String)
    (typeDoc : Doc)
    : emit_m Doc := do
  let rhsArgs := rhs.getArgs
  let fromAtom := rhsArgs[0]?.getD .missing
  let fromSource := (bare_src fromAtom).trimAscii.toString
  let fromText := if fromSource.isEmpty then "from" else fromSource
  let value := rhsArgs[1]?.getD .missing
  for trivia in [(Lean4Fmt.Syntax.leading? fromAtom).getD "",
      (Lean4Fmt.Syntax.trailing? fromAtom).getD "",
      (Lean4Fmt.Syntax.leading? value).getD ""] do
    if !trivia.trimAscii.toString.isEmpty then
      return (← verbatim stx "show-from-comment")
  let valueDoc ← walk value
  let glue := value.getKind == ``Lean.Parser.Term.do || value.getKind == ``Lean.Parser.Term.byTactic
  let layout :=
    if glue then
      .text (keyword ++ " ") ++ typeDoc ++ .text (" " ++ fromText ++ " ") ++ valueDoc
    else
      .group
        (
          .text (keyword ++ " ") ++ typeDoc ++ .text (" " ++ fromText)
              ++ .nest 2 (.line ++ valueDoc)
        )
  if Lean4Fmt.Doc.has_midline_reanchor layout then
    return (← verbatim stx "show-from-shape")
  return layout

private partial
def show_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (_kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do

  -- Route the parse-stable `show` shapes through their dedicated layouts.
  let some typeSyntax := args[1]? | return (← verbatim stx)
  let some rhs := args[2]? | return (← verbatim stx)
  let keywordSource := (bare_src args[0]!).trimAscii.toString
  let keyword := if keywordSource.isEmpty then "show" else keywordSource
  if !(((Lean4Fmt.Syntax.trailing? args[0]!).getD "").trimAscii.toString.isEmpty) then
    return (← verbatim stx "show-head-comment")
  let some typeDoc ← show_type_doc? walk typeSyntax (← read).layout.lineWidth
      | return (← verbatim stx "show-type-shape")
  if rhs.getKind == `Lean.Parser.Term.byTactic'
      || rhs.getKind == ``Lean.Parser.Term.byTactic then
    return (← show_by_doc walk stx rhs keyword typeDoc)
  if rhs.getKind == ``Lean.Parser.Term.fromTerm then
    return (← show_from_doc walk stx rhs keyword typeDoc)
  return (← verbatim stx "show-rhs-shape")

private
def core_quantifier_pieces? (args : Array Lean.Syntax) : Option (Array String) :=
  Id.run do
    let mut pieces : Array String := #[]
    for child in args.extract 0 (args.size - 1) do
      let token := Lean4Fmt.Emit.canon_tok child
      if token.any (· == '\n') then
        let some nested := head_pieces? child | return none
        pieces := pieces ++ nested
      else if token == "," then
        if pieces.isEmpty then
          return none
        pieces := pieces.set! (pieces.size - 1) (pieces[pieces.size - 1]! ++ ",")
      else if !token.isEmpty then pieces := pieces.push token
    return if pieces.isEmpty then none else some pieces

private partial
def quantifier_body_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (head : Doc)
    (body : Lean.Syntax)
    : emit_m Doc := do
  let bodyDoc ← walk body
  if Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc then
    return (← verbatim stx)
  let continuationIndent := (← read).layout.continuationIndent
  return head ++ .group (.nest continuationIndent (.line ++ bodyDoc))

private partial
def core_quantifier_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (args : Array Lean.Syntax)
    : emit_m Doc := do
  let some pieces := core_quantifier_pieces? args | return (← verbatim stx)
  let joined := String.intercalate " " pieces.toList
  let continuationIndent := (← read).layout.continuationIndent
  let head :=
    if !joined.any (· == '\n') && joined.length + 1 ≤ (← read).layout.lineWidth then
      .text joined
    else
      .nest continuationIndent (Doc.fillSep (pieces.toList.map Doc.text))
  quantifier_body_doc walk stx head args[args.size - 1]!

private partial
def extended_quantifier_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (args : Array Lean.Syntax)
    : emit_m Doc := do
  let head := (bare_src (Lean.mkNullNode (args.extract 0 (args.size - 1)))).trimAscii.toString
  if head.isEmpty || head.any (· == '\n') then
    return (← verbatim stx)
  quantifier_body_doc walk stx (.text head) args[args.size - 1]!

private partial
def binder_quantifier_doc
    (walk : Walk)
    (stx : Lean.Syntax)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do
  if args.size < 2 then
    return (← verbatim stx)
  let core :=
    kind == `Lean.«term∀__,_» || kind == `Lean.«term∃__,_» || kind == `«term∃_,_»
        || kind == `«term∀_,_»
  if core then core_quantifier_doc walk stx args
  else extended_quantifier_doc walk stx args

private partial
def emit_node_tail
    (walk : Walk)
    (stx : Lean.Syntax)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do
  if kind == ``Lean.Parser.Term.let || kind == ``Lean.Parser.Term.have
      || kind == ``Lean.Parser.Term.letI || kind == ``Lean.Parser.Term.haveI then
    return (← let_chain_doc walk stx)
  else if kind == ``Lean.Parser.Term.letDecl then
    return (← let_decl_doc walk stx args)
  else if kind == ``Lean.Parser.Term.letIdDecl || kind == ``Lean.Parser.Term.letPatDecl
       || kind == ``Lean.Parser.Term.letIdDeclNoBinders then
    return (← binding_doc walk stx args)
  else if kind == ``Lean.Parser.Term.match then
    return (← match_term_doc walk stx args)
  else if kind == `Mathlib.Meta.setBuilder then
    return (← set_builder_doc walk stx args)
  else if kind == Lean4Fmt.Syntax.dite_kind then
    return (← dependent_ite_doc walk stx kind args)
  else if kind == ``Lean.Parser.Term.fun then
    return (← function_doc walk stx kind args)
  else if kind == ``Lean.Parser.Term.tuple then
    return (← tuple_doc walk stx args)
  else if kind == ``Lean.Parser.Term.letrec then
    return (← letrec_doc walk stx args)
  else if kind == ``Lean.Parser.Term.forall then
    return (← forall_doc walk stx args)
  else if kind == `Lean.«term∀__,_» || kind == `Lean.«term∃__,_»
      || kind == `«term∃_,_» || kind == `«term∀_,_»
      || Lean4Fmt.Syntax.is_binder_comma kind then
    return (← binder_quantifier_doc walk stx kind args)
  else if kind == `«term¬_» && args.size == 2 then
    return (← negation_doc walk stx kind args)
  else if kind == ``Lean.Parser.Term.hole then
    return (← hole_doc walk stx kind args)
  else if kind == `str || kind == `num || kind == `scientific || kind == `char then
    return (← literal_doc walk stx kind args)
  else
    return (← verbatim stx) -- not yet ported (let/match/do/if/…): opaque

private partial
def emit_node
    (walk : Walk)
    (stx : Lean.Syntax)
    (kind : Lean.SyntaxNodeKind)
    (args : Array Lean.Syntax)
    : emit_m Doc := do
  if (Lean4Fmt.Syntax.is_bin_op kind || kind == ``Lean.Parser.Term.arrow) && args.size ≥ 3 then
    return (← binary_operator_doc walk stx kind args)
  else if kind == ``Lean.Parser.Term.app then
    return (← application_doc walk stx kind args)
  else if kind == ``Lean.Parser.Term.paren then
    return (← paren_term_doc walk stx kind args)
  else if kind == ``Lean.Parser.Term.show then
    return (← show_doc walk stx kind args)
  else if kind == ``Lean.Parser.Term.proj then
    return (← projection_doc walk stx kind args)
  else if kind == ``Lean.Parser.Term.dotIdent then
    return (← dot_ident_doc walk stx kind args)
  else if kind == ``Lean.Parser.Term.anonymousCtor then
    return (← anonymous_ctor_doc walk stx kind args)
  else if kind == ``Lean.Parser.Term.structInst then
    return (← struct_inst_doc walk stx args)
  else if kind == Lean4Fmt.Syntax.list_lit_kind || kind == Lean4Fmt.Syntax.array_lit_kind then
    return (← collection_literal_doc walk stx kind args)
  else if kind == Lean4Fmt.Syntax.ite_kind then
    return (← ite_doc walk stx args)
  else
    return (← emit_node_tail walk stx kind args)

/-- Emit an expression construct, recursing via `walk`. Produces flat Doc for the
    handled kinds; everything else (and anything with a line comment) reproduces
    verbatim. -/
partial
def emit (walk : Walk) (stx : Lean.Syntax) : emit_m Doc := do
  let source := bare_src stx
  if stx.getKind == ``Lean.Parser.Term.paren
      && (source.splitOn "(calc\n").length > 1 then
    return (← verbatim stx "paren-calc")
  if stx.getKind == `Lean.calc && source.any (· == '\n') then
    return (← verbatim stx "calc-multiline")
  -- Mathlib shift notation is adjacency-sensitive at both delimiters and may
  -- carry a prime suffix (`X⟦n⟧'`). Generic application/operator spacing
  -- changes its macro expansion, so preserve the smallest owning term span.
  let ownsShiftNotation :=
    let containsShift (node : Lean.Syntax) := ((bare_src node).splitOn "⟦").length > 1
    let children := stx.getArgs
    let childContains := children.any containsShift
    let childIsSmallest :=
      children.any fun child => containsShift child && !child.getArgs.any containsShift
    (source.splitOn "⟦").length > 1 && (!childContains || childIsSmallest)
  if ownsShiftNotation then
    return (← verbatim stx "shift-notation")
  if !Lean4Fmt.Syntax.owns_seams stx.getKind
      && Lean4Fmt.Syntax.has_unowned_line_comment stx then
    return (← verbatim stx)
  match stx with
  | .atom _ value => return .text value
  | .ident _ _ name _ => return .text name.toString
  | .node _ kind args => emit_node walk stx kind args
  | .missing => return .nil

end Lean4Fmt.Emit.Term
