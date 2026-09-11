/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // LEAN4FMT // EMIT // DECL
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Declarations (def / theorem / abbrev / opaque / example). The first category
    ported from verbatim to real `Doc` production: the signature is reflowed as a
    breakable `group` (binders on `line`, so it fits on one line or breaks at
    width — a genuine Doc layout the source did not dictate), and the value is
    laid out after `:=`. Binder/type/value subtrees recurse via `walk` (currently
    opaque-reproduced), so this is correct token-for-token today and gets richer
    as more categories are ported. Anything not a plain def-shape declaration
    falls back to byte-exact passthrough.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.emit.monad
import lean_4_fmt.emit.tokens
import lean_4_fmt.emit.binders
import lean_4_fmt.emit.command
import lean_4_fmt.syntax.kinds
import lean_4_fmt.solve.layout

namespace Lean4Fmt.Emit.Decl

open Lean Lean4Fmt.Doc Lean4Fmt.Emit

/-- Mutable modifier-layout facts accumulated across token seams. -/
private
structure modifier_state where
  restSep : Option Doc := none
  seen    : Bool := false
  out     : Doc := .nil
  needNl  : Bool := false

private
structure modifier_parts where
  docText   : String
  attrText  : String
  attrTrail : String
  restParts : List String
  attrSep   : Option Doc
  restSep   : Option Doc
  kwSep     : Option Doc

private
def combine_separators (first second : Option Doc) : Option Doc :=
  match first, second with
  | some first, some second => some (first ++ second)
  | some first, none        => some first
  | none, some second       => some second
  | none, none              => none

private
def inline_modifier_text (parts : modifier_parts) : String :=
  let attributes := if parts.attrText.isEmpty then [] else [parts.attrText]
  String.intercalate " " (attributes ++ parts.restParts)

private
def assemble_modifiers (attrsOwnLine visOwnLine : Bool) (parts : modifier_parts) : Doc × Nat :=
  Id.run do
    let restStr := String.intercalate " " parts.restParts
    let restDoc : Doc := if parts.restParts.isEmpty then .nil else .text restStr ++ .space
    let restWidth := if parts.restParts.isEmpty then 0 else restStr.length + 1
    let preKeyword := combine_separators parts.restSep parts.kwSep
    let mut state : modifier_state := {}
    if attrsOwnLine || !parts.attrTrail.isEmpty then
      if !parts.docText.isEmpty then
        state := { state with out := .textRaw parts.docText, needNl := true }
      if !parts.attrText.isEmpty then
        if state.needNl then
          state := { state with out := state.out ++ (parts.attrSep.getD Doc.hardline) }
        state := { state with
          out := state.out ++ .text parts.attrText ++ .textRaw parts.attrTrail
          needNl := true
        }
      if visOwnLine && !parts.restParts.isEmpty then
        if state.needNl then
          state := { state with out := state.out ++ (parts.restSep.getD Doc.hardline) }
        return (state.out ++ .text restStr ++ (parts.kwSep.getD Doc.hardline), 0)
      if state.needNl then
        state := { state with out := state.out ++ (preKeyword.getD Doc.hardline) }
      return (state.out ++ restDoc, restWidth)
    let allStr := inline_modifier_text parts
    let inlineDoc : Doc := if allStr.isEmpty then .nil else .text allStr ++ .space
    let inlineWidth := if allStr.isEmpty then 0 else allStr.length + 1
    let seam := combine_separators parts.attrSep preKeyword
    let out :=
      if !parts.docText.isEmpty then
        .textRaw parts.docText ++ seam.getD Doc.hardline
      else
        seam.getD .nil
    return (out ++ inlineDoc, inlineWidth)

/-- Head and mutually exclusive value forms discovered in a `where` field. -/
private
structure where_field_state where
  head  : String
  defn? : Option Lean.Syntax := none
  eqns? : Option Lean.Syntax := none

/-- Instance head classification threaded across binders and result type. -/
private
structure instance_head_state where
  head      : String
  flatOk    : Bool := true
  headTail? : Option Doc := none

/-- Signature layout accumulator shared by adaptive, fill, and one-line modes. -/
private
structure sig_state where
  bindersWidth : Nat := 0
  simple       : Bool := true
  doc          : Doc := .nil
  binderDocs   : Array Doc := #[]
  flatWidth    : Nat := 0

/-- Emit a declaration's `declModifiers` = [docComment?, attributes?, visibility?,
    …]. The doc comment (always first) goes on its own line (literal `textRaw` —
    it may be multi-line — then a `hardline`). If `attrsOwnLine` (straylight),
    the attributes `@[…]` also get their own line above the keyword; otherwise
    they sit inline with the visibility modifiers on the keyword's line. Returns
    the doc and the width of the INLINE prefix it contributes to the keyword's
    line (used for signature width coupling and binder alignment: with
    attrsOwnLine only the visibility modifiers count, so binders align under the
    name at a shallower column). -/
private
def modifiers_doc
    (attrsOwnLine : Bool)
    (modeValue : Lean.Syntax)
    (kwLead : String := "")
    (visOwnLine : Bool := false)
    : Doc × Nat :=
  Id.run
    do
      let margs := modeValue.getArgs
      let docText := (margs[0]?.map bare_src).getD "" |>.trimAscii.toString
      let attrText := (margs[1]?.map bare_src).getD "" |>.trimAscii.toString
      let attrTrail := ((margs[1]?.bind Lean4Fmt.Syntax.trailing?).getD "").trimAsciiEnd.toString
      let restParts :=
        (margs.toList.drop 2).filterMap
          (
            fun child =>
              let text := (bare_src child).trimAscii.toString
              if text.isEmpty then none else some text
          )
      -- placed comment seams: full-line comments in a LATER piece's leading
      -- (`/-- doc -/` then `-- TODO` then `@[attr]` — the mathlib idiom) sit
      -- at the own-line seams between pieces and place via leadingSep?; the
      -- zone exists only BEHIND a preceding piece (with none, the leading is
      -- the declaration's OUTER leading — Module's to place; double emission
      -- otherwise, the ElementaryMaps law). Unownable shapes bailed in
      -- modifiersCommentHazard before we got here.
      let sepOf : String → Option Doc :=
        fun line =>
          if Lean4Fmt.Syntax.has_line_comment line || (line.splitOn "/-").length > 1 then
            Lean4Fmt.Doc.leading_sep? line
          else
            none
      let attrSep : Option Doc :=
        if !docText.isEmpty && !attrText.isEmpty then
          sepOf ((margs[1]?.bind Lean4Fmt.Syntax.leading?).getD "")
        else
          none
      let mut state : modifier_state := { seen := !docText.isEmpty || !attrText.isEmpty }
      for child in margs.toList.drop 2 do
        if (bare_src child).trimAscii.toString.isEmpty then continue
        if state.seen then
          match sepOf ((Lean4Fmt.Syntax.leading? child).getD "") with
          | some textValue =>
            state := { state with restSep := some ((state.restSep.getD .nil) ++ textValue) }
          | none => pure ()
        state := { state with seen := true }
      let kwSep : Option Doc := if state.seen then sepOf kwLead else none
      -- assembly with ONE owner per seam: a piece's sep (the comment lines
      -- from its leading) REPLACES the plain hardline before it — stacking
      -- both inserted a spurious blank (hardlines are unconditional
      -- newlines, only .blank pend-merges; the glueBodyBlank lesson)
      return assemble_modifiers
        attrsOwnLine
        visOwnLine
        { docText, attrText, attrTrail, restParts, attrSep, restSep := state.restSep, kwSep }

/-- Prefix an actively formatted declaration body with its owned modifiers. -/
private
def add_modifiers (attrsOwnLine visOwnLine : Bool) (outer defn : Lean.Syntax) (body : Doc) : Doc :=
  let (modsDoc, _) :=
    match outer.getArgs[0]? with
    | some modifiers =>
      modifiers_doc attrsOwnLine modifiers ((Lean4Fmt.Syntax.leading? defn).getD "") visOwnLine
    | none => (.nil, 0)
  modsDoc ++ body

/-- Keyword-led definition shapes we actively format. -/
private
def is_def_shape (kind : SyntaxNodeKind) : Bool :=
  kind == ``Lean.Parser.Command.definition || kind == ``Lean.Parser.Command.theorem
      || kind == ``Lean.Parser.Command.abbrev
      || kind == ``Lean.Parser.Command.opaque
      || kind == ``Lean.Parser.Command.example

/-- Whether a `declValEqns` can be actively laid out as `| pat => body` arms. Only
    when there is no line comment anywhere inside it (arm comments must be
    preserved byte-exact), no `where`/`termination_by` suffix on the
    `matchAltsWhereDecls`, and at least one arm. When this is false the WHOLE
    declaration falls back to verbatim (a `.span` of just the eqns would mangle:
    the signature would still be reformatted while the arms re-anchor wrongly, as
    there is no `:=` seam to anchor them). -/
private
def eqns_formattable (declVal : Lean.Syntax) : Bool :=
  Id.run
    do
      -- comments handle per-seam in the arm loop (between-arm comments place
      -- structurally; an arm-INTERIOR comment falls back there). declVal's HEAD
      -- leading (a comment between the signature and the first arm — the
      -- `-- ── section ──` header position) is the FIRST ARM's leading too, and
      -- the loop places it via leadingSep? — safe ONLY because every loop bail
      -- condition is pre-checked below (a mid-loop `.span` bail would silently
      -- drop it: the span's bare source excludes that leading — found exactly
      -- that way). Keep the mirror EXACT when touching either side.
      let mawd := (declVal.getArgs[0]?).getD .missing
      let margs := mawd.getArgs
      -- suffixes (`termination_by`/`where`) are allowed as verbatim tails; the
      -- MIRROR of the loop's bail: a suffix whose leading head segment carries
      -- content (a comment leadingSep? cannot place) keeps whole-decl verbatim
      for slot in margs.toList.drop 1 do
        if (bare_src slot).trimAscii.toString.isEmpty then continue
        let isWsL (line : String) : Bool := line.all (fun char => char == ' ' || char == '\t')
        if !isWsL ((((Lean4Fmt.Syntax.leading? slot).getD "").splitOn "\n").headD "") then
          return false
      let altsNode := (margs[0]?).getD .missing
      let mut alts : Array Lean.Syntax := #[]
      for group in altsNode.getArgs do
        for child in group.getArgs do
          if child.getKind == ``Lean.Parser.Term.matchAlt then alts := alts.push child
      if alts.isEmpty then
        return false
      -- the per-arm seam conditions, mirrored from the valForm loop: any bail
      -- there can only `.span`, and an eqns span under a reformatted signature
      -- re-anchors wrongly (there is no `:=` seam) — so anything the loop cannot
      -- hold must be decided HERE, where the fallback is whole-decl verbatim
      for h : idx in [0:alts.size] do
        let alt := alts[idx]
        if Lean4Fmt.Syntax.has_unowned_interior_comment alt then
          return false
        let lead := (Lean4Fmt.Syntax.leading? alt).getD ""
        let isWs (line : String) : Bool := line.all (fun char => char == ' ' || char == '\t')
        if !isWs ((lead.splitOn "\n").headD "") then
          return false
        let trailT := ((Lean4Fmt.Syntax.trailing? alt).getD "").trimAscii.toString
        if idx + 1 < alts.size && trailT.any (· == '\n') then
          return false
      return true

/-- The comment block (if any) inside a trivia string: the non-whitespace-only
    lines, dedented to column 0 (so a caller can re-anchor them with
    `.verbatim … 0`). `none` when the trivia is pure whitespace. Lets onePerLine
    preserve inter-binder comments instead of dropping them (which would otherwise
    force the gate's identity fallback). -/
private
def comment_block? (trivia : String) : Option String :=
  Id.run do
    let isWs (line : String) : Bool := line.all (fun char => char == ' ' || char == '\t')
    let mut lines := trivia.splitOn "\n"
    lines := lines.dropWhile isWs
    lines := (lines.reverse.dropWhile isWs).reverse
    if lines.isEmpty then
      return none
    let indentOf (line : String) : Nat := (line.toList.takeWhile (· == ' ')).length
    let base :=
      (lines.filter (fun line => !isWs line)).foldl
        (fun minimum line => Nat.min minimum (indentOf line))
        1000000
    let base := if base == 1000000 then 0 else base
    let dedented :=
      lines.map
        (fun line => if line.length ≥ base then String.ofList (line.toList.drop base) else line)
    return some (String.intercalate "\n" dedented)

/-- Signature return-type info: `none` if there is no type spec, else
    `(termDoc, colonTypeDoc, flatWidth, multiline?)` where `termDoc` is the type
    term alone (no colon) — WALKED, so arrow chains and applications lay out
    actively and width-aware — and `colonTypeDoc` is the whole `: τ` byte-exact
    (with the colon). Callers use `termDoc` (adding their own `: `) when it is
    clean, and `colonTypeDoc` when the term carries a comment or a multi-line
    opaque block (so the colon and the bytes are never lost). -/
private
def type_info
    (walk : Lean4Fmt.Emit.Walk)
    (sig : Lean.Syntax)
    : emit_m (Option (Doc × Doc × Nat × Bool)) := do
  let args := sig.getArgs
  let tsNode : Option Lean.Syntax :=
    args[1]?.bind
      (
        fun candidate =>
          if candidate.getKind == ``Lean.Parser.Term.typeSpec then
            some candidate
          else
            candidate.getArgs[0]?
      )
  match tsNode with
  | some tokens =>
    if tokens.getKind == ``Lean.Parser.Term.typeSpec
        && !Lean4Fmt.Syntax.subtree_has_line_comment tokens then
      let term ← walk (tokens.getArgs[1]?.getD .missing)
      let colonType ← verbatim_quiet tokens   -- probe: logged only if the span is TAKEN
      -- wide types are ACTIVE now: commaGroups carry fillSep pools (§5), so a
      -- byte table reflows as a packed fill instead of exploding one-per-line
      if Lean4Fmt.Doc.hasMultilineVerbatim term then
        log_opt_out tokens
        return some (colonType, colonType, (Lean4Fmt.Doc.flat_width colonType).getD 0, true)
      return some (term, colonType, (Lean4Fmt.Doc.flat_width term).getD 0, false)
    else
      let ct ← verbatim tokens
      return some (ct, ct, (Lean4Fmt.Doc.flat_width ct).getD 0, true)  -- comment/unexpected: whole span
  | none => return none

private
abbrev type_info_data := Option (Doc × Doc × Nat × Bool)

private
def adaptive_binder_mode
    (binders : Array Lean.Syntax)
    (typeInfo : type_info_data)
    (prefixWidth reserve : Nat)
    : emit_m Lean4Fmt.Style.binder_layout := do
  let preserve := (← read).spacing.preserveBinders
  let lineWidth := (← read).layout.lineWidth
  let mut state : sig_state := {}
  for binder in binders do
    match Lean4Fmt.Emit.binder_text? binder preserve with
    | some text => state := { state with bindersWidth := state.bindersWidth + 1 + text.length }
    | none => state := { state with simple := false }
  let typeContrib :=
    match typeInfo with
    | some (term, _, _, false) =>
      match Lean4Fmt.Doc.flat_width term with
      | some typeWidth => 3 + typeWidth
      | none           => lineWidth + 1
    | some (_, _, _, true) => lineWidth + 1
    | none => 0
  let solveDefs := (← read).breaking.solveDefs
  if solveDefs && state.simple
      && Lean4Fmt.Solve.sig_one_line_fits lineWidth prefixWidth
        (state.bindersWidth + typeContrib + reserve) then
    return .oneLine
  return .onePerLine

private
def sig_doc_one_per_line
    (walk : Lean4Fmt.Emit.Walk)
    (nameCol : Nat)
    (binders : Array Lean.Syntax)
    (typeInfo : type_info_data)
    : emit_m Doc := do
  let mut state : sig_state := {}
  for binder in binders do
    match comment_block? ((Lean4Fmt.Syntax.leading? binder).getD "") with
    | some comment => state := { state with doc := state.doc ++ .hardline ++ .verbatim comment 0 }
    | none => pure ()
    state :=
      { state with doc := state.doc ++ .hardline ++ (← Lean4Fmt.Emit.binder_doc walk binder) }
  match typeInfo with
  | some (term, colonType, _, multi) =>
    if multi then state := { state with doc := state.doc ++ .hardline ++ colonType }
    else state := { state with doc := state.doc ++ .hardline ++ .text ": " ++ term }
  | none => pure ()
  return .nest nameCol state.doc

private
structure sig_fill_context where
  continuationIndent : Nat
  reserve            : Nat
  breakAfter         : Bool

private
def sig_fill_type
    (state : sig_state)
    (ctx : sig_fill_context)
    (multi : Bool)
    (term colonType : Doc)
    : Doc :=
  if multi then
    .nest ctx.continuationIndent (state.doc ++ .hardline ++ colonType)
  else if ctx.breakAfter then
    .nest
      ctx.continuationIndent
      (state.doc ++ .text " :" ++ .group (.line ++ term ++ .pad ctx.reserve))
  else
    .nest
      ctx.continuationIndent
      (state.doc ++ .group (.line ++ .text ": " ++ term ++ .pad ctx.reserve))

private
def sig_doc_fill
    (walk : Lean4Fmt.Emit.Walk)
    (reserve : Nat)
    (binders : Array Lean.Syntax)
    (typeInfo : type_info_data)
    : emit_m Doc := do
  let mut state : sig_state := {}
  for binder in binders do
    state :=
      { state with binderDocs := state.binderDocs.push (← Lean4Fmt.Emit.binder_doc walk binder) }
  let breakAfter := (← read).breaking.colon == .breakAfter
  let hasType :=
    match typeInfo with
    | some (_, _, _, false) => true
    | _ => false
  for h : idx in [0:state.binderDocs.size] do
    let binderDoc := state.binderDocs[idx]!
    let tailPad :=
      if idx + 1 < state.binderDocs.size then
        0
      else if hasType then if breakAfter then 2 else 0 else reserve
    state :=
      { state with
        doc := state.doc
            ++ (
              if idx == 0 then .space ++ binderDoc else .group (.line ++ binderDoc ++ .pad tailPad)
            ) }
  let continuationIndent := (← read).layout.continuationIndent
  let ctx : sig_fill_context := { continuationIndent, reserve, breakAfter }
  match typeInfo with
  | some (term, colonType, _, multi) => return sig_fill_type state ctx multi term colonType
  | none => return .nest continuationIndent state.doc

private
structure sig_one_line_context where
  prefixWidth        : Nat
  reserve            : Nat
  lineWidth          : Nat
  continuationIndent : Nat

private
def sig_one_line_type
    (state : sig_state)
    (ctx : sig_one_line_context)
    (typeWidth : Nat)
    (multi : Bool)
    (term colonType : Doc)
    : Doc :=
  if multi then
    state.doc ++ .space ++ colonType
  else if ctx.prefixWidth + state.flatWidth + 3 + typeWidth + ctx.reserve ≤ ctx.lineWidth then
    state.doc ++ .text " : " ++ term
  else
    state.doc ++ .text " :" ++ .nest ctx.continuationIndent (.hardline ++ term)

private
def sig_doc_one_line
    (walk : Lean4Fmt.Emit.Walk)
    (prefixWidth reserve : Nat)
    (binders : Array Lean.Syntax)
    (typeInfo : type_info_data)
    : emit_m Doc := do
  let mut state : sig_state := {}
  for binder in binders do
    let binderDoc ← Lean4Fmt.Emit.binder_doc walk binder
    state := { state with
      doc := state.doc ++ .space ++ binderDoc
      flatWidth := state.flatWidth + 1 + (Lean4Fmt.Doc.flat_width binderDoc).getD 0
    }
  let lineWidth := (← read).layout.lineWidth
  let continuationIndent := (← read).layout.continuationIndent
  let ctx : sig_one_line_context := { prefixWidth, reserve, lineWidth, continuationIndent }
  match typeInfo with
  | some (term, colonType, typeWidth, multi) =>
    return sig_one_line_type state ctx typeWidth multi term colonType
  | none => return state.doc

/-- Reflow an `optDeclSig`/`declSig` = [binders, typeSpec?] under the binder-layout
    knob (Style.breaking.binders):

    • `oneLine` — binders space-joined on the keyword line; the return type stays
      inline, or breaks AFTER the colon to a continuationIndent line when
      `prefixWidth + " : " + typeWidth + reserve` overflows (`reserve` = what the
      value adds to that line, e.g. `:= by`). The dense default.
    • `fill` — binders packed on the line and wrapped to continuation lines as the
      width fills (mathlib-ish); the type trails as a final fill element.
    • `onePerLine` — each binder on its own line, and the return type on its own
      line (colon leads it — breakBefore), all aligned under the declaration NAME
      (column `nameCol`). The straylight house style.

    A multi-line (verbatim) type is never itself broken (re-anchoring a multi-line
    opaque block in a nest could drift); it is reproduced byte-exact with its
    colon. -/
private
def sig_doc
    (walk : Lean4Fmt.Emit.Walk)
    (nameCol prefixWidth reserve : Nat)
    (sig : Lean.Syntax)
    : emit_m Doc := do
  let args := sig.getArgs
  let binders := (args[0]?.map (·.getArgs)).getD #[]
  let typeInfo ← type_info walk sig
  -- A comment in a binder's leading trivia owns the seam before that binder.
  -- Only the per-line layout materializes those seams; fill/oneLine would
  -- flatten the binders and silently discard the comments.
  let hasBinderComment :=
    binders.any fun binder =>
      Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? binder).getD "") > 0
  -- resolve `adaptive` per-declaration through the solver: the sig rides ONE
  -- line while its binders fit the keyword line, else the per-line stack
  -- (Solve.sigOneLineFits). A multi-line binder never rides one line. Other
  -- modes pass through unchanged, so onePerLine/oneLine/fill are byte-identical.
  let mode ← if hasBinderComment then pure Lean4Fmt.Style.binder_layout.onePerLine
  else if (← read).breaking.binders == .adaptive then
    do adaptive_binder_mode binders typeInfo prefixWidth reserve
  else pure (← read).breaking.binders
  match mode with
  | .onePerLine | .adaptive => sig_doc_one_per_line walk nameCol binders typeInfo
  | .fill => sig_doc_fill walk reserve binders typeInfo
  | .oneLine => sig_doc_one_line walk prefixWidth reserve binders typeInfo

/-- Value kinds we actively lay out even when they span multiple lines (their own
    `walk` produces a width-aware breaking `group`). Everything else keeps the
    conservative verbatim-span path. THE SET IS DATA in
    `Syntax.Kinds.activeMultilineTermKinds` — one registry shared with the walk
    router, subset relation by construction. -/
private
def is_active_multiline (kind : SyntaxNodeKind) : Bool :=
  Lean4Fmt.Syntax.active_multiline_term_kinds.contains kind || Lean4Fmt.Syntax.is_bin_op kind

/-- How a definition value is to be placed. `span` is a whole `:= …` reproduced
    verbatim (where/termination/multi-line-opaque cases — the `:=` is inside it).
    `body` is the value BODY alone (no `:=`), which the caller joins to `:=`;
    `glue` means keep it on the `:=` line (a `do` block, compactDo). `eqns` is an
    equation-style value (`| pat => body` arms, no `:=`) already laid out one arm
    per line; the caller places it under the signature at indent 2. -/
private
inductive val_form
  | span (doc : Doc)
  | body (doc : Doc) (glue : Bool)
  | eqns (arms : Doc)

/-- `bodyOwnLine` for GLUED bodies (`:= do` / `:= by`): the blank goes after
    the keyword, before the block. The block's own leading separator collapses
    into the blank (renderer pend accumulation), so exactly one blank line
    appears — the same rhythm term bodies get after `:=`. -/
private
def glue_body_blank (document : Doc) : Doc :=

  -- the body blank is DO/BY rhythm — a glued record literal (unconditional
  -- `{` left edge, the vertical structInst) keeps its close brace tight
  if ((Lean4Fmt.Doc.left_edge_text? document).map (·.startsWith "{")).getD false then document
  else
    match document with
    -- width-aware single-tactic body (`by rfl` shape): the group's leading
    -- `.line` must be REPLACED by the blank, not preceded by it — a flat-decided
    -- group after a pending blank renders the line's space after the indent
    -- flush (a spurious column; caught as an idempotence failure)
    | .cat keyword (.group (.nest count (.cat .line rest))) => .cat keyword (.nest count (.cat (.blank 1) rest))
    | .cat keyword rest => .cat keyword (.cat (.blank 1) rest)
    | document => document

/-- `bodyOwnLine` for VERBATIM value spans: when the span's first line is
    exactly `:=` / `:= by` / `:= do`, split that keyword line off the opaque
    block and put the body blank between — the body itself stays byte-exact
    (base 0: top-level lines keep their absolute indent). Without this, a decl
    whose body carries unported constructs would silently lose the rhythm the
    active path imposes ("blank when the tactics are simple, none when they
    aren't"). Idempotent: the injected blank is a leading blank line of the
    block on the next pass, and wrBlock drops those. -/
private
def span_body_blank_lines
    (bodyOwnLine : Bool)
    (declVal : Lean.Syntax)
    (original : Doc)
    (first : String)
    (rest : List String)
    : val_form :=
  Id.run do
    let firstText := first.trimAsciiEnd.toString
    if (firstText == ":=" || firstText == ":= by" || firstText == ":= do") && !rest.isEmpty then
      let body := String.intercalate "\n" rest
      let skip := first.utf8ByteSize + 1
      if bodyOwnLine then
        return .span
          (
            .text firstText ++ .blank 1
                ++ .verbatim (Lean4Fmt.Emit.canon_ws_piecewise declVal body skip) 0
          )
      if ((rest.head?.getD "x").trimAscii.toString.isEmpty) then
        return .span
          (
            .text firstText ++ .hardline
                ++ .verbatim (Lean4Fmt.Emit.canon_ws_piecewise declVal body skip) 0
          )
    return .span original

private
def span_body_blank (bodyOwnLine : Bool) (declVal : Lean.Syntax) : val_form → val_form
  | .span document =>
    match (bare_src declVal).splitOn "\n" with
    | first :: rest => span_body_blank_lines bodyOwnLine declVal document first rest
    | _             => .span document
  | valueForm => valueForm

private
structure simple_value_context where
  declVal : Lean.Syntax
  args    : Array Lean.Syntax
  value   : Lean.Syntax

private
def finish_value_doc (ctx : simple_value_context) (valueDoc : Doc) : emit_m val_form := do
  if Lean4Fmt.Doc.has_midline_reanchor valueDoc then
    return .span (← verbatim ctx.declVal "val-multiline")
  return .body valueDoc false

private
def simple_value_with_suffix
    (walk : Lean4Fmt.Emit.Walk)
    (ctx : simple_value_context)
    : emit_m val_form := do
  let valueDoc ← walk ctx.value
  let mut tail : Doc := .nil
  for slot in [ctx.args[2]?, ctx.args[3]?] do
    let some suffix := slot | continue
    if (bare_src suffix).trimAscii.toString.isEmpty then continue
    let some separator := Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? suffix).getD "")
        | return .span (← verbatim ctx.declVal "val-suffix-lead")
    let suffixDoc ← if reanchors_multiline_token (bare_src suffix) then
      pure (.textRaw (bare_src suffix))
    else verbatim suffix
    tail := tail ++ separator ++ suffixDoc
  let glue :=
    ctx.value.getKind == ``Lean.Parser.Term.do || ctx.value.getKind == ``Lean.Parser.Term.byTactic
        || ((← read).breaking.glueFun && ctx.value.getKind == ``Lean.Parser.Term.fun)
  return .body (valueDoc ++ tail) glue

private
def simple_value_body
    (walk : Lean4Fmt.Emit.Walk)
    (ctx : simple_value_context)
    : emit_m val_form := do
  let valueDoc ← walk ctx.value
  if ctx.value.getKind == ``Lean.Parser.Term.do
      || ctx.value.getKind == ``Lean.Parser.Term.byTactic then
    return .body valueDoc true
  if (← read).breaking.glueFun && ctx.value.getKind == ``Lean.Parser.Term.fun
      && !Lean4Fmt.Doc.hasMultilineVerbatim valueDoc then
    return .body valueDoc true
  let trailingComments :=
    Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.trailing? ctx.value).getD "")
  let leadingComments :=
    Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? ctx.value).getD "")
  let ownsLeading :=
    ctx.value.getKind == ``Lean.Parser.Term.let || ctx.value.getKind == ``Lean.Parser.Term.have
        || ctx.value.getKind == ``Lean.Parser.Term.letI
        || ctx.value.getKind == ``Lean.Parser.Term.haveI
        || ctx.value.getKind == ``Lean.Parser.Term.letrec
  let separator? := Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? ctx.value).getD "")
  let valueDoc :=
    if leadingComments > 0 && !ownsLeading then
      separator?.map (· ++ valueDoc) |>.getD valueDoc
    else
      valueDoc
  if leadingComments > 0 && !ownsLeading && separator?.isNone then
    return .span (← verbatim ctx.declVal "val-lead-unplaceable")
  let clean := !Lean4Fmt.Doc.hasMultilineVerbatim valueDoc
  if ((Lean4Fmt.Doc.left_edge_text? valueDoc).map (·.startsWith "{")).getD false && clean then
    return .body valueDoc true
  if (is_active_multiline ctx.value.getKind || leadingComments > 0) && clean then
    return .body valueDoc false
  if Lean4Fmt.Doc.flat_width valueDoc |>.isSome then
    return .body valueDoc false
  -- The declaration owns the line-start seam after `:=`: an opaque multiline
  -- value composes safely there. Reject only the actual hazard, a child that
  -- re-anchors after non-whitespace on an assembled line.
  finish_value_doc ctx valueDoc

private
def value_span (declVal : Lean.Syntax) (reason : String) : emit_m val_form :=
  .span <$> verbatim declVal reason

private
def equation_arm_fallback (declVal : Lean.Syntax) : emit_m val_form := do
  match Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? declVal).getD "") with
  | some separator => return .eqns (separator ++ (← verbatim declVal "eqns-arm"))
  | none => value_span declVal "eqns-arm"

private
def opaque_equation_arms
    (declVal : Lean.Syntax)
    (alternatives : Array Lean.Syntax)
    (suffixTail : Doc)
    : emit_m val_form := do
  let mut arms : Doc := .nil
  for alternative in alternatives do
    let some separator :=
      Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? alternative).getD "")
        | return ← equation_arm_fallback declVal
    arms := arms ++ separator ++ (← verbatim alternative "equation-arm-piece")
  return .eqns (arms ++ suffixTail)

private
def owned_equation_suffix_separator
    (_suffix : Lean.Syntax)
    (separator : Doc)
    : Except String (Option Doc) :=
  .ok (some separator)

private
def equation_suffix_separator (suffix : Lean.Syntax) : Except String (Option Doc) :=
  if (bare_src suffix).trimAscii.toString.isEmpty then
    .ok none
  else
    match Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? suffix).getD "") with
    | none           => .error "eqns-suffix-lead"
    | some separator => owned_equation_suffix_separator suffix separator

private
def equation_suffix_doc (suffix : Lean.Syntax) : emit_m (Except String Doc) :=
  match equation_suffix_separator suffix with
  | .error reason        => pure (.error reason)
  | .ok none             => pure (.ok .nil)
  | .ok (some separator) => (fun doc : Doc => Except.ok (separator ++ doc)) <$> verbatim suffix

private
def equation_value (walk : Lean4Fmt.Emit.Walk) (declVal : Lean.Syntax) : emit_m val_form := do
  let matchWithDecls := (declVal.getArgs[0]?).getD .missing
  let matchArgs := matchWithDecls.getArgs
  let suffixDocs ← (matchArgs.toList.drop 1).mapM equation_suffix_doc
  let failure? := suffixDocs.findSome? fun | .error reason => some reason | .ok _ => none
  if failure?.isSome then
    return ← value_span declVal (failure?.getD "eqns-suffix-lead")
  let suffixTail := suffixDocs.foldl (fun docs result => docs ++ result.toOption.getD .nil) .nil
  let alternatives := Lean4Fmt.Emit.match_alts_of ((matchArgs[0]?).getD .missing)
  if alternatives.isEmpty then
    return ← value_span declVal "eqns-empty"
  let pieces? ← Lean4Fmt.Emit.arm_pieces? walk alternatives Lean4Fmt.Emit.token_join_flat?
  let alignment := (← read).alignment
  if pieces?.isNone then
    return ← opaque_equation_arms declVal alternatives suffixTail
  let pieces := pieces?.getD #[]
  return .eqns
    (Lean4Fmt.Emit.arms_aligned_runs alignment.matchArms alignment.maxDelta pieces ++ suffixTail)

/-- Classify a `declVal` into a `ValForm` (see above). Splitting the `:=` from the
    body lets the caller choose the separator: inline ` := `, or (bodyOwnLine)
    `:=` then a blank then the body on its own indented line. -/
private
def valForm (walk : Lean4Fmt.Emit.Walk) (declVal : Lean.Syntax) : emit_m val_form := do
  if declVal.getKind == ``Lean.Parser.Command.declValSimple then
    let args := declVal.getArgs
    -- a same-line comment after `:=` lives in the ASSIGN ATOM's trailing
    -- (Lean trivia: same-line comments attach to the preceding token) — no
    -- layout here has a seam for it, and the value's leading never sees it
    -- (gate-caught on aleph EDSL.lean: `Claim :=   -- needs hardware`,
    -- comments class). The slot-tail-trailing rule, applied to `:=` itself.
    if !(((args[0]?.bind Lean4Fmt.Syntax.trailing?).getD "").trimAscii.toString.isEmpty) then
      return .span (← verbatim declVal "assign-trailing-comment")
    let hasSuffix :=
      (args[2]?.map (fun suffix => !(bare_src suffix).trimAscii.toString.isEmpty)).getD false
    let hasWhere := (args[3]?.map (fun whereBody => !whereBody.getArgs.isEmpty)).getD false
    let some value := args[1]? | return .span (← verbatim declVal "val-shape")
    let context : simple_value_context := { declVal, args, value }
    if hasSuffix || hasWhere then simple_value_with_suffix walk context
    else simple_value_body walk context
  else if declVal.getKind == ``Lean.Parser.Command.declValEqns then equation_value walk declVal
  else
    return .span (← verbatim declVal "where-struct") -- where-struct: literal span

/-- Flat width the value contributes to the `:= …` line (`none` if it can't be one
    line). span includes `:=` (+1 for the leading space); body adds ` := ` (4). -/
private
def val_form.flat_width : val_form → Option Nat
  | .span document   => (Lean4Fmt.Doc.flat_width document).map (· + 1)
  | .body document _ => (Lean4Fmt.Doc.flat_width document).map (· + 4)
  | .eqns _          => none

private
structure broken_value_context where
  eqGapL       : String
  glueOverflow : Bool
  bodyOwnLine  : Bool
  alwaysBreak  : Bool
  preserveLB   : Bool
  total        : Nat
  fitWidth     : Nat

private
def broken_value_doc (ctx : broken_value_context) (verticalFits : val_form) : Doc :=
  match verticalFits with
  | .span doc => .text ctx.eqGapL ++ doc
  | .body doc glue =>
    if glue && ctx.glueOverflow then
      .text (ctx.eqGapL ++ ":=") ++ .nest 2 (.hardline ++ doc)
    else if glue then
      .text (ctx.eqGapL ++ ":= ") ++ (if ctx.bodyOwnLine then glue_body_blank doc else doc)
    else if ctx.bodyOwnLine then
      .text (ctx.eqGapL ++ ":=") ++ .nest 2 (.blank 1 ++ doc)
    else if ctx.alwaysBreak || ctx.preserveLB then
      .text (ctx.eqGapL ++ ":=") ++ .nest 2 (.hardline ++ doc)
    else if verticalFits.flat_width.isSome && ctx.total > ctx.fitWidth then
      .text (ctx.eqGapL ++ ":=") ++ .nest 2 (.hardline ++ doc)
    else
      .text (ctx.eqGapL ++ ":=") ++ .group (.nest 2 (.line ++ doc))
  | .eqns _ => .nil

private
def signature_from_syntax
    (walk : Lean4Fmt.Emit.Walk)
    (sigStx : Option Lean.Syntax)
    (nameCol prefixWidth reserve : Nat)
    : emit_m Doc :=
  match sigStx with
  | some signature => sig_doc walk nameCol prefixWidth reserve signature
  | none           => pure .nil

private
def broken_signature_doc
    (walk : Lean4Fmt.Emit.Walk)
    (sigExact? : Option String)
    (sigStx : Option Lean.Syntax)
    (sigInline : Doc)
    (preserveLB : Bool)
    (nameCol prefixWidth sigWidth typeWidth reserve lineWidth : Nat)
    : emit_m Doc :=
  match sigExact? with
  | some _ =>
    if preserveLB || prefixWidth + sigWidth + typeWidth + reserve ≤ lineWidth then
      pure sigInline
    else
      signature_from_syntax walk sigStx nameCol prefixWidth reserve
  | none => signature_from_syntax walk sigStx nameCol prefixWidth reserve

private
structure defn_layout_context where
  defnSyntax  : Lean.Syntax
  args        : Array Lean.Syntax
  keyword     : String
  identifier  : String
  valueForm   : val_form
  nameCol     : Nat
  prefixWidth : Nat
  lineWidth   : Nat
  signature?  : Option Lean.Syntax
  exactSig?   : Option String
  inlineSig   : Doc
  sigWidth    : Nat
  typeWidth   : Nat
  typeClean   : Bool
  typeInfo    : Option (Doc × Doc × Nat × Bool)
  preserveLB  : Bool

private
def equation_defn_doc
    (walk : Lean4Fmt.Emit.Walk)
    (ctx : defn_layout_context)
    (arms : Doc)
    : emit_m Doc := do
  let signature ← if ctx.typeClean && ctx.prefixWidth + ctx.sigWidth + ctx.typeWidth ≤ ctx.lineWidth then
    let typeInline : Doc :=
      if ctx.exactSig?.isSome then
        .nil
      else
        match ctx.typeInfo with
        | some (term, _, _, false) => .text " : " ++ term
        | _ => .nil
    pure (ctx.inlineSig ++ typeInline)
  else signature_from_syntax walk ctx.signature? ctx.nameCol ctx.prefixWidth 0
  return .text ctx.keyword ++ .space ++ .text ctx.identifier ++ signature ++ .nest 2 arms

private
def regular_inline_doc? (ctx : defn_layout_context) : emit_m (Option Doc) := do
  let flatValue := ctx.valueForm.flat_width
  let eqGap :=
    if ctx.preserveLB then
      let sourceGap :=
        (
          (ctx.signature?.bind Lean4Fmt.Syntax.last_token_trailing?).getD
            (((ctx.args[1]?.bind Lean4Fmt.Syntax.trailing?)).getD " ")
        )
      if sourceGap.toList.all (· == ' ') then sourceGap else " "
    else
      " "
  let total := ctx.prefixWidth + ctx.sigWidth + ctx.typeWidth + flatValue.getD 1000000
  let inlineValue : Doc :=
    match ctx.valueForm with
    | .span doc   => .text eqGap ++ .flatten doc
    | .body doc _ => .text (eqGap ++ ":= ") ++ .flatten doc
    | .eqns _     => .nil
  let style ← read
  let alwaysBreak := style.breaking.bodyAlwaysBreak
  let sourceBroken :=
    (
      (ctx.args[3]?.bind (·.getArgs[1]?)).map
        (fun value => ((Lean4Fmt.Syntax.leading? value).getD "").any (· == '\n'))
    ).getD
      false
  let fitWidth := Nat.min ctx.lineWidth style.layout.bodyFitWidth
  let fits :=
    if style.breaking.solveDefs then
      Lean4Fmt.Solve.inline_def_fits fitWidth total
    else
      total ≤ fitWidth
  let noComment := !Lean4Fmt.Syntax.interior_has_line_comment ctx.defnSyntax
  let inlineOk :=
    noComment && flatValue.isSome && ctx.typeClean && !alwaysBreak
        && (if ctx.preserveLB then !sourceBroken else fits)
  let typeInline : Doc :=
    if ctx.exactSig?.isSome then
      .nil
    else
      match ctx.typeInfo with
      | some (term, _, _, false) => .text " : " ++ term
      | _ => .nil
  if inlineOk then
    return some
      (
        .text ctx.keyword ++ .space ++ .text ctx.identifier ++ ctx.inlineSig ++ typeInline
            ++ inlineValue
      )
  return none

private
def regular_defn_doc (walk : Lean4Fmt.Emit.Walk) (ctx : defn_layout_context) : emit_m Doc := do
  if let some inlineDoc ← regular_inline_doc? ctx then
    return inlineDoc
  let flatValue := ctx.valueForm.flat_width
  let eqGap :=
    if ctx.preserveLB then
      let sourceGap :=
        (
          (ctx.signature?.bind Lean4Fmt.Syntax.last_token_trailing?).getD
            (((ctx.args[1]?.bind Lean4Fmt.Syntax.trailing?)).getD " ")
        )
      if sourceGap.toList.all (· == ' ') then sourceGap else " "
    else
      " "
  let total := ctx.prefixWidth + ctx.sigWidth + ctx.typeWidth + flatValue.getD 1000000
  let style ← read
  let alwaysBreak := style.breaking.bodyAlwaysBreak
  let fitWidth := Nat.min ctx.lineWidth style.layout.bodyFitWidth
  let valueIsFun :=
    ((ctx.args[3]?.bind (·.getArgs[1]?)).map (·.getKind)) == some ``Lean.Parser.Term.fun
  let glueOverflow :=
    valueIsFun
        && (
          match ctx.valueForm with
          | .body doc true =>
            ctx.prefixWidth + ctx.sigWidth + ctx.typeWidth
                + (Lean4Fmt.Doc.first_line_width (.text (eqGap ++ ":= ") ++ doc)).1
                > ctx.lineWidth
                && ctx.prefixWidth + ctx.sigWidth + ctx.typeWidth + 3 ≤ ctx.lineWidth
          | _ => false
        )
  let valueDoc :=
    broken_value_doc
      { eqGapL := eqGap,
        glueOverflow,
        bodyOwnLine := style.breaking.bodyOwnLine,
        alwaysBreak,
        preserveLB := ctx.preserveLB,
        total,
        fitWidth }
      ctx.valueForm
  let reserve := (Lean4Fmt.Doc.first_line_width valueDoc).1
  let signature ←
    broken_signature_doc
      walk
      ctx.exactSig?
      ctx.signature?
      ctx.inlineSig
      ctx.preserveLB
      ctx.nameCol
      ctx.prefixWidth
      ctx.sigWidth
      ctx.typeWidth
      reserve
      ctx.lineWidth
  return .text ctx.keyword ++ .space ++ .text ctx.identifier ++ signature ++ valueDoc

private
structure defn_head_context where
  defnSyntax  : Lean.Syntax
  args        : Array Lean.Syntax
  keyword     : String
  identifier  : String
  valueForm   : val_form
  nameCol     : Nat
  prefixWidth : Nat
  lineWidth   : Nat
  signature?  : Option Lean.Syntax

private
def exact_signature? (preserve : Bool) (signature? : Option Lean.Syntax) : Option String :=
  if !preserve then
    none
  else
    match signature? with
    | none => some ""
    | some signature =>
      let source := (bare_src signature).trimAscii.toString
      if source.isEmpty then
        some ""
      else if source.any (· == '\n') then
        none
      else if Lean4Fmt.Syntax.count_subtree_line_comments signature > 0 then none else some source

private
def finish_defn_doc (walk : Lean4Fmt.Emit.Walk) (head : defn_head_context) : emit_m Doc := do
  let binders := ((head.signature?.bind (·.getArgs[0]?)).map (·.getArgs)).getD #[]
  let mut inlineBinders : Doc := .nil
  let mut bindersWidth := 0
  for binder in binders do
    let binderDoc ← Lean4Fmt.Emit.binder_doc walk binder
    inlineBinders := inlineBinders ++ .space ++ binderDoc
    bindersWidth := bindersWidth + 1 + (Lean4Fmt.Doc.flat_width binderDoc).getD 0
  let typeInfo ← match head.signature? with
  | some signature => type_info walk signature
  | none => pure none
  let typeClean := typeInfo.all (fun info => !info.2.2.2)
  let typeWidth :=
    match typeInfo with
    | some (_, _, width, false) => 3 + width
    | _ => 0
  let style ← read
  let exactSig? := exact_signature? style.spacing.preserveBinders head.signature?
  if style.spacing.preserveBinders && exactSig?.isNone then
    return (← verbatim head.defnSyntax "preserve-sig-inexact")
  let signatureGap :=
    if ((head.args[1]?.bind Lean4Fmt.Syntax.trailing?).getD " ").isEmpty then "" else " "
  let (inlineSig, sigWidth, typeWidth, typeClean) :=
    match exactSig? with
    | some source =>
      if source.isEmpty then
        ((.nil : Doc), 0, 0, true)
      else
        ((.text (signatureGap ++ source) : Doc), signatureGap.length + source.length, 0, true)
    | none => (inlineBinders, bindersWidth, typeWidth, typeClean)
  let context : defn_layout_context :=
    { defnSyntax := head.defnSyntax,
      args := head.args,
      keyword := head.keyword,
      identifier := head.identifier,
      valueForm := head.valueForm,
      nameCol := head.nameCol,
      prefixWidth := head.prefixWidth,
      lineWidth := head.lineWidth,
      signature? := head.signature?,
      exactSig?,
      inlineSig,
      sigWidth,
      typeWidth,
      typeClean,
      typeInfo,
      preserveLB := style.breaking.preserveLineBreaks }
  match head.valueForm with
  | .eqns arms => equation_defn_doc walk context arms
  | _ => regular_defn_doc walk context

/-- Format the inner definition node `[kw, declId, sig, declVal, …]`. `modsWidth`
    is the inline width the modifiers add to the keyword's line.

    One-liner exemption (chosen policy): if the WHOLE declaration
    `[vis] kw name binders : type := value` fits on one line — the value is single
    line, the type is single line, and there is no line comment — it is emitted
    inline regardless of the binder-layout knob (so a short def does not explode
    into onePerLine). Otherwise the signature breaks per the knob and the value is
    laid out by `valDoc`. (Any doc-comment/attribute lines sit above and do not
    count toward the one-line budget.) -/
private
def defn_doc (walk : Lean4Fmt.Emit.Walk) (modsWidth : Nat) (defn : Lean.Syntax) : emit_m Doc := do
  let args := defn.getArgs
  -- Standalone suffix slots such as `deriving` own a line-start seam after
  -- the value and compose independently with the formatted definition.
  let mut suffixTail : Doc := .nil
  for h : idx in [4:args.size] do
    let suffix := args[idx]
    let suffixText := Lean4Fmt.Emit.canon_tok suffix
    if suffixText.isEmpty then continue
    let some separator := Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? suffix).getD "")
        | return (← verbatim defn "definition-suffix-seam")
    let suffixDoc ← if suffixText.any (· == '\n') then verbatim suffix "definition-suffix-piece"
    else pure (.text suffixText)
    suffixTail := suffixTail ++ separator ++ suffixDoc
  let keyword :=
    match args[0]? with
    | some (Lean.Syntax.atom _ value) => value
    | _ => "def"
  let declId := (args[1]?.map bare_src).getD ""
  let valueForm ← match args[3]? with
  | some value => valForm walk value
  | none => pure (.body .nil false)
  let bodyOwn := (← read).breaking.bodyOwnLine
  let valueForm :=
    match args[3]? with
    | some value => span_body_blank bodyOwn value valueForm
    | none       => valueForm
  let nameCol := modsWidth + keyword.length + 1
  let document ←
    finish_defn_doc
      walk
      { defnSyntax := defn,
        args,
        keyword,
        identifier := declId,
        valueForm,
        nameCol,
        prefixWidth := nameCol + declId.length,
        lineWidth := (← read).layout.lineWidth,
        signature? := args[2]? }
  return document ++ suffixTail

private
def where_field_value_doc
    (walk : Lean4Fmt.Emit.Walk)
    (head : String)
    (value : Lean.Syntax)
    : emit_m (Option Doc) := do
  let valueLeading := (Lean4Fmt.Syntax.leading? value).getD ""
  let leadingComments := Lean4Fmt.Syntax.count_line_comments valueLeading
  let valueDoc ← if ((bare_src value).splitOn "private").length > 1 then
    verbatim value "where-private-value"
  else walk value
  if leadingComments > 0 then
    let some separator := Lean4Fmt.Emit.leading_sep? valueLeading | return none
    return some (.text head ++ .text " :=" ++ .nest 2 (separator ++ valueDoc))
  if value.getKind == ``Lean.Parser.Term.do || value.getKind == ``Lean.Parser.Term.byTactic then
    match valueDoc with
    | .verbatim _ _ => return some (.text head ++ .text " :=" ++ .nest 2 (.hardline ++ valueDoc))
    | _ => return some (.text (head ++ " := ") ++ valueDoc)
  if Lean4Fmt.Doc.hasMultilineVerbatim valueDoc then
    return some (.text head ++ .text " :=" ++ .nest 2 (.hardline ++ valueDoc))
  if (← read).breaking.glueFun && value.getKind == ``Lean.Parser.Term.fun then
    return some (.text (head ++ " := ") ++ valueDoc)
  return some (.text head ++ .text " :=" ++ .group (.nest 2 (.line ++ valueDoc)))

/-- One `where`-instance field `name (binders)* := value` — the lval and
    binders token-for-token, the VALUE walked (flat on the `:=` line when it
    fits, else next line at +2; `do`/`by` glue). `none` on a multi-line head
    piece, a value carrying a multi-line opaque block, or a structural
    surprise. -/
private
def parse_where_field_state?
    (head : String)
    (children : Array Lean.Syntax)
    : Option where_field_state :=
  Id.run do
    let mut state : where_field_state := { head }
    for child in children do
      if child.getKind == ``Lean.Parser.Term.structInstFieldDef then
        state := { state with defn? := some child }
      else if child.getKind == ``Lean.Parser.Term.structInstFieldEqns then
        state := { state with eqns? := some child }
      else
        let text := Lean4Fmt.Emit.canon_tok child
        if text.any (· == '\n') then
          return none
        if !text.isEmpty then state := { state with head := state.head ++ " " ++ text }
    return some state

private
def where_field_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (transform : Lean.Syntax)
    : emit_m (Option Doc) := do
  if ((bare_src transform).splitOn "private").length > 1 then
    let some text := Lean4Fmt.Emit.token_join_flat? transform | return none
    return some (.text text)
  if transform.getKind != ``Lean.Parser.Term.structInstField then
    return none
  if (← read).breaking.preserveLineBreaks then
    let text := (bare_src transform).trimAscii.toString
    if !text.isEmpty && !text.any (· == '\n')
        && !Lean4Fmt.Syntax.interior_has_line_comment transform then
      return some (.text text)
  let fieldArgs := transform.getArgs
  if fieldArgs.size != 2 then
    return none
  let lvalT := Lean4Fmt.Emit.canon_tok fieldArgs[0]!
  if lvalT.isEmpty || lvalT.any (· == '\n') then
    return none
  let rest := fieldArgs[1]!.getArgs
  let some state := parse_where_field_state? lvalT rest | return none
  if let some element := state.eqns? then
    -- pattern-matching field (`le_sup_left | lift a, lift b => …` — no
    -- `:=`, the mathlib instance-shape dominator): the shared arm loop
    -- lays the alternatives one per line at +2 under the field head
    if state.defn?.isSome then
      return none
    if Lean4Fmt.Syntax.count_subtree_line_comments transform >
        Lean4Fmt.Syntax.count_line_comments
          ((Lean4Fmt.Syntax.last_token_trailing? transform).getD "") then
      return none
    -- structInstFieldEqns = [binders-null, matchAlts] — matchAltsOf wants
    -- the matchAlts CHILD (called on the eqns node it found nothing and the
    -- whole instance bailed as instance-shape: Booleanisation)
    let altsNode := (element.getArgs.find? (·.getKind == ``Lean.Parser.Term.matchAlts)).getD element
    let alts := Lean4Fmt.Emit.match_alts_of altsNode
    if alts.isEmpty then
      return none
    let some pieces ← Lean4Fmt.Emit.arm_pieces? walk alts Lean4Fmt.Emit.token_join_flat? | return none
    let alignment := (← read).alignment
    return some (.text state.head
      ++ .nest 2
        (Lean4Fmt.Emit.arms_aligned_runs alignment.matchArms alignment.maxDelta pieces))
  -- Shorthand field (`... where app`): the head is the complete field.
  let some fdef := state.defn? | return some (.text state.head)
  let defArgs := fdef.getArgs
  let some value := defArgs[defArgs.size - 1]? | return none
  where_field_value_doc walk state.head value

/-- `<head> := value` placement shared by instance/example heads: inline when
    it fits, else per the bodyOwnLine knob (glued do/by keep the keyword on the
    `:=` line, blank after it). -/
private
def head_val_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (head : String)
    (declVal : Lean.Syntax)
    : emit_m (Option Doc) := do
  let width := (← read).layout.lineWidth
  let bodyOwnLine := (← read).breaking.bodyOwnLine
  let alwaysBreak := (← read).breaking.bodyAlwaysBreak
  match span_body_blank bodyOwnLine declVal (← valForm walk declVal) with
  | .span document => return some (.text head ++ .space ++ document)
  | .body document glue =>
    match Lean4Fmt.Doc.flat_width document with
    | some flatWidth =>
      if head.length + 4 + flatWidth ≤ width && !alwaysBreak && !glue then
        return some (.text head ++ .text " := " ++ .flatten document)
      else if glue && head.length + 4 + flatWidth ≤ width && !alwaysBreak then
        return some (.text head ++ .text " := " ++ .flatten document)
      else if glue then
        return some
          (
            .text head ++ .text " := "
                ++ (if bodyOwnLine then glue_body_blank document else document)
          )
      else if bodyOwnLine then
        return some (.text head ++ .text " :=" ++ .nest 2 (.blank 1 ++ document))
      else if alwaysBreak then
        return some (.text head ++ .text " :=" ++ .nest 2 (.hardline ++ document))
      else
        return some (.text head ++ .text " :=" ++ .group (.nest 2 (.line ++ document)))
    | none =>
      if glue then
        return some
          (
            .text head ++ .text " := "
                ++ (if bodyOwnLine then glue_body_blank document else document)
          )
      else if bodyOwnLine then
        return some (.text head ++ .text " :=" ++ .nest 2 (.blank 1 ++ document))
      else if alwaysBreak then
        return some (.text head ++ .text " :=" ++ .nest 2 (.hardline ++ document))
      else
        return some (.text head ++ .text " :=" ++ .group (.nest 2 (.line ++ document)))
  | .eqns _ => return none

/-- The field block of a `whereStructInst` declVal: one field per line, the
    seam loop owning inter-field trivia. The caller prepends `<head> where`
    and nests. -/
private
def where_body_doc? (walk : Lean4Fmt.Emit.Walk) (declVal : Lean.Syntax) : emit_m (Option Doc) := do
  let whereArgs := declVal.getArgs
  if whereArgs.size != 3 then
    return none
  if !((whereArgs[2]?.map bare_src).getD "").trimAscii.toString.isEmpty then
    return none
  if !((Lean4Fmt.Syntax.trailing? whereArgs[0]!).getD "").trimAscii.toString.isEmpty then
    return none
  let fields := ((whereArgs[1]?.bind (·.getArgs[0]?)).map (·.getArgs)).getD #[]
  let mut body : Doc := .nil
  let mut afterSemicolon := false
  for h : idx in [0:fields.size] do
    let field := fields[idx]
    if (bare_src field).trimAscii.toString.isEmpty then continue -- separator slot
    if field.isAtom then
      if (bare_src field).trimAscii.toString != ";" then
        return none
      body := body ++ .text ";" ++ .hardline
      afterSemicolon := true
      continue
    -- field-interior comments: whereFieldDoc? owns the accounting now (the
    -- VALUE's leading is a placeable zone — mathlib's `-- Porting note:`
    -- idiom); anything it cannot place still bails there
    let trailT := ((Lean4Fmt.Syntax.trailing? field).getD "").trimAscii.toString
    let last := idx + 1 == fields.size
    if !last && trailT.any (· == '\n') then
      return none
    let trailDoc : Doc := if !last && !trailT.isEmpty then .text (" " ++ trailT) else .nil
    let sep ← if afterSemicolon then pure Doc.nil
    else
      let some separator := Lean4Fmt.Emit.leading_sep? ((Lean4Fmt.Syntax.leading? field).getD "")
          | return none
      pure separator
    let some document ← where_field_doc? walk field | return none
    body := body ++ sep ++ document ++ trailDoc
    afterSemicolon := false
  -- n == 0 is the EMPTY where (`instance … : T where` — every field
  -- defaulted; the mathlib Prop-class idiom): a bare `where` tail, no body
  return some body

/-- `def name <sig> where <fields>` (the codegen Func-where pattern): head
    tokens single-line, fields via the where machinery. -/
private
def def_where_doc? (walk : Lean4Fmt.Emit.Walk) (defn : Lean.Syntax) : emit_m (Option Doc) := do
  let dargs := defn.getArgs
  if dargs.size < 4 then
    return none
  for h : idx in [0:3] do
    let child := dargs[idx]!
    -- first child's leading = the FORM's own leading — the enclosing seam
    -- owns it (see exampleDoc?); interior comments still bail
    let ownLead :=
      if idx == 0 then
        Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? child).getD "")
      else
        0
    if Lean4Fmt.Syntax.count_subtree_line_comments child > ownLead then
      return none
  let some body ← where_body_doc? walk dargs[3]! | return none
  let kwT := Lean4Fmt.Emit.canon_tok dargs[0]!
  let idT := Lean4Fmt.Emit.canon_tok dargs[1]!
  if kwT.isEmpty || kwT.any (· == '\n') || idT.any (· == '\n') then return none
  let hd0 := kwT ++ (if idT.isEmpty then "" else " " ++ idT)
  -- the inline-vs-broken decision must be ORIGIN-INDEPENDENT: flatten-first
  -- (newline gaps → spaces), never the source bytes — deciding on canonTok
  -- made pass 1 break a source-multi-line sig that pass 2 then re-inlined
  -- (gate-caught fixed-point on mathlib SetAlgebra/Action)
  let sigT := (Lean4Fmt.Emit.token_join_flat? dargs[2]!).getD
    ((bare_src dargs[2]!).trimAscii.toString)
  let flatHead := if sigT.isEmpty then hd0 else hd0 ++ " " ++ sigT
  if !flatHead.any (· == '\n') && flatHead.length + 6 ≤ (← read).layout.lineWidth then
    return some (.text (flatHead ++ " where") ++ .nest 2 body)
  -- the head doesn't fit on one line: the shared sig machinery (sigDoc)
  -- breaks it — binders/type per the knob, aligned under the name, ` where`
  -- glued to the sig's last line. This was the single largest mathlib bail
  -- class (defwhere-shape: long-signature Equiv/Iso defs). A sig carrying a
  -- multi-line re-anchoring piece normally keeps the whole declaration
  -- verbatim. At top-level, however, the signature starts at its original
  -- column and the independently rendered `where` body is nested only after
  -- that piece, so the opaque type remains anchored without owning the body.
  let sigD ← sig_doc walk (kwT.length + 1) flatHead.length 6 dargs[2]!
  return some (.text hd0 ++ sigD ++ .text " where" ++ .nest 2 body)

/-- `example <sig> := value`: keyword + signature single-line, the value via
    the shared head-value placement. -/
private
def example_doc? (walk : Lean4Fmt.Emit.Walk) (defn : Lean.Syntax) : emit_m (Option Doc) := do
  let dargs := defn.getArgs
  if dargs.size != 3 then
    return none
  let mut head := ""
  for h : idx in [0:2] do
    let child := dargs[idx]!
    -- the FIRST child's leading is the DECL's leading — the Module seam owns
    -- it (a `-- note` above an example must not evict the inline path; found
    -- as first-after-comment examples breaking while identical twins inline)
    let ownLead :=
      if idx == 0 then
        Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? child).getD "")
      else
        0
    if Lean4Fmt.Syntax.count_subtree_line_comments child > ownLead then
      return none
    let text := Lean4Fmt.Emit.canon_tok child
    -- flatten-first: a multi-line signature's canonical one-line spelling
    let wLim := (← read).layout.lineWidth
    let text :=
      if text.any (· == '\n') then
        match Lean4Fmt.Emit.token_join_flat? child with
        | some ftValue => if ftValue.length + 16 ≤ wLim then ftValue else text
        | none         => text
      else
        text
    if text.any (· == '\n') then
      return none
    if !text.isEmpty then head := if head.isEmpty then text else head ++ " " ++ text
  if head.isEmpty then
    return none
  if dargs[2]!.getKind != ``Lean.Parser.Command.declValSimple then
    return none
  head_val_doc? walk head dargs[2]!

/-- Value placement behind a Doc-valued (already multi-line) head: no inline
    path — the value glues or breaks per the knobs. -/
private
def doc_head_val_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (documentProof : Doc)
    (declVal : Lean.Syntax)
    : emit_m (Option Doc) := do
  let bodyOwnLine := (← read).breaking.bodyOwnLine
  match span_body_blank bodyOwnLine declVal (← valForm walk declVal) with
  | .span document => return some (documentProof ++ .text " " ++ document)
  | .body document glue =>
    if glue then
      return some
        (
          documentProof ++ .text " := "
              ++ (if bodyOwnLine then glue_body_blank document else document)
        )
    else if bodyOwnLine then
      return some (documentProof ++ .text " :=" ++ .nest 2 (.blank 1 ++ document))
    else
      return some (documentProof ++ .text " :=" ++ .nest 2 (.hardline ++ document))
  | .eqns _ => return none

/-- An `example` whose signature cannot flatten: binders via the kit, the
    TYPE walked at the continuation, value behind the Doc head. -/
private
def example_walked_doc? (walk : Lean4Fmt.Emit.Walk) (defn : Lean.Syntax) : emit_m (Option Doc) := do
  let dargs := defn.getArgs
  if dargs.size != 3 then
    return none
  if Lean4Fmt.Syntax.interior_has_line_comment defn then
    return none
  if dargs[2]!.getKind != ``Lean.Parser.Command.declValSimple then
    return none
  let signatureArgs := dargs[1]!.getArgs
  if signatureArgs.size < 2 then
    return none
  let mut head : Doc := .text ((bare_src dargs[0]!).trimAscii.toString)
  for binder in ((signatureArgs[0]?).map (·.getArgs)).getD #[] do
    let bd ← Lean4Fmt.Emit.binder_doc walk binder
    if Lean4Fmt.Doc.hasMultilineVerbatim bd then
      return none
    head := head ++ .space ++ bd
  let tyNode :=
    (
      signatureArgs[1]?.bind
        (
          fun candidate =>
            if candidate.getKind == ``Lean.Parser.Term.typeSpec then
              some candidate
            else
              candidate.getArgs[0]?
        )
    ).getD
      .missing
  if tyNode.getKind != ``Lean.Parser.Term.typeSpec then
    return none
  let tyDoc ← walk (tyNode.getArgs[1]?.getD .missing)
  if Lean4Fmt.Doc.hasMultilineVerbatim tyDoc then
    return none
  let cont := (← read).layout.continuationIndent
  doc_head_val_doc? walk (head ++ .text " :" ++ .group (.nest cont (.line ++ tyDoc))) dargs[2]!

/-- Fallback for an `example` whose SIGNATURE spans lines (quasiquote types):
    the keyword rides active, everything from the signature on is ONE
    re-anchored span — the decl participates in module structure (blank
    rhythm) while its interior stays byte-exact. -/
private
def example_span_doc? (defn : Lean.Syntax) : emit_m (Option Doc) := do
  let dargs := defn.getArgs
  if dargs.size != 3 then
    return none
  let kwT := (bare_src dargs[0]!).trimAscii.toString
  if kwT.isEmpty || kwT.any (· == '\n') then
    return none
  let rest := Lean.mkNullNode (dargs.extract 1 dargs.size)
  let text := bare_src rest
  if text.isEmpty then
    return none
  return some (.text (kwT ++ " ") ++ (← verbatim_quiet rest))

private
def append_instance_binder
    (preserve : Bool)
    (state : instance_head_state)
    (binder : Lean.Syntax)
    : instance_head_state :=
  match Lean4Fmt.Emit.binder_text? binder preserve with
  | some text => { state with head := state.head ++ " " ++ text }
  | none =>
    let text := (bare_src binder).trimAscii.toString
    if text.isEmpty || text.any (· == '\n') then
      { state with flatOk := false }
    else
      { state with head := state.head ++ " " ++ text }

private
def instance_head?
    (walk : Lean4Fmt.Emit.Walk)
    (defn : Lean.Syntax)
    : emit_m (Option (instance_head_state × String × Lean.Syntax)) := do
  let args := defn.getArgs
  if args.size != 6 then
    return none
  let attrText := (bare_src args[0]!).trimAscii.toString
  let priorityText := (bare_src args[2]!).trimAscii.toString
  let idText := (bare_src args[3]!).trimAscii.toString
  if attrText.any (· == '\n') || priorityText.any (· == '\n') || idText.any (· == '\n') then
    return none
  let mut state : instance_head_state :=
    { head := (if attrText.isEmpty then "" else attrText ++ " ") ++ "instance" }
  if !priorityText.isEmpty then state := { state with head := state.head ++ " " ++ priorityText }
  if !idText.isEmpty then state := { state with head := state.head ++ " " ++ idText }
  let flatHead := state.head
  let sig := args[4]!
  let sigArgs := sig.getArgs
  let preserve := (← read).spacing.preserveBinders
  for binder in ((sigArgs[0]?).map (·.getArgs)).getD #[] do
    state := append_instance_binder preserve state binder
  let some typeSpec := sigArgs[1]? | return none
  let typeSyntax := (typeSpec.getArgs[1]?).getD .missing
  let typeText := Lean4Fmt.Emit.canon_tok typeSyntax
  if typeText.isEmpty then
    return none
  let lineWidth := (← read).layout.lineWidth
  let typeText :=
    if typeText.any (· == '\n') then
      match Lean4Fmt.Emit.token_join_flat? typeSyntax with
      | some flatText =>
        if state.head.length + 3 + flatText.length + 6 ≤ lineWidth then flatText else typeText
      | none => typeText
    else
      typeText
  if typeText.any (· == '\n') || state.head.length + 3 + typeText.length + 6 > lineWidth then
    let typeDoc ← walk typeSyntax
    if Lean4Fmt.Doc.hasMultilineVerbatim typeDoc then
      return none
    let continuationIndent := (← read).layout.continuationIndent
    state :=
      { state with
        headTail? := some (.text " :" ++ .group (.nest continuationIndent (.line ++ typeDoc))) }
  else state := { state with head := state.head ++ " : " ++ typeText }
  return some (state, flatHead, sig)

/-- Active layout for `instance` declarations: head on one line
    (`instance (prio)? (name)? <binders> : τ`), then `:= value` (walked, the
    same placement rules as a def) or `where` + one field per line at +2 (the
    seam loop owning inter-field trivia), or equation arms nested below the
    head. Falls back to whole-declaration verbatim on: `where`-decls suffixes, comments in
    seamless zones, multi-line head pieces, or an over-wide head. -/
private
def instance_doc_head_value?
    (walk : Lean4Fmt.Emit.Walk)
    (head : Doc)
    (declVal : Lean.Syntax)
    : emit_m (Option Doc) := do
  if declVal.getKind == ``Lean.Parser.Command.whereStructInst then
    let some body ← where_body_doc? walk declVal | return none
    return some (head ++ .text " where" ++ .nest 2 body)
  if declVal.getKind == ``Lean.Parser.Command.declValSimple then
    return (← doc_head_val_doc? walk head declVal)
  if declVal.getKind == ``Lean.Parser.Command.declValEqns then
    match ← equation_value walk declVal with
    | .eqns arms => return some (head ++ .nest 2 arms)
    | _ => return none
  return none

private
def instance_doc? (walk : Lean4Fmt.Emit.Walk) (defn : Lean.Syntax) : emit_m (Option Doc) := do
  let args := defn.getArgs
  let some (state, hd0, sigSyntax) ← instance_head? walk defn | return none
  let width := (← read).layout.lineWidth
  if !state.flatOk || (state.headTail?.isNone && state.head.length + 6 > width) then
    -- over-width or unjoinable flat head: the shared sig machinery breaks it
    -- (the defwhere recipe) — binders/type per the knob under the keyword,
    -- the value behind the Doc head (docHeadValDoc?) or the where body
    let sigD ← sig_doc walk 9 state.head.length 6 sigSyntax
    if Lean4Fmt.Doc.hasMultilineReanchor sigD then
      return none
    return (← instance_doc_head_value? walk (.text hd0 ++ sigD) args[5]!)
  match state.headTail? with
  | some tail => return (← instance_doc_head_value? walk (.text state.head ++ tail) args[5]!)
  | none => pure ()
  let declVal := args[5]!
  if declVal.getKind == ``Lean.Parser.Command.declValSimple then
    head_val_doc? walk state.head declVal
  else if declVal.getKind == ``Lean.Parser.Command.declValEqns then
    match ← equation_value walk declVal with
    | .eqns arms => return some (.text state.head ++ .nest 2 arms)
    | _ => return none
  else if declVal.getKind == ``Lean.Parser.Command.whereStructInst then
    match ← where_body_doc? walk declVal with
    | some body => return some (.text (state.head ++ " where") ++ .nest 2 body)
    | none => return none
  else
    return none

/-- True when a line comment hides in the modifiers REGION: in trivia between the
    region's tokens (e.g. between the doc comment and a visibility keyword), or in
    the gap between the last modifier and the declaration keyword. `modifiersDoc`
    reflows the modifiers from bare token text, which would silently drop such a
    comment — the caller reproduces the whole declaration verbatim instead. Two
    exemptions: the first token's LEADING trivia (the declaration's outer leading —
    comments above the decl — placed byte-exact by `Module`), and docstring TEXT
    (`--` inside `/-- … -/` is token content, not a trivia comment). -/
private
def modifiers_comment_hazard (modeValue defn : Lean.Syntax) : Bool :=
  Id.run
    do
      -- an ownable full-line comment run in a LATER piece's leading is NOT a
      -- hazard anymore — modifiersDoc places it at the own-line seam
      -- (leadingSep?); comments in a piece's INTERIOR trivia or same-line
      -- trailing, or an unownable leading shape, keep the bail. Detection is
      -- COUNT-based over TRIVIA, never a naive substring test on token text:
      -- `@[to_additive /-- doc -/]` carries `--` inside a docstring ARGUMENT
      -- (token content, not a comment) — the naive test sent every such
      -- decl verbatim (round-6 census regression, 13 files dropped)
      let hasCommentContent :=
        fun (line : String) =>
          Lean4Fmt.Syntax.has_line_comment line || (line.splitOn "/-").length > 1
      let unownable :=
        fun (line : String) => hasCommentContent line && (Lean4Fmt.Doc.leading_sep? line).isNone
      let mut seenTokens := false
      for child in modeValue.getArgs do
        let isAttribute := (modeValue.getArgs[1]?.map (· == child)).getD false
        let ownedTrailComments :=
          if isAttribute then
            Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.trailing? child).getD "")
          else
            0
        if seenTokens then
          let lead := (Lean4Fmt.Syntax.leading? child).getD ""
          let leadC := Lean4Fmt.Syntax.count_line_comments lead
          if Lean4Fmt.Syntax.count_subtree_line_comments child > leadC + ownedTrailComments then
            return true
          if unownable lead then
            return true
        else if !(bare_src child).isEmpty then
          seenTokens := true
          -- the docComment slot is a null WRAPPER around the docComment node, and
          -- docstring text starts with `/--` — which contains `--` — so the bare-text
          -- check must exempt it (its interior holds no trivia anyway)
          let isDocWrap :=
            child.getKind == ``Lean.Parser.Command.docComment
                || (child.getArgs[0]?.map (·.getKind == ``Lean.Parser.Command.docComment)).getD
                  false
          if !isDocWrap && Lean4Fmt.Syntax.has_line_comment (bare_src child) then
            return true
          if !isAttribute
              && Lean4Fmt.Syntax.has_line_comment ((Lean4Fmt.Syntax.trailing? child).getD "") then
            return true
      -- gap between the last modifier and the keyword = the defn head's leading;
      -- with no modifier tokens at all that gap IS the outer leading (exempt).
      -- With INLINE rest modifiers (`protected def`), the keyword shares
      -- their line — a comment between them has no own-line seam: bail.
      let kwLead := (Lean4Fmt.Syntax.leading? defn).getD ""
      let restNonempty :=
        (modeValue.getArgs.toList.drop 2).any
          (fun child => !(bare_src child).trimAscii.toString.isEmpty)
      if seenTokens && restNonempty && Lean4Fmt.Syntax.has_line_comment kwLead then
        return true
      return seenTokens && unownable kwLead

private
structure emit_context where
  outer        : Lean.Syntax
  defn         : Lean.Syntax
  preserve     : Bool
  attrsOwnLine : Bool
  visOwnLine   : Bool
  defShape     : Bool
  valKind      : Option SyntaxNodeKind

private
def emit_context.modifier_hazard (ctx : emit_context) : Bool :=
  (ctx.outer.getArgs[0]?.map (modifiers_comment_hazard · ctx.defn)).getD false

private
def emit_context.with_modifiers (ctx : emit_context) (body : Doc) : Doc :=
  add_modifiers ctx.attrsOwnLine ctx.visOwnLine ctx.outer ctx.defn body

private
def sig_only_doc? (walk : Lean4Fmt.Emit.Walk) (defn : Lean.Syntax) : emit_m (Option Doc) := do
  let args := defn.getArgs
  if args.size < 3 then
    return none
  let keyword := (bare_src args[0]!).trimAscii.toString
  let identifier := (bare_src args[1]!).trimAscii.toString
  if keyword.isEmpty || keyword.any (· == '\n') || identifier.any (· == '\n') then
    return none
  for child in args.extract 3 args.size do
    if !(bare_src child).trimAscii.toString.isEmpty then
      return none
  if Lean4Fmt.Syntax.interior_has_line_comment defn then
    return none
  let signatureArgs := args[2]!.getArgs
  if signatureArgs.size < 2 then
    return none
  let mut head : Doc := .text (keyword ++ (if identifier.isEmpty then "" else " " ++ identifier))
  for binder in ((signatureArgs[0]?).map (·.getArgs)).getD #[] do
    let binderDoc ← Lean4Fmt.Emit.binder_doc walk binder
    if Lean4Fmt.Doc.hasMultilineVerbatim binderDoc then
      return none
    head := head ++ .space ++ binderDoc
  let typeNode :=
    (
      signatureArgs[1]?.bind
        (
          fun child =>
            if child.getKind == ``Lean.Parser.Term.typeSpec then some child else child.getArgs[0]?
        )
    ).getD
      .missing
  if typeNode.getKind != ``Lean.Parser.Term.typeSpec then
    return none
  let typeDoc ← walk (typeNode.getArgs[1]?.getD .missing)
  if Lean4Fmt.Doc.hasMultilineVerbatim typeDoc then
    return none
  let continuationIndent := (← read).layout.continuationIndent
  return some (head ++ .text " :" ++ .group (.nest continuationIndent (.line ++ typeDoc)))

private
def route_instance? (walk : Lean4Fmt.Emit.Walk) (ctx : emit_context) : emit_m (Option Doc) := do
  if ctx.defn.getKind != ``Lean.Parser.Command.instance then
    return none
  if ctx.modifier_hazard then
    return some (← verbatim ctx.outer "modifier-seam-comment")
  let some body ← instance_doc? walk ctx.defn |
    let valueKind := (ctx.defn.getArgs[5]?.map (·.getKind)).getD `missing
    let reason := if valueKind == ``Lean.Parser.Command.whereStructInst then
      "instance-where-body"
    else
      "instance-shape"
    return some (← verbatim ctx.outer reason)
  return some (ctx.with_modifiers body)

private
def route_type_decl? (walk : Lean4Fmt.Emit.Walk) (ctx : emit_context) : emit_m (Option Doc) := do
  let kind := ctx.defn.getKind
  if kind != ``Lean.Parser.Command.inductive && kind != ``Lean.Parser.Command.structure then
    return none
  if ctx.modifier_hazard then
    return some (← verbatim ctx.outer "modifier-seam-comment")
  let alignment := (← read).alignment
  let body? ← if kind == ``Lean.Parser.Command.inductive then
    Command.inductive_doc? walk ctx.defn alignment.trailingComments alignment.maxDelta ctx.preserve
  else
    Command.structure_doc?
      walk
      ctx.defn
      alignment.trailingComments
      alignment.structFields
      alignment.maxDelta
      ctx.preserve
  -- Keep the wrapper active even when its body is not: modifiers own the seam
  -- before the byte-exact declaration child, so this composition is lossless.
  let reason :=
    if kind == ``Lean.Parser.Command.inductive then
      Command.inductive_failure_reason ctx.defn
    else
      Command.structure_failure_reason ctx.defn
  let some body := body? | return some (ctx.with_modifiers (← verbatim ctx.defn reason))
  return some (ctx.with_modifiers body)

private
def example_body? (walk : Lean4Fmt.Emit.Walk) (defn : Lean.Syntax) : emit_m (Option Doc) := do
  let some body ← example_doc? walk defn | return ← example_walked_doc? walk defn
  return some body

private
def route_example? (walk : Lean4Fmt.Emit.Walk) (ctx : emit_context) : emit_m (Option Doc) := do
  if ctx.defn.getKind != ``Lean.Parser.Command.example then
    return none
  if ctx.modifier_hazard then
    return some (← verbatim ctx.outer "modifier-seam-comment")
  let body? ← example_body? walk ctx.defn
  let body? ← if body?.isSome then pure body?
  else example_span_doc? ctx.defn
  let some body := body? | return some (← verbatim ctx.outer "example-shape")
  return some (ctx.with_modifiers body)

private
def route_def_where? (walk : Lean4Fmt.Emit.Walk) (ctx : emit_context) : emit_m (Option Doc) := do
  if !ctx.defShape || ctx.valKind != some ``Lean.Parser.Command.whereStructInst then
    return none
  if ctx.modifier_hazard then
    return some (← verbatim ctx.outer "modifier-seam-comment")
  -- Preserve an unsupported `where` body as the declaration child while the
  -- wrapper still formats its independently owned modifiers.
  let some body ← def_where_doc? walk ctx.defn |
    let body? ← where_body_doc? walk (ctx.defn.getArgs[3]?.getD .missing)
    let reason := if body?.isSome then "defwhere-signature" else "defwhere-body"
    return some (ctx.with_modifiers (← verbatim ctx.defn reason))
  return some (ctx.with_modifiers body)

private
def route_inactive? (walk : Lean4Fmt.Emit.Walk) (ctx : emit_context) : emit_m (Option Doc) := do
  let isEqns := ctx.valKind == some ``Lean.Parser.Command.declValEqns
  let active := ctx.valKind == some ``Lean.Parser.Command.declValSimple || isEqns
  if ctx.defShape && active then
    return none
  if ctx.modifier_hazard then
    return some (← verbatim ctx.outer "modifier-seam-comment")
  let source := bare_src ctx.defn
  if !source.isEmpty && !source.any (· == '\n') then
    let some joined := Lean4Fmt.Emit.token_join? ctx.defn
        | return some (← verbatim ctx.outer "join-fail")
    return some (ctx.with_modifiers (.text joined))
  let some body ← sig_only_doc? walk ctx.defn |
    return some (← verbatim ctx.outer "unported-value-multiline")
  return some (ctx.with_modifiers body)

private
def active_modifiers (ctx : emit_context) : Doc × Nat :=
  match ctx.outer.getArgs[0]? with
  | some modifiers =>
    if ctx.preserve && !(bare_src modifiers).trimAscii.toString.isEmpty then
      let source := (bare_src modifiers).trimAscii.toString
      let keywordGap := ((Lean4Fmt.Syntax.leading? ctx.defn).getD " ")
      let separator : Doc := if keywordGap.any (· == '\n') then .hardline else .text " "
      if source.any (· == '\n') then
        (Doc.verbatim source 0 ++ separator, 0)
      else
        (Doc.text source ++ separator, if keywordGap.any (· == '\n') then 0 else source.length + 1)
    else
      modifiers_doc
        ctx.attrsOwnLine
        modifiers
        ((Lean4Fmt.Syntax.leading? ctx.defn).getD "")
        ctx.visOwnLine
  | none => (.nil, 0)

private
def route_active (walk : Lean4Fmt.Emit.Walk) (ctx : emit_context) : emit_m Doc := do
  let isEqns := ctx.valKind == some ``Lean.Parser.Command.declValEqns
  if isEqns && !eqns_formattable (ctx.defn.getArgs[3]?.getD .missing) then
    return (← verbatim ctx.outer "eqns-unformattable")
  if ctx.modifier_hazard then
    return (← verbatim ctx.outer "modifier-seam-comment")
  let (modifiers, modifiersWidth) := active_modifiers ctx
  return modifiers ++ (← defn_doc walk modifiersWidth ctx.defn)

private
def make_emit_context (outer defn : Lean.Syntax) : emit_m emit_context := do
  let preserve := (← read).breaking.preserveLineBreaks
  let attributesOwnLine := (← read).breaking.attributesOwnLine
  let visibilityOwnLine := (← read).breaking.visibilityOwnLine
  let attrsOwnLine :=
    if preserve then
      let afterAttribute? := (outer.getArgs[0]?.map (·.getArgs.toList.drop 2)).getD []
        |>.findSome? (fun child =>
          if (bare_src child).isEmpty then none else Lean4Fmt.Syntax.leading? child)
      ((afterAttribute?.getD ((Lean4Fmt.Syntax.leading? defn).getD ""))).any (· == '\n')
    else
      attributesOwnLine
  let visOwnLine := visibilityOwnLine && !preserve
  let defShape := is_def_shape defn.getKind || (outer.getKind == `lemma && defn.getKind == `group)
  pure
    { outer        := outer,
      defn         := defn,
      preserve     := preserve,
      attrsOwnLine := attrsOwnLine,
      visOwnLine   := visOwnLine,
      defShape     := defShape,
      valKind      := defn.getArgs[3]?.map (·.getKind) }

private partial
def adaptation_note_in_anonymous_ctor (stx : Lean.Syntax) : Bool :=
  (stx.getKind == ``Lean.Parser.Term.anonymousCtor && (bare_src stx).contains "#adaptation_note")
      || stx.getArgs.any adaptation_note_in_anonymous_ctor

/-- Emit a declaration through ordered, total declaration-family routes. -/
def emit (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let some defn := stx.getArgs[1]? | return (← verbatim stx "decl-shape")
  let defnSource := bare_src defn
  let declarationSource := bare_src stx
  if declarationSource.contains "m!\"" && declarationSource.contains "\\\n" then
    return (← source_exact stx "message-interpolation-whitespace")
  if adaptation_note_in_anonymous_ctor defn then
    return (← source_exact stx "adaptation-note-whitespace")
  if (declarationSource.splitOn "ℓ^").length > 1 then
    return (← verbatim stx "lp-notation")
  if (defnSource.splitOn "\n").any (fun line => line.trimAscii.toString == "--") then
    return (← verbatim stx "empty-line-comment")
  -- A declaration body whose first tactic begins at column zero relies on a
  -- command/tactic boundary that canonical indentation would change.
  if (defnSource.splitOn "\nexact ").length > 1 then
    return (← verbatim stx "zero-column-tactic")
  let ctx ← make_emit_context stx defn
  let some doc ← route_instance? walk ctx | do
    let some doc ← route_type_decl? walk ctx | do
      let some doc ← route_example? walk ctx | do
        let some doc ← route_def_where? walk ctx | do
          let some doc ← route_inactive? walk ctx | return ← route_active walk ctx
          return doc
        return doc
      return doc
    return doc
  return doc

end Lean4Fmt.Emit.Decl
