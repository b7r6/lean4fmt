/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // EMIT // Command
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Open-recursion emitter for the Command category (doc/design.md §6): `inductive`
    declarations (reached through `Decl.emit` — the modifiers live there). The
    head goes on one line, each constructor on its own line at +2 (doc comment
    above it, byte-exact), `deriving` at +2 below. Anything the layout can't
    hold — old `:=`-style bodies, computed fields, a line comment anywhere, a
    multi-line head or constructor — returns `none` and the whole declaration
    reproduces verbatim, guarded by the safety gate as always.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.emit.monad
import lean_4_fmt.emit.tokens
import lean_4_fmt.emit.binders
import lean_4_fmt.syntax.trivia

namespace Lean4Fmt.Emit.Command

open Lean Lean4Fmt.Doc Lean4Fmt.Emit

/-- Accumulated constructor signature while its binders and result type are
    classified for flat or fill layout. -/
private
structure ctor_state where
  parts    : Array String := #[]
  fillDocs : Array Doc := #[]
  needFill : Bool := false
  tyDoc?   : Option Doc := none

private
def ctor_binders? (binders : Array Lean.Syntax) : Option ctor_state :=
  Id.run do
    let mut state : ctor_state := {}
    for binder in binders do
      let token := Lean4Fmt.Emit.canon_tok binder
      if token.any (· == '\n') then
        let some flat := Lean4Fmt.Emit.token_join_flat? binder | return none
        state := { state with
          needFill := true
          parts := state.parts.push flat
          fillDocs := state.fillDocs.push (.text flat)
        }
      else
        state := { state with
          parts := state.parts.push token
          fillDocs := state.fillDocs.push (.text token)
        }
    return some state

private
def ctor_type?
    (walk : Lean4Fmt.Emit.Walk)
    (typeSlot : Array Lean.Syntax)
    (prefixLength : Nat)
    (state : ctor_state)
    : Lean4Fmt.Emit.emit_m (Option (ctor_state × Option String)) := do
  if typeSlot.isEmpty then
    return some (state, none)
  let [typeSpec] := typeSlot.toList | return none
  let typeSyntax := (typeSpec.getArgs[1]?).getD .missing
  let token := Lean4Fmt.Emit.canon_tok typeSyntax
  if token.isEmpty then
    return none
  let flat? :=
    if token.any (· == '\n') then Lean4Fmt.Emit.token_join_flat? typeSyntax else some token
  let some flat := flat?
      | do
        let doc ← walk typeSyntax
        if Lean4Fmt.Doc.hasMultilineVerbatim doc then
          return none
        return some ({ state with tyDoc? := some doc }, none)
  if prefixLength + 3 + flat.length + 4 ≤ (← read).layout.lineWidth then
    return some (state, some flat)
  let doc ← walk typeSyntax
  if Lean4Fmt.Doc.hasMultilineVerbatim doc then
    return none
  return some ({ state with tyDoc? := some doc }, none)

private
def ctor_line_doc?
    (state : ctor_state)
    (modifiers name : String)
    (typeText? : Option String)
    (joined : String)
    (width : Nat)
    : Option Doc :=
  match state.tyDoc? with
  | some typeDoc =>
    let armHead := "| " ++ (if modifiers.isEmpty then "" else modifiers ++ " ") ++ name
    if state.parts.isEmpty then
      some (.text (armHead ++ " :") ++ .group (.nest 4 (.line ++ typeDoc)))
    else
      some
        (
          .text (armHead ++ " ")
              ++ .nest
                6
                (
                  Doc.fillSep state.fillDocs.toList ++ .text " :"
                      ++ .group (.nest 4 (.line ++ typeDoc))
                )
        )
  | none =>
    if (state.needFill || joined.length + 4 > width) && !state.fillDocs.isEmpty then
      some
        (
          .text ("| " ++ (if modifiers.isEmpty then "" else modifiers ++ " ") ++ name ++ " ")
              ++ .nest
                6
                (
                  Doc.fillSep state.fillDocs.toList
                      ++ (typeText?.map (fun text => Doc.text (" : " ++ text))).getD .nil
                )
        )
    else
      none

/-- One constructor `(/-- doc -/)? | (modifiers)? name (binders)* (: τ)?`, as a
    single line (the doc comment on its own line above). `none` on a multi-line
    piece or a structural surprise — the caller reproduces the whole
    declaration. -/
private
def ctor_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (character : Lean.Syntax)
    (preserve : Bool)
    : Lean4Fmt.Emit.emit_m (Option (Doc × String × Option Doc)) := do
  if character.getKind != ``Lean.Parser.Command.ctor then
    return none
  let args := character.getArgs
  if args.size != 5 then
    return none
  let docT := (bare_src args[0]!).trimAscii.toString
  let modsT := (bare_src args[2]!).trimAscii.toString
  let nameT := (bare_src args[3]!).trimAscii.toString
  if nameT.isEmpty || nameT.any (· == '\n') || modsT.any (· == '\n') then
    return none
  let sig := args[4]!.getArgs
  let some state := ctor_binders? (((sig[0]?).map (·.getArgs)).getD #[]) | return none
  let prefixLen :=
    2 + (if modsT.isEmpty then 0 else modsT.length + 1) + nameT.length
        + state.parts.foldl (fun width part => width + 1 + part.length) 0
  let some (state, tyT) ←
    ctor_type? walk (((sig[1]?).map (·.getArgs)).getD #[]) prefixLen state | return none
  let joined :=
    "| " ++ (if modsT.isEmpty then "" else modsT ++ " ") ++ nameT
      ++ (state.parts.foldl (fun text part => text ++ " " ++ part) "")
        ++ (tyT.map (fun text => " : " ++ text)).getD ""
  let exact :=
    (Lean4Fmt.Emit.bare_src (Lean.mkNullNode (args.extract 1 args.size))).trimAscii.toString
  let line := if preserve && !exact.isEmpty && !exact.any (· == '\n') then "| " ++ exact else joined
  let lineDoc? := ctor_line_doc? state modsT nameT tyT joined (← read).layout.lineWidth
  let docD : Doc := if docT.isEmpty then .nil else .textRaw docT ++ .hardline
  return some (docD, line, lineDoc?)

/-- A body item for the seam-owning loops: its separator (leading trivia,
    already placed), whether that separator is a plain single newline, its
    prefix (doc comment lines), the single-line content, and its trailing
    comment (empty when none / not owned). -/
private
structure item where
  sep       : Doc
  plainSep  : Bool
  prefixDoc : Doc
  hasPrefix : Bool
  line      : String
  /-- Doc-valued line (multi-line types walk); excluded from grids. -/
  lineDoc : Option Doc := none
  /-- the `name (binders)` segment of `line`, when the site aligns name columns
      (§7 structFields); empty when the site aligns trailing comments only -/
  nameSeg : String := ""
  /-- the `: τ (:= v)` remainder matching `nameSeg` -/
  restSeg : String := ""
  trailT : String
  deriving Inhabited

/-- Output and pending alignment run threaded through body-item assembly. -/
private
structure assemble_state where
  out : Doc := .nil
  run : Array item := #[]

/-- Pieces accumulated while a structure field is classified. -/
private
structure field_state where
  modifiers   : String := ""
  binders     : Array String := #[]
  typeDoc?    : Option Doc := none
  defaultDoc? : Option Doc := none

private
structure field_parts where
  prefixDoc : Doc
  name      : String
  rest      : String
  line      : String
  lineDoc?  : Option Doc

private
def field_modifiers? (node : Lean.Syntax) : Option (String × String) :=
  Id.run do
    let arguments := node.getArgs
    let docText := ((arguments[0]?.map bare_src).getD "").trimAscii.toString
    let mut modifiers := ""
    for modifier in arguments.toList.drop 1 do
      let text := (bare_src modifier).trimAscii.toString
      if text.any (· == '\n') then
        return none
      if !text.isEmpty then modifiers := modifiers ++ text ++ " "
    return some (docText, modifiers)

private
def field_type?
    (walk : Lean4Fmt.Emit.Walk)
    (typeSlot : Array Lean.Syntax)
    (prefixLength : Nat)
    (state : field_state)
    : Lean4Fmt.Emit.emit_m (Option (field_state × Option String)) := do
  if typeSlot.isEmpty then
    return some (state, none)
  let [typeSpec] := typeSlot.toList | return none
  let typeSyntax := (typeSpec.getArgs[1]?).getD .missing
  let token := Lean4Fmt.Emit.canon_tok typeSyntax
  if token.isEmpty then
    return none
  if !token.any (· == '\n') then
    return some (state, some token)
  match Lean4Fmt.Emit.token_join_flat? typeSyntax with
  | some flat =>
    if prefixLength + flat.length ≤ (← read).layout.lineWidth then
      return some (state, some flat)
  | none => pure ()
  let doc ← walk typeSyntax
  if Lean4Fmt.Doc.hasMultilineVerbatim doc then
    return none
  return some ({ state with typeDoc? := some doc }, none)

private
def field_line_doc
    (state : field_state)
    (nameSegment : String)
    (typeText? : Option String)
    : Option Doc :=
  match state.typeDoc?, state.defaultDoc? with
  | some typeDoc, some defaultDoc => some (Doc.text (nameSegment ++ " : ") ++ typeDoc ++ defaultDoc)
  | some typeDoc, none => some (Doc.text (nameSegment ++ " : ") ++ typeDoc)
  | none, some defaultDoc =>
    some
      (
        Doc.text
          (
            nameSegment
                ++ (
                  match typeText? with
                  | some text => " : " ++ text
                  | none      => ""
                )
          )
            ++ defaultDoc
      )
  | none, none => none

private
def field_prefix_doc? (field : Lean.Syntax) (docText modifiers : String) : Option Doc :=
  Id.run do
    let nameLead :=
      if docText.isEmpty && modifiers.isEmpty then
        ""
      else
        ((Lean4Fmt.Syntax.leading? field.getArgs[1]!).getD "")
    let zoneLines :=
      (((nameLead.splitOn "\n").drop 1).dropLast.map (fun line => line.trimAscii.toString)).filter
        (fun line => !line.isEmpty)
    if !zoneLines.all (·.startsWith "--") then
      return none
    let mut doc : Doc := if docText.isEmpty then .nil else .textRaw docText ++ .hardline
    for line in zoneLines do
      doc := doc ++ .text line ++ .hardline
    return some doc

/-- Emit one unaligned body item, including its owned separator and comment. -/
private
def emit_plain_item (output : Doc) (current : item) : Doc :=
  output ++ current.sep ++ current.prefixDoc
      ++ (
        match current.lineDoc with
        | some doc => doc
        | none     => .text current.line
      )
      ++ (if current.trailT.isEmpty then Doc.nil else .text (" " ++ current.trailT))

/-- Flush one maximal alignment run, preserving its plain fallback exactly. -/
private
def flush_item_run (columnsEnabled : Bool) (cap : Nat) (output : Doc) (run : Array item) : Doc :=
  Id.run do
    if run.size < 2 then
      return run.foldl emit_plain_item output
    let fallback :=
      (List.range run.size).foldl
        (
          fun document idx =>
            let current := run[idx]!
            if idx == 0 then
              document ++ current.prefixDoc ++ .text current.line
                  ++ (if current.trailT.isEmpty then Doc.nil else .text (" " ++ current.trailT))
            else
              emit_plain_item document current
        )
        .nil
    let rows :=
      run.toList.map fun current =>
        if columnsEnabled && !current.nameSeg.isEmpty then
          if current.trailT.isEmpty then
            [Doc.text current.nameSeg, Doc.text current.restSeg]
          else
            [Doc.text current.nameSeg, Doc.text current.restSeg, Doc.text current.trailT]
        else if current.trailT.isEmpty then
          [Doc.text current.line]
        else
          [Doc.text current.line, Doc.text current.trailT]
    return output ++ run[0]!.sep ++ Doc.align_or { sep := " ", maxDelta := cap } rows fallback

/-- Assemble body items, aligning RUNS of consecutive plain items that carry
    trailing comments into `[code, comment]` alignTable rows (§7,
    `alignment.trailingComments`). A run breaks at: a doc-comment prefix, a
    non-plain separator (blank lines / placed comments — a blank line resets
    alignment, matching clang-format), or an item without a trailing comment.
    `.always` ignores the delta cap; `.whenShort` passes it to the renderer
    (which opts the whole run out rather than padding raggedly); `.never`
    emits everything plain. -/
private
def assemble
    (trailMode : Lean4Fmt.Style.align_mode)
    (colMode : Lean4Fmt.Style.align_mode)
    (maxDelta : Nat)
    (items : Array item)
    : Doc :=
  Id.run
    do
      let trailOn := trailMode != Lean4Fmt.Style.align_mode.never
      let colOn := colMode != Lean4Fmt.Style.align_mode.never
      let cap :=
        if trailMode == Lean4Fmt.Style.align_mode.always
            || colMode == Lean4Fmt.Style.align_mode.always then
          1000000
        else
          maxDelta
      -- run eligibility: plain separator, no doc-comment prefix, and — when only
      -- trailing alignment is on — a trailing comment to align
      let eligible (item : item) : Bool :=
        item.plainSep && !item.hasPrefix
            && ((colOn && !item.nameSeg.isEmpty) || (trailOn && !item.trailT.isEmpty))
      let mut state : assemble_state := {}
      for item in items do
        if eligible item then state := { state with run := state.run.push item }
        else
          state :=
            { out := emit_plain_item (flush_item_run colOn cap state.out state.run) item,
              run := #[] }
      return flush_item_run colOn cap state.out state.run

private
structure inductive_layout where
  head         : String
  constructors : Array Lean.Syntax
  derivingText : String
  derivingSep  : Doc

private
def append_inductive_type? (head : String) (typeSlot : Array Lean.Syntax) : Option String :=
  match typeSlot.toList with
  | [typeSpec] =>
    let token := Lean4Fmt.Emit.canon_tok ((typeSpec.getArgs[1]?).getD .missing)
    if token.isEmpty || token.any (· == '\n') then none else some (head ++ " : " ++ token)
  | [] => some head
  | _ => none

private
def inductive_layout? (defn : Lean.Syntax) : Option inductive_layout := do
  let args := defn.getArgs
  if args.size != 7 then none
  let ident := (bare_src args[1]!).trimAscii.toString
  if ident.isEmpty || ident.any (· == '\n') then none
  let signature := args[2]!.getArgs
  let mut head := "inductive " ++ ident
  for binder in ((signature[0]?).map (·.getArgs)).getD #[] do
    let token := Lean4Fmt.Emit.canon_tok binder
    let false := token.any (· == '\n') | none
    head := head ++ " " ++ token
  let some typedHead := append_inductive_type? head (((signature[1]?).map (·.getArgs)).getD #[])
      | none
  head := typedHead
  let whereText := ((args[3]?.map bare_src).getD "").trimAscii.toString
  if whereText != "where" && !whereText.isEmpty then none
  if !((args[5]?.map bare_src).getD "").trimAscii.toString.isEmpty then none
  if whereText == "where"
      && !((Lean4Fmt.Syntax.trailing? args[3]!).getD "").trimAscii.toString.isEmpty then none
  if whereText == "where" then head := head ++ " where"
  let constructors := (args[4]?.map (·.getArgs)).getD #[]
  if constructors.isEmpty then none
  let derivingSyntax := args[6]?.getD .missing
  let derivingText := Lean4Fmt.Emit.canon_tok derivingSyntax
  let derivingText :=
    if derivingText.any (· == '\n') then
      Lean4Fmt.Emit.token_join_flat? derivingSyntax |>.getD derivingText
    else
      derivingText
  if derivingText.any (· == '\n') then none
  let derivingSep ← if derivingText.isEmpty then some .nil
  else leading_sep? ((Lean4Fmt.Syntax.leading? args[6]!).getD "")
  return { head, constructors, derivingText, derivingSep }

/-- Verbatim fallback for a constructor `ctor_doc?` declined: a documented
    ctor splits its doc comment onto its own line above the verbatim tail;
    anything else ships whole. -/
private
def constructor_verbatim_piece
    (ctor : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m (Doc × String × Option Doc) := do
  let args := ctor.getArgs
  if ctor.getKind == ``Lean.Parser.Command.ctor && args.size == 5 then
    let docText := (bare_src args[0]!).trimAscii.toString
    if !docText.isEmpty then
      let tail := Lean.mkNullNode (args.extract 1 args.size)
      return
      (
        .textRaw docText ++ .hardline,
        "",
        some (← Lean4Fmt.Emit.verbatim tail "inductive-constructor-tail-piece")
      )
  return (.nil, "", some (← Lean4Fmt.Emit.verbatim ctor "inductive-constructor-piece"))

private
def constructor_items?
    (walk : Lean4Fmt.Emit.Walk)
    (constructors : Array Lean.Syntax)
    (hasDeriving preserve : Bool)
    : Lean4Fmt.Emit.emit_m (Option (Array item)) := do
  let mut items : Array item := #[]
  for h : idx in [0:constructors.size] do
    let ctor := constructors[idx]
    let trail := ((Lean4Fmt.Syntax.trailing? ctor).getD "").trimAscii.toString
    let owned := idx + 1 != constructors.size || hasDeriving
    if owned && trail.any (· == '\n') then
      return none
    let leading := (Lean4Fmt.Syntax.leading? ctor).getD ""
    let some separator := leading_sep? leading | return none
    let plainSeparator := ((leading.splitOn "\n").drop 1).dropLast.isEmpty
    let rendered ← if Lean4Fmt.Syntax.interior_has_line_comment ctor then pure none
    else ctor_doc? walk ctor preserve
    let (doc, line, lineDoc?) ← match rendered with
    | some rendered => pure rendered
    | none => constructor_verbatim_piece ctor
    let rawTrail := (((Lean4Fmt.Syntax.trailing? ctor).getD "").trimAsciiEnd).toString
    let (line, trail) :=
      if preserve && owned && !trail.isEmpty && !rawTrail.any (· == '\n') then
        (line ++ rawTrail, "")
      else
        (line, trail)
    items := items.push
      { sep := separator, plainSep := plainSeparator, prefixDoc := doc
        hasPrefix := !(doc matches Doc.nil), line, lineDoc := lineDoc?
        trailT := if owned then trail else "" }
  return some items

/-- Active layout for a `where`-style `inductive` body (the declaration node
    WITHOUT its modifiers — `Decl.emit` places those). `none` when this layout
    can't hold the input faithfully. -/
def inductive_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (defn : Lean.Syntax)
    (alignMode : Lean4Fmt.Style.align_mode)
    (alignDelta : Nat)
    (preserve : Bool := false)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let some layout := inductive_layout? defn | return none
  let hasDeriving := !layout.derivingText.isEmpty
  let some items ← constructor_items? walk layout.constructors hasDeriving preserve | return none
  let derivingDoc : Doc :=
    if hasDeriving then layout.derivingSep ++ .text layout.derivingText else .nil
  -- ctorsOneLine (purtell): an all-BARE ctor set (`| GET | POST …` — no
  -- docs, no comments, no binders/types) joins on ONE line when it fits —
  -- the enum-table idiom, headless form, ctor line at column 0
  if (← read).breaking.ctorsOneLine && !(layout.head.endsWith " where")
      && items.all (fun item => !item.hasPrefix && item.trailT.isEmpty && item.plainSep
        && item.lineDoc.isNone && (item.line.splitOn " ").length == 2) then
    let joined := String.intercalate " " (items.toList.map (·.line))
    if joined.length ≤ (← read).layout.lineWidth then
      return some (.text layout.head ++ .hardline ++ .text joined ++ .nest 2 derivingDoc)
  let body := assemble alignMode .never alignDelta items
  return some (.text layout.head ++ .nest 2 (body ++ derivingDoc))

/-- Name the unsupported inductive layer after `inductive_doc?` declines it. -/
def inductive_failure_reason (defn : Lean.Syntax) : String :=
  if (inductive_layout? defn).isSome then "inductive-constructors" else "inductive-head"

/-- One structure field `(/-- doc -/)? (modifiers)? name (binders)* : τ (:= v)?`,
    as a single line (the doc comment on its own line above — it lives INSIDE
    the field's declModifiers, unlike a ctor's). `none` on a multi-line piece,
    a parenthesized field group (`structExplicitBinder`), or a structural
    surprise. -/
private
def field_binders? (signature : Array Lean.Syntax) (state : field_state) : Option field_state :=
  Id.run do
    let mut next := state
    for binder in ((signature[0]?).map (·.getArgs)).getD #[] do
      let token := Lean4Fmt.Emit.canon_tok binder
      if token.any (· == '\n') then
        return none
      next := { next with binders := next.binders.push token }
    return some next

private
def field_default
    (walk : Lean4Fmt.Emit.Walk)
    (defaultNode : Lean.Syntax)
    (defaultText : String)
    (state : field_state)
    : Lean4Fmt.Emit.emit_m field_state := do
  if !defaultText.any (· == '\n') then
    return state
  let document ← walk defaultNode
  return { state with defaultDoc? := some (.nest 2 (.hardline ++ document)) }

/-- Assemble the rendered field line: modifiers + name + binders, the
    `: τ (:= v)?` tail, and the preserve-mode exact-bytes override. Returns
    `(nameSeg, restSeg, line, lineDoc?)`. -/
private
def field_render
    (args : Array Lean.Syntax)
    (state : field_state)
    (nameT : String)
    (tyT : Option String)
    (defT : String)
    (preserve : Bool)
    : String × String × String × Option Doc :=
  let defTFlat := if state.defaultDoc?.isSome then "" else defT
  let nameSeg :=
    state.modifiers ++ nameT ++ (state.binders.foldl (fun text binder => text ++ " " ++ binder) "")
  let restSeg :=
    (
      match tyT with
      | some trailing => ": " ++ trailing
      | none          => ""
    )
        ++ (if defTFlat.isEmpty then "" else (if tyT.isSome then " " else "") ++ defTFlat)
  let joined := nameSeg ++ (if restSeg.isEmpty then "" else " " ++ restSeg)
  -- exact tail: the field bytes from the name onward (doc rides docD)
  let exact :=
    (Lean4Fmt.Emit.bare_src (Lean.mkNullNode (args.extract 1 args.size))).trimAscii.toString
  let line :=
    if preserve && state.modifiers.isEmpty && !exact.isEmpty && !exact.any (· == '\n') then
      exact
    else
      joined
  (nameSeg, restSeg, line, field_line_doc state nameSeg tyT)

private
def field_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (transform : Lean.Syntax)
    (preserve : Bool)
    : Lean4Fmt.Emit.emit_m (Option field_parts) := do
  if transform.getKind == ``Lean.Parser.Command.structInstBinder
      || transform.getKind == ``Lean.Parser.Command.structImplicitBinder
      || transform.getKind == ``Lean.Parser.Command.structExplicitBinder then
    let some line := Lean4Fmt.Emit.token_join_flat? transform | return none
    return some { prefixDoc := .nil, name := line, rest := "", line, lineDoc? := none }
  if transform.getKind != ``Lean.Parser.Command.structSimpleBinder then
    return none
  let args := transform.getArgs
  if args.size != 4 then
    return none
  let some (docT, modifiers) := field_modifiers? args[0]! | return none
  let state : field_state := { modifiers }
  let nameT := (bare_src args[1]!).trimAscii.toString
  if nameT.isEmpty || nameT.any (· == '\n') then
    return none
  let sig := args[2]!.getArgs
  let some state := field_binders? sig state | return none
  let prefixLength :=
    2 + state.modifiers.length + nameT.length
        + (state.binders.foldl (fun total binder => total + 1 + binder.length) 0)
        + 3
  let some (state, tyT) ←
    field_type? walk (((sig[1]?).map (·.getArgs)).getD #[]) prefixLength state | return none
  let defT := ((args[3]?.map bare_src).getD "").trimAscii.toString
  -- Walk the whole default node: its bytes carry the `:=` and any `by`.
  let state ← field_default walk args[3]! defT state
  let state :=
    if state.typeDoc?.isSome && state.defaultDoc?.isNone && !defT.isEmpty then
      { state with defaultDoc? := some (.text (" " ++ defT)) }
    else
      state
  let (nameSeg, restSeg, line, lineDoc?) := field_render args state nameT tyT defT preserve
  -- comment LINES between the docstring/modifiers and the field name (the
  -- mathlib Porting-note zone): full `--` lines re-emitted in order between
  -- the docstring and the field line; anything else in that zone bails.
  -- The zone exists ONLY behind a docstring/modifier — with no prefix
  -- tokens the name's leading IS the field's leading, which the item loop
  -- already places (emitting it here doubled every bare-commented field:
  -- comments gate, mathlib ElementaryMaps)
  let some docD := field_prefix_doc? transform docT state.modifiers | return none
  return some { prefixDoc := docD, name := nameSeg, rest := restSeg, line, lineDoc? }

private
def append_structure_type? (head : String) (typeSlot : Array Lean.Syntax) : Option String :=
  match typeSlot.toList with
  | [typeSpec] =>
    let typeSyntax := (typeSpec.getArgs[1]?).getD .missing
    let token := Lean4Fmt.Emit.canon_tok typeSyntax
    let token :=
      if token.any (· == '\n') then
        Lean4Fmt.Emit.token_join_flat? typeSyntax |>.getD token
      else
        token
    if token.isEmpty || token.any (· == '\n') then none else some (head ++ " : " ++ token)
  | [] => some head
  | _ => none

private
def structure_head? (arguments : Array Lean.Syntax) : Option String :=
  Id.run do
    let keyword := (bare_src arguments[0]!).trimAscii.toString
    let identifier := (bare_src arguments[1]!).trimAscii.toString
    if keyword.isEmpty || keyword.any (· == '\n')
        || identifier.isEmpty || identifier.any (· == '\n') then return none
    let signature := arguments[2]!.getArgs
    let mut head := keyword ++ " " ++ identifier
    for binder in ((signature[0]?).map (·.getArgs)).getD #[] do
      let token := Lean4Fmt.Emit.canon_tok binder
      let token :=
        if token.any (· == '\n') then Lean4Fmt.Emit.token_join_flat? binder |>.getD token else token
      if token.any (· == '\n') then
        return none
      head := head ++ " " ++ token
    let some typedHead := append_structure_type? head (((signature[1]?).map (·.getArgs)).getD #[])
        | return none
    head := typedHead
    let extendsSyntax := arguments[3]?.getD .missing
    let extendsText := (bare_src extendsSyntax).trimAscii.toString
    let extendsText :=
      if extendsText.any (· == '\n') then
        Lean4Fmt.Emit.token_join_flat? extendsSyntax |>.getD extendsText
      else
        extendsText
    if extendsText.any (· == '\n') then
      return none
    if !extendsText.isEmpty then head := head ++ " " ++ extendsText
    return some head

private
def has_item_prefix : Doc → Bool
  | .nil => false
  | _    => true

private
def field_trail_available (trailText rawTrail : String) : Bool :=
  (trailText.isEmpty, rawTrail.contains '\n') == (false, false)

private
def owned_field_trail (owned : Bool) (trailText rawTrail : String) : Bool :=
  (owned, field_trail_available trailText rawTrail) == (true, true)

private
def should_preserve_field_trail (preserve owned : Bool) (trailText rawTrail : String) : Bool :=
  (preserve, owned_field_trail owned trailText rawTrail) == (true, true)

private
def field_source_line (preserveTrail : Bool) (sourceLine rawTrail : String) : String :=
  if preserveTrail then sourceLine ++ rawTrail else sourceLine

private
def field_trail_text (owned preserveTrail : Bool) (trailText : String) : String :=
  if owned && !preserveTrail then trailText else ""

private
def finish_field_item_parts
    (separator : Doc)
    (plainSeparator owned preserve : Bool)
    (doc : Doc)
    (nameSegment restSegment sourceLine : String)
    (lineDoc? : Option Doc)
    (trailText rawTrail : String)
    : item :=
  let preserveTrail := should_preserve_field_trail preserve owned trailText rawTrail
  { sep := separator, plainSep := plainSeparator, prefixDoc := doc
    hasPrefix := has_item_prefix doc
    line := field_source_line preserveTrail sourceLine rawTrail
    lineDoc := lineDoc?, nameSeg := nameSegment, restSeg := restSegment
    trailT := field_trail_text owned preserveTrail trailText }

private
def finish_field_item
    (separator : Doc)
    (plainSeparator owned preserve : Bool)
    (parsed : field_parts)
    (trailText rawTrail : String)
    : item :=
  finish_field_item_parts
    separator
    plainSeparator
    owned
    preserve
    parsed.prefixDoc
    parsed.name
    parsed.rest
    parsed.line
    parsed.lineDoc?
    trailText
    rawTrail

/-- Verbatim fallback for a field `field_doc?` declined: an unmodified simple
    binder splits its doc comment onto its own line above the verbatim tail;
    anything else ships the field whole. `none` when the doc-comment zone
    can't be owned. -/
private
def field_verbatim_parts? (field : Lean.Syntax) : Lean4Fmt.Emit.emit_m (Option field_parts) := do
  let args := field.getArgs
  if field.getKind == ``Lean.Parser.Command.structSimpleBinder && args.size == 4 then
    if let some (docText, modifiers) := field_modifiers? args[0]! then
      if modifiers.isEmpty then
        let some prefixDoc := field_prefix_doc? field docText modifiers | return none
        let tail := Lean.mkNullNode (args.extract 1 args.size)
        return some
          {
            prefixDoc
            name := ""
            rest := ""
            line := ""
            lineDoc? := some (← Lean4Fmt.Emit.verbatim tail "structure-field-tail-piece")
          }
  return some
    {
      prefixDoc := .nil
      name := ""
      rest := ""
      line := ""
      lineDoc? := some (← Lean4Fmt.Emit.verbatim field "structure-field-piece")
    }

private
def structure_field_tail?
    (walk : Lean4Fmt.Emit.Walk)
    (field : Lean.Syntax)
    (separator : Doc)
    (leading trailText : String)
    (owned preserve : Bool)
    : Lean4Fmt.Emit.emit_m (Option item) := do
  let plainSeparator := ((leading.splitOn "\n").drop 1).dropLast.isEmpty
  let rawTrail := (((Lean4Fmt.Syntax.trailing? field).getD "").trimAsciiEnd).toString
  let parsed? ← match ← field_doc? walk field preserve with
  | some parsed => pure (some parsed)
  | none => field_verbatim_parts? field
  let some parsed := parsed? | return none
  return some (finish_field_item separator plainSeparator owned preserve parsed trailText rawTrail)

private
def structure_field_item?
    (walk : Lean4Fmt.Emit.Walk)
    (field : Lean.Syntax)
    (owned preserve : Bool)
    : Lean4Fmt.Emit.emit_m (Option item) := do
  let trailText := ((Lean4Fmt.Syntax.trailing? field).getD "").trimAscii.toString
  if owned && trailText.any (· == '\n') then
    return none
  let leading := (Lean4Fmt.Syntax.leading? field).getD ""
  let some separator := leading_sep? leading | return none
  return ← structure_field_tail? walk field separator leading trailText owned preserve

private
def structure_field_items?
    (walk : Lean4Fmt.Emit.Walk)
    (fields : Array Lean.Syntax)
    (hasDeriving preserve : Bool)
    : Lean4Fmt.Emit.emit_m (Option (Array item)) := do
  let mut items := #[]
  for idx in [0:fields.size] do
    let owned := idx + 1 != fields.size || hasDeriving
    let some current ← structure_field_item? walk fields[idx]! owned preserve | return none
    items := items.push current
  return some items

/-- Active layout for a `structure`/`class` declaration (WITHOUT its modifiers —
    `Decl.emit` places those): head on one line
    (`structure Name <binders> (: τ)? (extends …)? where`), one field per line
    at +2 via the seam-owning item loop, `deriving` at +2 below. `none` when
    this layout can't hold the input (an explicit `mk ::`, parenthesized field
    groups, comments in seamless zones, multi-line pieces). -/
def structure_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (defn : Lean.Syntax)
    (alignMode : Lean4Fmt.Style.align_mode)
    (fieldColMode : Lean4Fmt.Style.align_mode)
    (alignDelta : Nat)
    (preserve : Bool := false)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let args := defn.getArgs
  if args.size != 6 then
    return none
  let some head := structure_head? args | return none
  -- deriving, shared with the fieldless form
  let derT := (args[5]?.map Lean4Fmt.Emit.canon_tok).getD ""
  if derT.any (· == '\n') then
    return none
  let hasDer := !derT.isEmpty
  let some derSep :=
    (if hasDer then leading_sep? ((Lean4Fmt.Syntax.leading? args[5]!).getD "") else some Doc.nil)
      | return none
  let derD : Doc := if hasDer then derSep ++ .text derT else .nil
  -- the where-block: ["where", mk?, structFields] — absent for a fieldless
  -- structure; own a single explicit constructor as the first body item.
  let wargs := (args[4]?.map (·.getArgs)).getD #[]
  if wargs.isEmpty then
    return some (.text head ++ .nest 2 derD)
  if wargs.size != 3 then
    return none
  if ((wargs[0]?.map bare_src).getD "").trimAscii.toString != "where" then
    return none
  if !((Lean4Fmt.Syntax.trailing? wargs[0]!).getD "").trimAscii.toString.isEmpty then
    return none
  let head := head ++ " where"
  let constructorDoc ← match wargs[1]!.getArgs.toList with
  | [] => pure Doc.nil
  | [constructor] => do
    let some constructorText := Lean4Fmt.Emit.token_join_flat? constructor | return none
    let some separator := leading_sep? ((Lean4Fmt.Syntax.leading? constructor).getD "")
        | return none
    pure (separator ++ .text constructorText)
  | _ => return none
  let fields := ((wargs[2]?.bind (·.getArgs[0]?)).map (·.getArgs)).getD #[]
  if fields.isEmpty then
    if Lean4Fmt.Syntax.count_subtree_line_comments wargs[2]! > 0
        || Lean4Fmt.Syntax.subtree_has_block_comment wargs[2]! then
      return none
    return some (.text head ++ .nest 2 (constructorDoc ++ derD))
  -- fields, one per line at +2: the loop OWNS the inter-field trivia (leading
  -- comment/blank lines placed structurally, same-line trailing comments
  -- re-appended; the LAST field's trailing belongs to the enclosing seam
  -- unless `deriving` follows)
  let some items ← structure_field_items? walk fields hasDer preserve | return none
  let body := constructorDoc ++ assemble alignMode fieldColMode alignDelta items
  return some (.text head ++ .nest 2 (body ++ derD))

/-- Name the unsupported structure layer after `structure_doc?` declines it. -/
def structure_failure_reason (defn : Lean.Syntax) : String :=
  let args := defn.getArgs
  if args.size != 6 || (structure_head? args).isNone then
    "structure-head"
  else
    let derivingText := (args[5]?.map Lean4Fmt.Emit.canon_tok).getD ""
    if derivingText.any (· == '\n') then
      "structure-deriving"
    else
      let whereArgs := (args[4]?.map (·.getArgs)).getD #[]
      if whereArgs.isEmpty then
        "structure-fieldless"
      else if whereArgs.size != 3
          || ((whereArgs[0]?.map bare_src).getD "").trimAscii.toString != "where"
          || !((Lean4Fmt.Syntax.trailing? whereArgs[0]!).getD "").trimAscii.toString.isEmpty then
        "structure-where-seam"
      else
        let fields := ((whereArgs[2]?.bind (·.getArgs[0]?)).map (·.getArgs)).getD #[]
        if fields.isEmpty then "structure-empty-body" else "structure-fields"

/-- Format Batteries' declaration-shaped deprecated alias command. -/
private
def emit_alias (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let args := stx.getArgs
  if args.size != 5 || Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← Lean4Fmt.Emit.verbatim stx)
  let modifiers := args[0]!
  let docText := ((modifiers.getArgs[0]?.map bare_src).getD "").trimAscii.toString
  let mut modDoc : Doc := if docText.isEmpty then .nil else .textRaw docText ++ .hardline
  let attrText := ((modifiers.getArgs[1]?.map Lean4Fmt.Emit.canon_tok).getD "").trimAscii.toString
  if attrText.any (· == '\n') then
    return (← Lean4Fmt.Emit.verbatim stx)
  if !attrText.isEmpty then modDoc := modDoc ++ .text attrText ++ .hardline
  let mut prelude := ""
  for child in modifiers.getArgs.toList.drop 2 do
    let token := Lean4Fmt.Emit.canon_tok child
    if token.any (· == '\n') then
      return (← Lean4Fmt.Emit.verbatim stx)
    if !token.isEmpty then prelude := prelude ++ token ++ " "
  let keyword := (bare_src args[1]!).trimAscii.toString
  let name := Lean4Fmt.Emit.canon_tok args[2]!
  let assignment := (bare_src args[3]!).trimAscii.toString
  let target := Lean4Fmt.Emit.canon_tok args[4]!
  if keyword.isEmpty || name.isEmpty || target.isEmpty
      || [keyword, name, assignment, target].any (·.any (· == '\n')) then
    return (← Lean4Fmt.Emit.verbatim stx)
  let assignment := if assignment.isEmpty then ":=" else assignment
  return modDoc
      ++ .group
        (
          .text (prelude ++ keyword ++ " " ++ name ++ " " ++ assignment)
              ++ .nest 2 (.line ++ .text target)
        )

private
structure elab_prefix where
  bodyIndex : Nat
  pieces    : Array (Doc × String)

private
def is_elab_doc (stx : Lean.Syntax) : Bool :=
  stx.getKind == ``Lean.Parser.Command.docComment
      || (stx.getArgs[0]?.map (·.getKind == ``Lean.Parser.Command.docComment)).getD false

private
def is_elab_attr (stx : Lean.Syntax) : Bool :=
  stx.getKind == `Lean.Parser.Term.attributes
      || (stx.getArgs[0]?.map (·.getKind == `Lean.Parser.Term.attributes)).getD false

private
def collect_elab_prefix (args : Array Lean.Syntax) : Option elab_prefix :=
  Id.run do
    let mut bodyIndex := 0
    let mut pieces : Array (Doc × String) := #[]
    for current in args do
      let text := (bare_src current).trimAscii.toString
      if text.isEmpty then bodyIndex := bodyIndex + 1
      else if is_elab_doc current then
        pieces := pieces.push (.textRaw text, (Lean4Fmt.Syntax.leading? current).getD "")
        bodyIndex := bodyIndex + 1
      else if is_elab_attr current then
        if text.any (· == '\n') then
          return none
        pieces := pieces.push (.text text, (Lean4Fmt.Syntax.leading? current).getD "")
        bodyIndex := bodyIndex + 1
      else break
    return some { bodyIndex, pieces }

private
def elab_has_comment (leading : String) : Bool :=
  Lean4Fmt.Syntax.has_line_comment leading || (leading.splitOn "/-").length > 1

private
def elab_separator? (leading : String) : Option Doc :=
  if elab_has_comment leading then Lean4Fmt.Emit.leading_sep? leading else some .hardline

private
def elab_prefix_doc? (args : Array Lean.Syntax) (elabPrefix : elab_prefix) : Option Doc :=
  Id.run do
    let headLeading :=
      (
        Lean4Fmt.Syntax.leading?
          (Lean.mkNullNode (args.extract elabPrefix.bodyIndex (args.size - 1)))
      ).getD
        ""
    for h : idx in [1:elabPrefix.pieces.size] do
      if (elab_separator? elabPrefix.pieces[idx].2).isNone then
        return none
    if !elabPrefix.pieces.isEmpty && (elab_separator? headLeading).isNone then
      return none
    let mut document : Doc := .nil
    for h : idx in [0:elabPrefix.pieces.size] do
      if idx > 0 then
        let some separator := elab_separator? elabPrefix.pieces[idx].2 | return none
        document := document ++ separator
      document := document ++ elabPrefix.pieces[idx].1
    if !elabPrefix.pieces.isEmpty then
      let some separator := elab_separator? headLeading | return none
      document := document ++ separator
    return some document

private
def elab_head_body?
    (args : Array Lean.Syntax)
    (bodyIndex : Nat)
    : Option (String × Lean.Syntax) := do
  let mut body := args[args.size - 1]!
  let mut tailHead := ""
  if body.getKind == ``Lean.Parser.Command.elabTail then
    let tailArgs := body.getArgs
    if tailArgs.size != 5 then none
    tailHead := Lean4Fmt.Emit.canon_tok (Lean.mkNullNode (tailArgs.extract 0 4))
    if tailHead.isEmpty || tailHead.any (· == '\n') then none
    body := tailArgs[4]!
  let sourceHead :=
    (bare_src (Lean.mkNullNode (args.extract bodyIndex (args.size - 1)))).trimAscii.toString
  let head := sourceHead ++ (if tailHead.isEmpty then "" else " " ++ tailHead)
  if head.isEmpty || head.any (· == '\n') then none
  return (head, body)

private
def emit_elab (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let args := stx.getArgs
  if args.size < 3 then
    return ← Lean4Fmt.Emit.verbatim stx
  let some elabPrefix := collect_elab_prefix args | return ← Lean4Fmt.Emit.verbatim stx
  if elabPrefix.bodyIndex ≥ args.size - 1 then
    return ← Lean4Fmt.Emit.verbatim stx
  let some prefixDoc := elab_prefix_doc? args elabPrefix | return ← Lean4Fmt.Emit.verbatim stx
  let some (head, body) := elab_head_body? args elabPrefix.bodyIndex
      | return ← Lean4Fmt.Emit.verbatim stx
  let bodyDoc ← walk body
  if (bodyDoc matches .verbatim _ _) || Lean4Fmt.Doc.has_midline_reanchor bodyDoc then
    return ← Lean4Fmt.Emit.verbatim stx
  let glue :=
    body.getKind == ``Lean.Parser.Term.do || body.getKind == ``Lean.Parser.Term.byTactic
        || body.getKind == `Lean.Parser.Term.byTactic'
  if glue then
    return prefixDoc ++ .text (head ++ " ") ++ bodyDoc
  return prefixDoc ++ .text head ++ .group (.nest 2 (.line ++ bodyDoc))

private
def emit_variable (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do

  -- `variable <binders>`: a MULTI-LINE binder list packs BINDER-WISE as a
  -- fillSep at the continuation (each binder one item — a token fill
  -- would wrap inside brackets); single-line lists fit on the line the
  -- same way (mathlib's long variable blocks were 4.3KB of the census)
  if Lean4Fmt.Syntax.has_owned_line_comment stx then
    return (← Lean4Fmt.Emit.verbatim stx)
  let binders := ((stx.getArgs[1]?).map (·.getArgs)).getD #[]
  let mut items : Array Doc := #[]
  for binder in binders do
    let bd ← Lean4Fmt.Emit.binder_doc walk binder
    if Lean4Fmt.Doc.hasMultilineReanchor bd then
      return (← Lean4Fmt.Emit.verbatim stx)
    if (Lean4Fmt.Doc.flat_width bd).isNone then
      return (← Lean4Fmt.Emit.verbatim stx)
    items := items.push (.flatten bd)
  if items.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  let cont := (← read).layout.continuationIndent
  return .text "variable " ++ .nest cont (Doc.fillSep items.toList)

private
structure open_pack_state where
  items   : Array String := #[]
  pending : String := ""

private
def push_open_token (state : open_pack_state) (token : String) : open_pack_state :=
  if token == "(" then
    { state with pending := state.pending ++ "(" }
  else if token == ")" then
    if state.items.isEmpty then
      { state with pending := state.pending ++ ")" }
    else
      { state with
        items := state.items.set! (state.items.size - 1) (state.items[state.items.size - 1]! ++ ")") }
  else
    { items := state.items.push (state.pending ++ token), pending := "" }

private
def open_items (tokens : List String) : Array String :=
  let state := tokens.foldl push_open_token {}
  if state.pending.isEmpty then state.items else state.items.push state.pending

private
def emit_open_tokens (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let tokens :=
    (Lean4Fmt.Emit.leaf_tokens stx).map (fun leaf => (bare_src leaf).trimAscii.toString)
      |>.filter (fun token => !token.isEmpty)
  if tokens.isEmpty || tokens.any (·.any (· == '\n')) then
    return ← Lean4Fmt.Emit.verbatim stx
  let keyword :: rest := tokens.toList | return ← Lean4Fmt.Emit.verbatim stx
  let continuation := (← read).layout.continuationIndent
  return .text (keyword ++ " ")
      ++ .nest continuation (Doc.fillSep ((open_items rest).toList.map Doc.text))

private
def simple_line? (stx : Lean.Syntax) : Option String :=
  Id.run do
    let mut line := ""
    for child in stx.getArgs do
      let token := Lean4Fmt.Emit.canon_tok child
      if token.any (· == '\n') then
        return none
      if !token.isEmpty then line := if line.isEmpty then token else line ++ " " ++ token
    if line.isEmpty then none
    else some line

private
def emit_simple (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let kind := stx.getKind
  -- trivial one-line commands, token-for-token; a MULTI-LINE command
  -- (an `open Ns (long ident list)`) reflows its tokens as a fillSep pool
  if Lean4Fmt.Syntax.has_owned_line_comment stx then
    return (← Lean4Fmt.Emit.verbatim stx)
  if kind == ``Lean.Parser.Command.open && (bare_src stx).any (· == '\n') then
    return ← emit_open_tokens stx
  let some line := simple_line? stx | return ← Lean4Fmt.Emit.verbatim stx
  return .text line

private
def emit_in (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do

  -- `open X in\n<command>` — prefix command token-for-token, the trailed
  -- command walked (usually a declaration; Decl does the real work)
  let args := stx.getArgs
  if args.size != 3 then
    return (← Lean4Fmt.Emit.verbatim stx)
  let preT := Lean4Fmt.Emit.canon_tok args[0]!
  if preT.isEmpty || preT.any (· == '\n') then
    return (← Lean4Fmt.Emit.verbatim stx)
  if !((Lean4Fmt.Syntax.trailing? args[1]!).getD "").trimAscii.toString.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some sep := leading_sep? ((Lean4Fmt.Syntax.leading? args[2]!).getD "")
      | return (← Lean4Fmt.Emit.verbatim stx)
  return .text (preT ++ " in") ++ sep ++ (← walk args[2]!)

private
def emit_mutual (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let args := stx.getArgs
  if args.size != 3 then
    return (← Lean4Fmt.Emit.verbatim stx)
  if ((args[2]?.map bare_src).getD "").trimAscii.toString != "end" then
    return (← Lean4Fmt.Emit.verbatim stx)
  -- a comment on the `mutual` line itself has no home in the layout
  if !((Lean4Fmt.Syntax.trailing? args[0]!).getD "").trimAscii.toString.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  let decls := (args[1]?.map (·.getArgs)).getD #[]
  if decls.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  let mut body : Doc := .nil
  for declaration in decls do
    let some sep := leading_sep? ((Lean4Fmt.Syntax.leading? declaration).getD "")
        | return (← Lean4Fmt.Emit.verbatim stx)
    let trailT := ((Lean4Fmt.Syntax.trailing? declaration).getD "").trimAscii.toString
    if trailT.any (· == '\n') then
      return (← Lean4Fmt.Emit.verbatim stx)
    let trailDoc : Doc := if !trailT.isEmpty then .text (" " ++ trailT) else .nil
    let dDoc ← walk declaration
    -- a member that reproduces as a multi-line RE-ANCHORING block (verbatim)
    -- drifts at +2 (only idempotent at its natural top-level column) — whole
    -- block verbatim. textRaw (multi-line docstrings, comment blocks) emits
    -- RAW at source columns, placement-stable — NOT counted (counting it kept
    -- every mutual with a multi-line-docstring'declaration member verbatim).
    if Lean4Fmt.Doc.hasMultilineReanchor dDoc then
      return (← Lean4Fmt.Emit.verbatim stx)
    body := body ++ sep ++ dDoc ++ trailDoc
  let some endSep := leading_sep? ((Lean4Fmt.Syntax.leading? args[2]!).getD "")
      | return (← Lean4Fmt.Emit.verbatim stx)
  return .text "mutual" ++ .nest 2 body ++ endSep ++ .text "end"

private
def is_simple_command (kind : Lean.SyntaxNodeKind) : Bool :=
  kind == ``Lean.Parser.Command.open || kind == ``Lean.Parser.Command.namespace
      || kind == ``Lean.Parser.Command.end
      || kind == ``Lean.Parser.Command.section
      || kind == ``Lean.Parser.Command.universe
      || kind == ``Lean.Parser.Command.eval

/-- Emit the Command construct rooted at `stx`, recursing via `walk`.
    Ordered command-family routing leaves unsupported syntax source-exact. -/
def emit (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc := do
  let kind := stx.getKind
  if kind == `Batteries.Tactic.Alias.alias then
    return ← emit_alias stx
  if kind == ``Lean.Parser.Command.elab then
    return ← emit_elab walk stx
  if kind == ``Lean.Parser.Command.variable then
    return ← emit_variable walk stx
  if is_simple_command kind then
    return ← emit_simple stx
  if kind == ``Lean.Parser.Command.in then
    return ← emit_in walk stx
  if kind == ``Lean.Parser.Command.mutual then
    return ← emit_mutual walk stx
  Lean4Fmt.Emit.verbatim stx

end Lean4Fmt.Emit.Command
