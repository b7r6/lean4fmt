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

import Lean4Fmt.Emit.Monad
import Lean4Fmt.Emit.Command
import Lean4Fmt.Syntax.Kinds

namespace Lean4Fmt.Emit.Decl

open Lean Lean4Fmt.Doc Lean4Fmt.Emit

/-- Emit a declaration's `declModifiers` = [docComment?, attributes?, visibility?,
    …]. The doc comment (always first) goes on its own line (literal `textRaw` —
    it may be multi-line — then a `hardline`). If `attrsOwnLine` (straylight),
    the attributes `@[…]` also get their own line above the keyword; otherwise
    they sit inline with the visibility modifiers on the keyword's line. Returns
    the doc and the width of the INLINE prefix it contributes to the keyword's
    line (used for signature width coupling and binder alignment: with
    attrsOwnLine only the visibility modifiers count, so binders align under the
    name at a shallower column). -/
private def modifiersDoc
            (attrsOwnLine : Bool)
            (m : Lean.Syntax)
            : Doc × Nat := Id.run do
  let margs := m.getArgs
  let docText := (margs[0]?.map bareSrc).getD "" |>.trimAscii.toString
  let attrText := (margs[1]?.map bareSrc).getD "" |>.trimAscii.toString
  let restParts := (margs.toList.drop 2).filterMap (fun c =>
    let s := (bareSrc c).trimAscii.toString; if s.isEmpty then none else some s)
  let docDoc : Doc := if docText.isEmpty then .nil else .textRaw docText ++ .hardline
  let restStr := String.intercalate " " restParts
  let restDoc : Doc := if restParts.isEmpty then .nil else .text restStr ++ .space
  let restW := if restParts.isEmpty then 0 else restStr.length + 1
  if attrsOwnLine then
    -- doc (own line) · attributes (own line) · visibility (inline)
    let attrDoc : Doc := if attrText.isEmpty then .nil else .text attrText ++ .hardline
    return (docDoc ++ attrDoc ++ restDoc, restW)
  else
    -- doc (own line) · attributes+visibility (inline)
    let allStr := String.intercalate " " ((if attrText.isEmpty then [] else [attrText]) ++ restParts)
    let inlineDoc : Doc := if allStr.isEmpty then .nil else .text allStr ++ .space
    let inlineW := if allStr.isEmpty then 0 else allStr.length + 1
    return (docDoc ++ inlineDoc, inlineW)

/-- Keyword-led definition shapes we actively format. -/
private def isDefShape
            (kind : SyntaxNodeKind)
            : Bool :=

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
private def eqnsFormattable
            (declVal : Lean.Syntax)
            : Bool := Id.run do
  if Lean4Fmt.Syntax.subtreeHasLineComment declVal then return false
  let mawd := (declVal.getArgs[0]?).getD .missing
  let margs := mawd.getArgs
  if (margs.toList.drop 1).any (fun s => !(bareSrc s).trimAscii.toString.isEmpty) then
    return false
  let altsNode := (margs[0]?).getD .missing
  let mut n := 0
  for g in altsNode.getArgs do
    for c in g.getArgs do
      if c.getKind == ``Lean.Parser.Term.matchAlt then n := n + 1
  return n != 0

/-- The comment block (if any) inside a trivia string: the non-whitespace-only
    lines, dedented to column 0 (so a caller can re-anchor them with
    `.verbatim … 0`). `none` when the trivia is pure whitespace. Lets onePerLine
    preserve inter-binder comments instead of dropping them (which would otherwise
    force the gate's identity fallback). -/
private def commentBlock?
            (trivia : String)
            : Option String :=

  Id.run
    do
      let isWs (l : String) : Bool := l.all (fun c => c == ' ' || c == '\t')
      let mut ls := trivia.splitOn "\n"
      ls := ls.dropWhile isWs
      ls := (ls.reverse.dropWhile isWs).reverse
      if ls.isEmpty then return none
      let indentOf (l : String) : Nat := (l.toList.takeWhile (· == ' ')).length
      let base := (ls.filter (fun l => !isWs l)).foldl (fun m l => Nat.min m (indentOf l)) 1000000
      let base := if base == 1000000 then 0 else base
      let dedented := ls.map (fun l => if l.length ≥ base then String.ofList (l.toList.drop base) else l)
      return some (String.intercalate "\n" dedented)

/-- A binder as a single active line: bracket atoms from source, the interior
    segments trimmed and single-spaced (`(x  :  Nat)` → `(x : Nat)`). Only the
    bracketed binder kinds; `none` (caller falls back to per-binder verbatim)
    on anything else, a multi-line piece, or a comment (a line comment forces a
    newline into its segment, so the '\n' guard covers it). -/
private def binderText?
            (b : Lean.Syntax)
            : Option String := Id.run do
  let k := b.getKind
  if k != ``Lean.Parser.Term.explicitBinder && k != ``Lean.Parser.Term.implicitBinder
      && k != ``Lean.Parser.Term.strictImplicitBinder && k != ``Lean.Parser.Term.instBinder then
    return none
  let a := b.getArgs
  if a.size < 3 then return none
  let l := (bareSrc a[0]!).trimAscii.toString
  let r := (bareSrc a[a.size-1]!).trimAscii.toString
  if l.isEmpty || r.isEmpty then return none
  let mut interior := ""
  for c in a.extract 1 (a.size - 1) do
    let t := (bareSrc c).trimAscii.toString
    if t.any (· == '\n') then return none
    if !t.isEmpty then interior := if interior.isEmpty then t else interior ++ " " ++ t
  if interior.isEmpty then return none
  return some (l ++ interior ++ r)

/-- A binder doc: active single-line text when `binderText?` can hold it,
    verbatim otherwise. -/
private def binderDoc
            (b : Lean.Syntax)
            : EmitM Doc := do
  match binderText? b with
  | some t => pure (.text t)
  | none => verbatim b

/-- Signature return-type info: `none` if there is no type spec, else
    `(termDoc, colonTypeDoc, flatWidth, multiline?)` where `termDoc` is the type
    term alone (no colon) — WALKED, so arrow chains and applications lay out
    actively and width-aware — and `colonTypeDoc` is the whole `: τ` byte-exact
    (with the colon). Callers use `termDoc` (adding their own `: `) when it is
    clean, and `colonTypeDoc` when the term carries a comment or a multi-line
    opaque block (so the colon and the bytes are never lost). -/
private def typeInfo
            (walk : Lean4Fmt.Emit.Walk)
            (sig : Lean.Syntax)
            : EmitM (Option (Doc × Doc × Nat × Bool)) := do
  let a := sig.getArgs
  let tsNode : Option Lean.Syntax := a[1]?.bind (fun x =>
    if x.getKind == ``Lean.Parser.Term.typeSpec then some x else x.getArgs[0]?)
  match tsNode with
  | some ts =>
    if ts.getKind == ``Lean.Parser.Term.typeSpec
        && !Lean4Fmt.Syntax.subtreeHasLineComment ts then
      let term ← walk (ts.getArgs[1]?.getD .missing)
      let colonType ← verbatim ts
      let w := (← read).layout.lineWidth
      -- a type too wide to EVER fit flat would explode into the all-or-nothing
      -- group layouts (a 20-element byte list, one element per line) — keep the
      -- author's hand-packed span for those until a fill mode exists (§5)
      let tooWide := (Lean4Fmt.Doc.flatWidth term).getD (w + 1) > w
      if Lean4Fmt.Doc.hasMultilineVerbatim term || tooWide then
        return some (colonType, colonType, (Lean4Fmt.Doc.flatWidth colonType).getD 0, true)
      return some (term, colonType, (Lean4Fmt.Doc.flatWidth term).getD 0, false)
    else
      let ct ← verbatim ts
      return some (ct, ct, (Lean4Fmt.Doc.flatWidth ct).getD 0, true)  -- comment/unexpected: whole span
  | none => return none

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
private def sigDoc
            (walk : Lean4Fmt.Emit.Walk)
            (nameCol prefixWidth reserve : Nat)
            (sig : Lean.Syntax)
            : EmitM Doc := do
  let a := sig.getArgs
  let binders := (a[0]?.map (·.getArgs)).getD #[]
  let ti ← typeInfo walk sig
  let mode := (← read).breaking.binders
  let cont := (← read).layout.continuationIndent
  let w := (← read).layout.lineWidth
  match mode with
  | .onePerLine =>
    let mut d : Doc := .nil
    for b in binders do
      -- preserve any comment sitting in this binder's leading trivia (e.g. an
      -- inter-binder comment) on its own line(s), re-anchored to the name column.
      match commentBlock? ((Lean4Fmt.Syntax.leading? b).getD "") with
      | some cmt => d := d ++ .hardline ++ .verbatim cmt 0
      | none => pure ()
      d := d ++ .hardline ++ (← binderDoc b)
    match ti with
    | some (term, colonType, _, multi) =>
      if multi then d := d ++ .hardline ++ colonType         -- multi-line type: own line, byte-exact
      else d := d ++ .hardline ++ .text ": " ++ term          -- breakBefore colon, own line
    | none => pure ()
    return .nest nameCol d
  | .fill =>
    let mut d : Doc := .nil
    let mut first := true
    for b in binders do
      let bd ← binderDoc b
      d := d ++ (if first then .space else .group (.line)) ++ bd
      first := false
    match ti with
    | some (term, colonType, _, multi) =>
      if multi then return .nest cont (d ++ .space ++ colonType)
      else return .nest cont (d ++ .group (.line ++ .text ": " ++ term))
    | none => return .nest cont d
  | .oneLine =>
    let mut bdoc : Doc := .nil
    let mut bwidth := 0
    for b in binders do
      let bd ← binderDoc b
      bdoc := bdoc ++ .space ++ bd
      bwidth := bwidth + 1 + (Lean4Fmt.Doc.flatWidth bd).getD 0
    match ti with
    | some (term, colonType, typeWidth, multi) =>
      if multi then return bdoc ++ .space ++ colonType
      if prefixWidth + bwidth + 3 + typeWidth + reserve ≤ w then
        return bdoc ++ .text " : " ++ term                             -- inline
      else
        return bdoc ++ .text " :" ++ .nest cont (.hardline ++ term)    -- break after colon
    | none => return bdoc

/-- Value kinds we actively lay out even when they span multiple lines (their own
    `walk` produces a width-aware breaking `group`). Everything else keeps the
    conservative verbatim-span path. Grows as constructs are ported. -/
private def isActiveMultiline
            (kind : SyntaxNodeKind)
            : Bool :=

  kind.toString == "termIfThenElse" || kind.toString == "termDepIfThenElse"
      || kind == ``Lean.Parser.Term.app
      || kind == ``Lean.Parser.Term.anonymousCtor
      || kind == ``Lean.Parser.Term.fun
      || kind == ``Lean.Parser.Term.tuple
      || kind == ``Lean.Parser.Term.structInst
      || kind.toString == "«term[_]»"
      || kind == ``Lean.Parser.Term.let
      || kind == ``Lean.Parser.Term.match
      || Lean4Fmt.Syntax.isBinOp kind

/-- How a definition value is to be placed. `span` is a whole `:= …` reproduced
    verbatim (where/termination/multi-line-opaque cases — the `:=` is inside it).
    `body` is the value BODY alone (no `:=`), which the caller joins to `:=`;
    `glue` means keep it on the `:=` line (a `do` block, compactDo). `eqns` is an
    equation-style value (`| pat => body` arms, no `:=`) already laid out one arm
    per line; the caller places it under the signature at indent 2. -/
private inductive ValForm
  | span (doc : Doc)
  | body (doc : Doc) (glue : Bool)
  | eqns (arms : Doc)

/-- Classify a `declVal` into a `ValForm` (see above). Splitting the `:=` from the
    body lets the caller choose the separator: inline ` := `, or (bodyOwnLine)
    `:=` then a blank then the body on its own indented line. -/
private def valForm
            (walk : Lean4Fmt.Emit.Walk)
            (declVal : Lean.Syntax)
            : EmitM ValForm := do
  if declVal.getKind == ``Lean.Parser.Command.declValSimple then
    let a := declVal.getArgs
    let hasSuffix := (a[2]?.map (fun s => !(bareSrc s).trimAscii.toString.isEmpty)).getD false
    let hasWhere := (a[3]?.map (fun s => !s.getArgs.isEmpty)).getD false
    match a[1]? with
    | some v =>
      if hasSuffix || hasWhere then return .span (← verbatim declVal)
      let vdoc ← walk v
      -- `:= do` glues even when the do carries comments BETWEEN its statements —
      -- DoNotation places statement leading/trailing trivia structurally. A do
      -- with a comment INSIDE a statement still lands here with a multi-line
      -- opaque block in vdoc (a line comment runs to end-of-line, so its
      -- statement is multi-line → verbatim), falling through to the safe span.
      if (v.getKind == ``Lean.Parser.Term.do || v.getKind == ``Lean.Parser.Term.byTactic)
          && !Lean4Fmt.Doc.hasMultilineVerbatim vdoc then
        return .body vdoc true    -- glue `:= do` / `:= by`
      -- Comment hazard: a line comment anywhere in the value except its tail
      -- token's trailing (that one sits in the inter-form gap, placed byte-exact
      -- by Module) has no seam to survive at in an active layout — in particular
      -- the flat-body path would silently drop a comment between `:=` and a
      -- single-line value. Keep the whole `:= …` span.
      let tailCmts := Lean4Fmt.Syntax.countLineComments
        ((Lean4Fmt.Syntax.trailing? v).getD "")
      if Lean4Fmt.Syntax.countSubtreeLineComments v > tailCmts then
        return .span (← verbatim declVal)
      let clean := !Lean4Fmt.Doc.hasMultilineVerbatim vdoc   -- comments handled above
      if isActiveMultiline v.getKind && clean then return .body vdoc false
      match Lean4Fmt.Doc.flatWidth vdoc with
      | some _ => return .body (.flatten vdoc) false                                 -- dense flat body
      | none => return .span (← verbatim declVal)                                    -- multi-line: safe span
    | none => return .span (← verbatim declVal)
  else if declVal.getKind == ``Lean.Parser.Command.declValEqns then
    -- `| pat => body` equation arms. Structure:
    --   declValEqns[ matchAltsWhereDecls[ matchAlts[ null[matchAlt…] ], term?, where? ] ]
    -- Lay each arm on its own line (`| pat =>` + width-aware body after `=>`),
    -- mirroring the `match` arm layout. Guarded: a line comment anywhere, a
    -- `where`/`termination_by` suffix, or a structural surprise falls back to the
    -- safe verbatim span (the gate would otherwise trip on it).
    if Lean4Fmt.Syntax.subtreeHasLineComment declVal then return .span (← verbatim declVal)
    let mawd := (declVal.getArgs[0]?).getD .missing
    let margs := mawd.getArgs
    let hasSuffix := (margs.toList.drop 1).any (fun s =>
      !(bareSrc s).trimAscii.toString.isEmpty)
    if hasSuffix then return .span (← verbatim declVal)
    let altsNode := (margs[0]?).getD .missing
    let mut alts : Array Lean.Syntax := #[]
    for g in altsNode.getArgs do
      for c in g.getArgs do
        if c.getKind == ``Lean.Parser.Term.matchAlt then alts := alts.push c
    if alts.isEmpty then return .span (← verbatim declVal)
    let mut armsDoc : Doc := .nil
    let mut first := true
    let mut aligned : Array (Doc × Option Doc) := #[]
    for alt in alts do
      let aa := alt.getArgs
      let patDoc ← walk (aa[1]?.getD .missing)
      let body := aa[aa.size-1]?.getD .missing
      let bodyDoc ← walk body
      -- a `do` body glues to the `=>` (its statements bring their own hardline);
      -- anything else is width-aware after the `=>`
      let bodyPart : Doc := if body.getKind == ``Lean.Parser.Term.do
        then .text " " ++ bodyDoc
        else .group (.nest 2 (.line ++ bodyDoc))
      let armDoc := .text "| " ++ patDoc ++ .text " =>" ++ bodyPart
      armsDoc := armsDoc ++ (if first then .nil else .hardline) ++ armDoc
      first := false
      let inlineOk := body.getKind != ``Lean.Parser.Term.do
        && !Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc
      aligned := aligned.push (patDoc, if inlineOk then some bodyDoc else none)
    let al := (← read).alignment
    return .eqns (armsAligned al.matchArms al.maxDelta aligned armsDoc)
  else
    return .span (← verbatim declVal)   -- where-struct: literal span

/-- Flat width the value contributes to the `:= …` line (`none` if it can't be one
    line). span includes `:=` (+1 for the leading space); body adds ` := ` (4). -/
private def ValForm.flatWidth : ValForm → Option Nat
  | .span d => (Lean4Fmt.Doc.flatWidth d).map (· + 1)
  | .body d _ => (Lean4Fmt.Doc.flatWidth d).map (· + 4)
  | .eqns _ => none

/-- Format the inner definition node `[kw, declId, sig, declVal, …]`. `modsWidth`
    is the inline width the modifiers add to the keyword's line.

    One-liner exemption (chosen policy): if the WHOLE declaration
    `[vis] kw name binders : type := value` fits on one line — the value is single
    line, the type is single line, and there is no line comment — it is emitted
    inline regardless of the binder-layout knob (so a short def does not explode
    into onePerLine). Otherwise the signature breaks per the knob and the value is
    laid out by `valDoc`. (Any doc-comment/attribute lines sit above and do not
    count toward the one-line budget.) -/
private def defnDoc
            (walk : Lean4Fmt.Emit.Walk)
            (modsWidth : Nat)
            (defn : Lean.Syntax)
            : EmitM Doc := do
  let a := defn.getArgs
  let kw := match a[0]? with | some (.atom _ v) => v | _ => "def"
  let declId := (a[1]?.map bareSrc).getD ""
  let vf ← match a[3]? with | some v => valForm walk v | none => pure (.body .nil false)
  let nameCol := modsWidth + kw.length + 1              -- column where the declId starts
  let prefixWidth := nameCol + declId.length            -- column where binders start
  let w := (← read).layout.lineWidth
  let sigStx := a[2]?
  -- inline binder docs + flat width (for the one-line-fit check)
  let binders := ((sigStx.bind (·.getArgs[0]?)).map (·.getArgs)).getD #[]
  let mut bInline : Doc := .nil
  let mut bW := 0
  for b in binders do
    let bd ← binderDoc b
    bInline := bInline ++ .space ++ bd
    bW := bW + 1 + (Lean4Fmt.Doc.flatWidth bd).getD 0
  let ti ← match sigStx with | some s => typeInfo walk s | none => pure none
  let typeOK := match ti with | some (_, _, _, multi) => !multi | none => true
  let typeW := match ti with | some (_, _, tw, false) => 3 + tw | _ => 0
  -- Equation-style value: the signature stays inline when it fits (matching the
  -- source shape), else breaks per the binder knob; the arms then hang on their
  -- own lines at indent 2. There is never a one-liner form for eqns.
  match vf with
  | .eqns arms =>
    -- An arm body reproduced as a multi-line opaque block (e.g. a not-yet-ported
    -- `structInst`) re-anchors by column, which drifts under active layout and is
    -- non-idempotent. Fall back to whole-`defn` verbatim (modifiers still active).
    if Lean4Fmt.Doc.hasMultilineVerbatim arms then return (← verbatim defn)
    let sigDocFinal ←
      if typeOK && prefixWidth + bW + typeW ≤ w then
        let typeInline : Doc := match ti with | some (term, _, _, false) => .text " : " ++ term | _ => .nil
        pure (bInline ++ typeInline)
      else
        match sigStx with | some s => sigDoc walk nameCol prefixWidth 0 s | none => pure .nil
    return .text kw ++ .space ++ .text declId ++ sigDocFinal ++ .nest 2 (.hardline ++ arms)
  | _ => pure ()
  let vFlat := vf.flatWidth
  let noComment := !Lean4Fmt.Syntax.subtreeHasLineComment defn
  let total := prefixWidth + bW + typeW + (vFlat.getD 1000000)
  -- inline form of the value (` := body`, or the span reproduced flat)
  let valInline : Doc := match vf with
    | .span d => .space ++ .flatten d
    | .body d _ => .text " := " ++ .flatten d
    | .eqns _ => .nil     -- unreachable: eqns returned above
  if noComment && vFlat.isSome && typeOK && total ≤ w then
    let typeInline : Doc := match ti with | some (term, _, _, false) => .text " : " ++ term | _ => .nil
    return .text kw ++ .space ++ .text declId ++ bInline ++ typeInline ++ valInline
  else
    -- broken value placement per the bodyOwnLine knob (skipped for span / glued do)
    let bodyOwnLine := (← read).breaking.bodyOwnLine
    let valBroken : Doc := match vf with
      | .span d => .space ++ d
      | .body d glue =>
        if glue then .text " := " ++ d
        else if bodyOwnLine then .text " :=" ++ .nest 2 (.blank 1 ++ d)
        else .text " :=" ++ .group (.nest 2 (.line ++ d))
      | .eqns _ => .nil     -- unreachable: eqns returned above
    let reserve := (Lean4Fmt.Doc.firstLineWidth valBroken).1
    let sig ← match sigStx with | some s => sigDoc walk nameCol prefixWidth reserve s | none => pure .nil
    return .text kw ++ .space ++ .text declId ++ sig ++ valBroken

/-- True when a line comment hides in the modifiers REGION: in trivia between the
    region's tokens (e.g. between the doc comment and a visibility keyword), or in
    the gap between the last modifier and the declaration keyword. `modifiersDoc`
    reflows the modifiers from bare token text, which would silently drop such a
    comment — the caller reproduces the whole declaration verbatim instead. Two
    exemptions: the first token's LEADING trivia (the declaration's outer leading —
    comments above the decl — placed byte-exact by `Module`), and docstring TEXT
    (`--` inside `/-- … -/` is token content, not a trivia comment). -/
private def modifiersCommentHazard
            (m defn : Lean.Syntax)
            : Bool := Id.run do
  let mut seenTokens := false
  for c in m.getArgs do
    if seenTokens then
      if Lean4Fmt.Syntax.subtreeHasLineComment c then return true
    else if !(bareSrc c).isEmpty then
      seenTokens := true
      -- the docComment slot is a null WRAPPER around the docComment node, and
      -- docstring text starts with `/--` — which contains `--` — so the bare-text
      -- check must exempt it (its interior holds no trivia anyway)
      let isDocWrap := c.getKind == ``Lean.Parser.Command.docComment
        || (c.getArgs[0]?.map (·.getKind == ``Lean.Parser.Command.docComment)).getD false
      if !isDocWrap && Lean4Fmt.Syntax.hasLineComment (bareSrc c) then
        return true
      if Lean4Fmt.Syntax.hasLineComment ((Lean4Fmt.Syntax.trailing? c).getD "") then
        return true
  -- gap between the last modifier and the keyword = the defn head's leading;
  -- with no modifier tokens at all that gap IS the outer leading (exempt)
  return seenTokens
    && Lean4Fmt.Syntax.hasLineComment ((Lean4Fmt.Syntax.leading? defn).getD "")

/-- Emit a declaration (bare — `Module` places its leading trivia), recursing
    via `walk` where needed. Plain `:= term` defs and `| pat => body` equation
    defs are actively formatted; `where`-instance / other value forms reproduce
    whole-verbatim (their sig↔value boundary trivia is subtle — deferred). -/
def emit
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.EmitM Doc := do
  let a := stx.getArgs
  let some defn := a[1]? | return (← verbatim stx)
  let dargs := defn.getArgs
  let valKind := dargs[3]?.map (·.getKind)
  let isEqns := valKind == some ``Lean.Parser.Command.declValEqns
  let isActiveVal := valKind == some ``Lean.Parser.Command.declValSimple || isEqns
  if defn.getKind == ``Lean.Parser.Command.inductive
      || defn.getKind == ``Lean.Parser.Command.structure then
    -- `where`-style inductive: modifiers as usual, head + one ctor per line at
    -- +2 (Command.inductiveDoc?). Ctor doc comments ride byte-exact; inter-ctor
    -- line comments and blank groups place structurally (the ctor loop owns
    -- those seams). A comment in the modifiers region, inside a ctor, or in a
    -- zone with no seam (the `where` line, a multi-line head) falls back to
    -- whole-declaration verbatim, as does any shape the layout can't hold.
    if (a[0]?.map (modifiersCommentHazard · defn)).getD false then
      return (← verbatim stx)
    let al := (← read).alignment
    let inner? := if defn.getKind == ``Lean.Parser.Command.inductive
      then Command.inductiveDoc? defn al.trailingComments al.maxDelta
      else Command.structureDoc? defn al.trailingComments al.structFields al.maxDelta
    match inner? with
    | some d =>
      let attrsOwnLine := (← read).breaking.attributesOwnLine
      let (modsDoc, _) := match a[0]? with
        | some m => modifiersDoc attrsOwnLine m
        | none => (.nil, 0)
      return modsDoc ++ d
    | none => return (← verbatim stx)
  if !isDefShape defn.getKind || !isActiveVal then
    return (← verbatim stx)     -- structure/instance/where: reproduce
  if isEqns && !eqnsFormattable (dargs[3]?.getD .missing) then
    return (← verbatim stx)     -- comment/where/termination-bearing eqns: whole-decl verbatim
  if (a[0]?.map (modifiersCommentHazard · defn)).getD false then
    return (← verbatim stx)     -- comment hiding in the modifiers region: whole-decl verbatim
  let attrsOwnLine := (← read).breaking.attributesOwnLine
  let (modsDoc, modsWidth) := match a[0]? with
    | some m => modifiersDoc attrsOwnLine m
    | none => (.nil, 0)
  return modsDoc ++ (← defnDoc walk modsWidth defn)

end Lean4Fmt.Emit.Decl
