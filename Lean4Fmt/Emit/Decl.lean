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
import Lean4Fmt.Emit.Tokens
import Lean4Fmt.Emit.Binders
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
  -- comments handle per-seam in the arm loop (between-arm comments place
  -- structurally; an arm-INTERIOR comment falls back there). One zone stays
  -- whole-declaration verbatim: declVal's HEAD leading (a comment between the
  -- signature and the first arm) — every fallback in the loop is a `.span`,
  -- and the span's bare source EXCLUDES that leading, so a span bail there
  -- would silently drop the comment (found exactly that way).
  if Lean4Fmt.Syntax.hasLineComment ((Lean4Fmt.Syntax.leading? declVal).getD "") then
    return false
  let mawd := (declVal.getArgs[0]?).getD .missing
  let margs := mawd.getArgs
  if (margs.toList.drop 1).any (fun s => !(bareSrc s).trimAscii.toString.isEmpty) then
    return false
  let altsNode := (margs[0]?).getD .missing
  let mut alts : Array Lean.Syntax := #[]
  for g in altsNode.getArgs do
    for c in g.getArgs do
      if c.getKind == ``Lean.Parser.Term.matchAlt then alts := alts.push c
  if alts.isEmpty then return false
  -- the per-arm seam conditions, mirrored from the valForm loop: any bail
  -- there can only `.span`, and an eqns span under a reformatted signature
  -- re-anchors wrongly (there is no `:=` seam) — so anything the loop cannot
  -- hold must be decided HERE, where the fallback is whole-decl verbatim
  for h : i in [0:alts.size] do
    let alt := alts[i]
    if Lean4Fmt.Syntax.interiorHasLineComment alt then return false
    let lead := (Lean4Fmt.Syntax.leading? alt).getD ""
    let isWs (l : String) : Bool := l.all (fun c => c == ' ' || c == '\t')
    if !isWs ((lead.splitOn "\n").headD "") then return false
    let trailT := ((Lean4Fmt.Syntax.trailing? alt).getD "").trimAscii.toString
    if i + 1 < alts.size && trailT.any (· == '\n') then return false
  return true

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
      let colonType ← verbatimQuiet ts   -- probe: logged only if the span is TAKEN
      -- wide types are ACTIVE now: commaGroups carry fillSep pools (§5), so a
      -- byte table reflows as a packed fill instead of exploding one-per-line
      if Lean4Fmt.Doc.hasMultilineVerbatim term then
        logOptOut ts
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
      d := d ++ .hardline ++ (← Lean4Fmt.Emit.binderDoc walk b)
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
      let bd ← Lean4Fmt.Emit.binderDoc walk b
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
      let bd ← Lean4Fmt.Emit.binderDoc walk b
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
      || kind.toString == "«term#[_,]»"
      || kind == ``Lean.Parser.Term.forall
      || kind == ``Lean.Parser.Term.arrow
      || kind == ``Lean.Parser.Term.paren
      || kind == ``Lean.Parser.Term.let
      || kind == ``Lean.Parser.Term.letrec
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

/-- `bodyOwnLine` for GLUED bodies (`:= do` / `:= by`): the blank goes after
    the keyword, before the block. The block's own leading separator collapses
    into the blank (renderer pend accumulation), so exactly one blank line
    appears — the same rhythm term bodies get after `:=`. -/
private def glueBodyBlank : Doc → Doc
  -- width-aware single-tactic body (`by rfl` shape): the group's leading
  -- `.line` must be REPLACED by the blank, not preceded by it — a flat-decided
  -- group after a pending blank renders the line's space after the indent
  -- flush (a spurious column; caught as an idempotence failure)
  | .cat kw (.group (.nest n (.cat .line rest))) => .cat kw (.nest n (.cat (.blank 1) rest))
  | .cat kw rest => .cat kw (.cat (.blank 1) rest)
  | d => d

/-- `bodyOwnLine` for VERBATIM value spans: when the span's first line is
    exactly `:=` / `:= by` / `:= do`, split that keyword line off the opaque
    block and put the body blank between — the body itself stays byte-exact
    (base 0: top-level lines keep their absolute indent). Without this, a decl
    whose body carries unported constructs would silently lose the rhythm the
    active path imposes ("blank when the tactics are simple, none when they
    aren't"). Idempotent: the injected blank is a leading blank line of the
    block on the next pass, and wrBlock drops those. -/
private def spanBodyBlank (bodyOwnLine : Bool) (declVal : Lean.Syntax) : ValForm → ValForm
  | .span d => Id.run do
    if !bodyOwnLine then return .span d
    match (bareSrc declVal).splitOn "\n" with
    | first :: rest =>
      let ft := first.trimAsciiEnd.toString
      if (ft == ":=" || ft == ":= by" || ft == ":= do") && !rest.isEmpty then
        return .span (.text ft ++ .blank 1 ++ .verbatim (String.intercalate "\n" rest) 0)
      return .span d
    | _ => return .span d
  | vf => vf

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
      if hasSuffix || hasWhere then
        -- value active, `termination_by …` / `where …` as own-line verbatim
        -- blocks below it, their leading trivia placed structurally. The value
        -- must be comment-free and single-line-leaf-clean (same rules as the
        -- plain body path); anything else keeps the whole safe span.
        let tailCmts := Lean4Fmt.Syntax.countLineComments
          ((Lean4Fmt.Syntax.trailing? v).getD "")
        let leadCmts := Lean4Fmt.Syntax.countLineComments
          ((Lean4Fmt.Syntax.leading? v).getD "")
        if (if Lean4Fmt.Syntax.ownsSeams v.getKind then leadCmts > 0
            else Lean4Fmt.Syntax.countSubtreeLineComments v > tailCmts) then
          return .span (← verbatim declVal)
        let vdoc ← walk v
        if Lean4Fmt.Doc.hasMultilineVerbatim vdoc then return .span (← verbatim declVal)
        let mut tail : Doc := .nil
        for slot in [a[2]?, a[3]?] do
          match slot with
          | some sfx =>
            if (bareSrc sfx).trimAscii.toString.isEmpty then continue
            let some sep := Lean4Fmt.Emit.leadingSep? ((Lean4Fmt.Syntax.leading? sfx).getD "")
              | return .span (← verbatim declVal)
            tail := tail ++ sep ++ (← verbatim sfx)
          | none => continue
        let glue := v.getKind == ``Lean.Parser.Term.do || v.getKind == ``Lean.Parser.Term.byTactic
        return .body (vdoc ++ tail) glue
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
      -- EXEMPT seam-owning kinds (Kinds.ownsSeams) — but only for comments
      -- INSIDE their seams: the value's own HEAD leading (between `:=` and
      -- the first token) has no owner in expression space, so it keeps the
      -- span (which carries it byte-exact)
      let leadCmts := Lean4Fmt.Syntax.countLineComments
        ((Lean4Fmt.Syntax.leading? v).getD "")
      if (if Lean4Fmt.Syntax.ownsSeams v.getKind then False
          else Lean4Fmt.Syntax.countSubtreeLineComments v > tailCmts + leadCmts) then
        return .span (← verbatim declVal)
      -- the value's HEAD-LEADING comment lines place structurally (the seam
      -- kit; T3) and force the BROKEN placement — an inline `:= -- cmt v`
      -- would be nonsense. hasMultilineVerbatim still spans.
      -- CHAIN walkers (let/letrec) place their OWN leading (their head
      -- comments are chain seams) — prepending would double them; every
      -- other kind gets the seam-kit prefix (idempotence sweep verifies)
      let selfLead := v.getKind == ``Lean.Parser.Term.let
        || v.getKind == ``Lean.Parser.Term.letrec
      let vdoc ← (do
        if leadCmts > 0 && !selfLead then
          match Lean4Fmt.Emit.leadingSep? ((Lean4Fmt.Syntax.leading? v).getD "") with
          | some sep => pure (sep ++ vdoc)
          | none => pure vdoc   -- unownable shape: caught below as span
        else pure vdoc)
      if leadCmts > 0 && !selfLead
          && !(match Lean4Fmt.Emit.leadingSep?
          ((Lean4Fmt.Syntax.leading? v).getD "") with | some _ => true | none => false) then
        return .span (← verbatim declVal)
      let clean := !Lean4Fmt.Doc.hasMultilineVerbatim vdoc   -- comments handled above
      if (isActiveMultiline v.getKind || leadCmts > 0) && clean then return .body vdoc false
      match Lean4Fmt.Doc.flatWidth vdoc with
      | some _ => return .body vdoc false      -- width decides (no forced flatten)
      | none => return .span (← verbatim declVal)                                    -- multi-line: safe span
    | none => return .span (← verbatim declVal)
  else if declVal.getKind == ``Lean.Parser.Command.declValEqns then
    -- `| pat => body` equation arms. Structure:
    --   declValEqns[ matchAltsWhereDecls[ matchAlts[ null[matchAlt…] ], term?, where? ] ]
    -- Lay each arm on its own line (`| pat =>` + width-aware body after `=>`),
    -- mirroring the `match` arm layout. Guarded: a line comment anywhere, a
    -- `where`/`termination_by` suffix, or a structural surprise falls back to the
    -- safe verbatim span (the gate would otherwise trip on it).
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
    let mut armsPlain : Doc := .nil
    let mut aligned : Array (Doc × Option Doc) := #[]
    let mut plainArms := true
    for h : i in [0:alts.size] do
      let alt := alts[i]
      -- a comment INSIDE the arm — whole-declaration verbatim (via the
      -- defnDoc multiline-arms gate: the span carries it)
      if Lean4Fmt.Syntax.interiorHasLineComment alt then return .span (← verbatim declVal)
      let lead := (Lean4Fmt.Syntax.leading? alt).getD ""
      let some sep := Lean4Fmt.Emit.leadingSep? lead | return .span (← verbatim declVal)
      let plainSep := ((lead.splitOn "\n").drop 1).dropLast.isEmpty
      let trailT := ((Lean4Fmt.Syntax.trailing? alt).getD "").trimAscii.toString
      let last := i + 1 == alts.size
      if !last && trailT.any (· == '\n') then return .span (← verbatim declVal)
      let trailDoc : Doc := if !last && !trailT.isEmpty then .text (" " ++ trailT) else .nil
      if !plainSep || (!last && !trailT.isEmpty) then plainArms := false
      let aa := alt.getArgs
      let patDoc ← walk (aa[1]?.getD .missing)
      let body := aa[aa.size-1]?.getD .missing
      let bodyDoc ← walk body
      -- a `do` body glues to the `=>` (its statements bring their own hardline);
      -- anything else is width-aware after the `=>`
      let srcBroken := ((Lean4Fmt.Syntax.leading? body).getD "").any (· == '\n')
      let preserveLB := (← read).breaking.preserveLineBreaks
      let bodyPart : Doc := if body.getKind == ``Lean.Parser.Term.do
        then .text " " ++ bodyDoc
        else if preserveLB then
          if srcBroken then Doc.nest 2 (Doc.hardline ++ bodyDoc)
          else Doc.text " " ++ bodyDoc
        else .group (.nest 2 (.line ++ bodyDoc))
      -- preserve mode: a single-line arm is byte-exact (hand-padded `=>`
      -- columns survive)
      let armSrc := (bareSrc alt).trimAscii.toString
      let armDoc :=
        if preserveLB && !armSrc.isEmpty
            && !armSrc.any (· == '\n') then
          Doc.text armSrc
        else .text "| " ++ patDoc ++ .text " =>" ++ bodyPart
      armsDoc := armsDoc ++ sep ++ armDoc ++ trailDoc
      armsPlain := armsPlain ++ (if i == 0 then Doc.nil else .hardline) ++ armDoc
      let inlineOk := body.getKind != ``Lean.Parser.Term.do
        && !Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc
      aligned := aligned.push (patDoc, if inlineOk then some bodyDoc else none)
    let al := (← read).alignment
    -- the arms doc OWNS its leading break (defnDoc places it bare at +2):
    -- plain arm sets lead with a hardline; seam-led sets already start with
    -- their first arm's separator
    if plainArms then
      return .eqns (.hardline ++ armsAligned al.matchArms al.maxDelta aligned armsPlain)
    return .eqns armsDoc
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
  let bodyOwn := (← read).breaking.bodyOwnLine
  let vf := match a[3]? with
    | some v => spanBodyBlank bodyOwn v vf
    | none => vf
  let nameCol := modsWidth + kw.length + 1              -- column where the declId starts
  let prefixWidth := nameCol + declId.length            -- column where binders start
  let w := (← read).layout.lineWidth
  let sigStx := a[2]?
  -- inline binder docs + flat width (for the one-line-fit check)
  let binders := ((sigStx.bind (·.getArgs[0]?)).map (·.getArgs)).getD #[]
  let mut bInline : Doc := .nil
  let mut bW := 0
  for b in binders do
    let bd ← Lean4Fmt.Emit.binderDoc walk b
    bInline := bInline ++ .space ++ bd
    bW := bW + 1 + (Lean4Fmt.Doc.flatWidth bd).getD 0
  let ti ← match sigStx with | some s => typeInfo walk s | none => pure none
  let typeOK := match ti with | some (_, _, _, multi) => !multi | none => true
  let typeW := match ti with | some (_, _, tw, false) => 3 + tw | _ => 0
  -- preserve mode: a single-line signature rides byte-exact (authors are
  -- inconsistent about `): T` vs `) : T` — no synthesized rule round-trips);
  -- the declId↔sig gap comes from the source too (`name: T` stays glued)
  let preserve := (← read).spacing.preserveBinders
  let preserveLB := (← read).breaking.preserveLineBreaks
  let sigGap := if ((a[1]?.bind Lean4Fmt.Syntax.trailing?).getD " ").isEmpty then "" else " "
  let sigExact? : Option String := Id.run do
    if !preserve then return none
    let some ss := sigStx | return some ""
    let t := (bareSrc ss).trimAscii.toString
    if t.isEmpty then return some ""
    if t.any (· == '\n') then return none
    if Lean4Fmt.Syntax.countSubtreeLineComments ss > 0 then return none
    return some t
  -- preserve + multi-line signature: the author's sig breaks are not held by
  -- the active layout — whole-decl byte-exact
  if preserve && sigExact?.isNone then return (← verbatim defn)
  let (sigInline, sigW, typeW, typeOK) := match sigExact? with
    | some t =>
      if t.isEmpty then ((.nil : Doc), 0, 0, true)
      else ((.text (sigGap ++ t) : Doc), sigGap.length + t.length, 0, true)
    | none => (bInline, bW, typeW, typeOK)
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
      if typeOK && prefixWidth + sigW + typeW ≤ w then
        let typeInline : Doc :=
          if sigExact?.isSome then .nil
          else match ti with | some (term, _, _, false) => .text " : " ++ term | _ => .nil
        pure (sigInline ++ typeInline)
      else
        match sigStx with | some s => sigDoc walk nameCol prefixWidth 0 s | none => pure .nil
    return .text kw ++ .space ++ .text declId ++ sigDocFinal ++ .nest 2 arms
  | _ => pure ()
  let vFlat := vf.flatWidth
  -- preserve: the gap before `:=` comes from the source (`TestSeq:= runTest`
  -- keeps its glued form); spaces only — anything else falls to the default
  let eqGapL :=
    if preserveLB then
      let g := ((sigStx.bind Lean4Fmt.Syntax.lastTokenTrailing?).getD
        (((a[1]?.bind Lean4Fmt.Syntax.trailing?)).getD " "))
      if g.toList.all (· == ' ') then g else " "
    else " "
  let noComment := !Lean4Fmt.Syntax.interiorHasLineComment defn
  let total := prefixWidth + sigW + typeW + (vFlat.getD 1000000)
  -- inline form of the value (` := body`, or the span reproduced flat)
  let valInline : Doc := match vf with
    | .span d => .text eqGapL ++ .flatten d
    | .body d _ => .text (eqGapL ++ ":= ") ++ .flatten d
    | .eqns _ => .nil     -- unreachable: eqns returned above
  let alwaysBreak := (← read).breaking.bodyAlwaysBreak
  -- source's `:=`-line decision (preserveLineBreaks: it is load-bearing)
  let srcValBroken := ((a[3]?.bind (·.getArgs[1]?)).map
    (fun v => ((Lean4Fmt.Syntax.leading? v).getD "").any (· == '\n'))).getD false
  let inlineOk :=
    if preserveLB then noComment && vFlat.isSome && typeOK && !srcValBroken && !alwaysBreak
    else noComment && vFlat.isSome && typeOK && total ≤ w && !alwaysBreak
  if inlineOk then
    let typeInline : Doc :=
      if sigExact?.isSome then .nil
      else match ti with | some (term, _, _, false) => .text " : " ++ term | _ => .nil
    return .text kw ++ .space ++ .text declId ++ sigInline ++ typeInline ++ valInline
  else
    -- broken value placement per the bodyOwnLine knob (skipped for span / glued do)
    let bodyOwnLine := (← read).breaking.bodyOwnLine
    let valBroken : Doc := match vf with
      | .span d => .text eqGapL ++ d
      | .body d glue =>
        if glue then
          .text (eqGapL ++ ":= ") ++ (if bodyOwnLine then glueBodyBlank d else d)
        else if bodyOwnLine then .text (eqGapL ++ ":=") ++ .nest 2 (.blank 1 ++ d)
        else if alwaysBreak || preserveLB then
          .text (eqGapL ++ ":=") ++ .nest 2 (.hardline ++ d)
        else .text (eqGapL ++ ":=") ++ .group (.nest 2 (.line ++ d))
      | .eqns _ => .nil     -- unreachable: eqns returned above
    let reserve := (Lean4Fmt.Doc.firstLineWidth valBroken).1
    let sig ← match sigExact? with
      | some _ =>
        if preserveLB || prefixWidth + sigW + reserve ≤ w then pure sigInline
        else match sigStx with | some s => sigDoc walk nameCol prefixWidth reserve s | none => pure .nil
      | none =>
        match sigStx with | some s => sigDoc walk nameCol prefixWidth reserve s | none => pure .nil
    return .text kw ++ .space ++ .text declId ++ sig ++ valBroken

/-- One `where`-instance field `name (binders)* := value` — the lval and
    binders token-for-token, the VALUE walked (flat on the `:=` line when it
    fits, else next line at +2; `do`/`by` glue). `none` on a multi-line head
    piece, a value carrying a multi-line opaque block, or a structural
    surprise. -/
private def whereFieldDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (f : Lean.Syntax)
            : EmitM (Option Doc) := do
  if f.getKind != ``Lean.Parser.Term.structInstField then return none
  if (← read).breaking.preserveLineBreaks then
    let t := (bareSrc f).trimAscii.toString
    if !t.isEmpty && !t.any (· == '\n')
        && !Lean4Fmt.Syntax.interiorHasLineComment f then
      return some (.text t)
  let fa := f.getArgs
  if fa.size != 2 then return none
  let lvalT := (bareSrc fa[0]!).trimAscii.toString
  if lvalT.isEmpty || lvalT.any (· == '\n') then return none
  let rest := fa[1]!.getArgs
  let mut head := lvalT
  let mut fd : Option Lean.Syntax := none
  for c in rest do
    if c.getKind == ``Lean.Parser.Term.structInstFieldDef then fd := some c
    else
      let t := (bareSrc c).trimAscii.toString
      if t.any (· == '\n') then return none
      if !t.isEmpty then head := head ++ " " ++ t
  let some fdef := fd | return none
  let da := fdef.getArgs
  let some v := da[da.size - 1]? | return none
  let vdoc ← walk v
  if Lean4Fmt.Doc.hasMultilineVerbatim vdoc then return none
  if v.getKind == ``Lean.Parser.Term.do || v.getKind == ``Lean.Parser.Term.byTactic then
    return some (.text (head ++ " := ") ++ vdoc)
  return some (.text head ++ .text " :=" ++ .group (.nest 2 (.line ++ vdoc)))

/-- `<head> := value` placement shared by instance/example heads: inline when
    it fits, else per the bodyOwnLine knob (glued do/by keep the keyword on the
    `:=` line, blank after it). -/
private def headValDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (head : String)
            (declVal : Lean.Syntax)
            : EmitM (Option Doc) := do
  let w := (← read).layout.lineWidth
  let bodyOwnLine := (← read).breaking.bodyOwnLine
  let alwaysBreak := (← read).breaking.bodyAlwaysBreak
  match spanBodyBlank bodyOwnLine declVal (← valForm walk declVal) with
  | .span d => return some (.text head ++ .space ++ d)
  | .body d glue =>
    match Lean4Fmt.Doc.flatWidth d with
    | some fw =>
      if head.length + 4 + fw ≤ w && !alwaysBreak && !glue then
        return some (.text head ++ .text " := " ++ .flatten d)
      else if glue && head.length + 4 + fw ≤ w && !alwaysBreak then
        return some (.text head ++ .text " := " ++ .flatten d)
      else if glue then
        return some (.text head ++ .text " := "
          ++ (if bodyOwnLine then glueBodyBlank d else d))
      else if bodyOwnLine then
        return some (.text head ++ .text " :=" ++ .nest 2 (.blank 1 ++ d))
      else if alwaysBreak then
        return some (.text head ++ .text " :=" ++ .nest 2 (.hardline ++ d))
      else return some (.text head ++ .text " :=" ++ .group (.nest 2 (.line ++ d)))
    | none =>
      if glue then
        return some (.text head ++ .text " := "
          ++ (if bodyOwnLine then glueBodyBlank d else d))
      else if bodyOwnLine then
        return some (.text head ++ .text " :=" ++ .nest 2 (.blank 1 ++ d))
      else if alwaysBreak then
        return some (.text head ++ .text " :=" ++ .nest 2 (.hardline ++ d))
      else return some (.text head ++ .text " :=" ++ .group (.nest 2 (.line ++ d)))
  | .eqns _ => return none

/-- The field block of a `whereStructInst` declVal: one field per line, the
    seam loop owning inter-field trivia. The caller prepends `<head> where`
    and nests. -/
private def whereBodyDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (declVal : Lean.Syntax)
            : EmitM (Option Doc) := do
  let wa := declVal.getArgs
  if wa.size != 3 then return none
  if !((wa[2]?.map bareSrc).getD "").trimAscii.toString.isEmpty then return none
  if !((Lean4Fmt.Syntax.trailing? wa[0]!).getD "").trimAscii.toString.isEmpty then return none
  let fields := ((wa[1]?.bind (·.getArgs[0]?)).map (·.getArgs)).getD #[]
  let mut body : Doc := .nil
  let mut n := 0
  for h : i in [0:fields.size] do
    let f := fields[i]
    if (bareSrc f).trimAscii.toString.isEmpty then continue  -- separator slot
    if f.isAtom then return none
    if Lean4Fmt.Syntax.interiorHasLineComment f then return none
    n := n + 1
    let trailT := ((Lean4Fmt.Syntax.trailing? f).getD "").trimAscii.toString
    let last := i + 1 == fields.size
    if !last && trailT.any (· == '\n') then return none
    let trailDoc : Doc := if !last && !trailT.isEmpty then .text (" " ++ trailT) else .nil
    let some sep := Lean4Fmt.Emit.leadingSep? ((Lean4Fmt.Syntax.leading? f).getD "")
      | return none
    let some d ← whereFieldDoc? walk f | return none
    body := body ++ sep ++ d ++ trailDoc
  if n == 0 then return none
  return some body

/-- `def name <sig> where <fields>` (the codegen Func-where pattern): head
    tokens single-line, fields via the where machinery. -/
private def defWhereDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (defn : Lean.Syntax)
            : EmitM (Option Doc) := do
  let dargs := defn.getArgs
  if dargs.size < 4 then return none
  let mut head := ""
  for c in dargs.extract 0 3 do
    if Lean4Fmt.Syntax.countSubtreeLineComments c > 0 then return none
    let t := Lean4Fmt.Emit.canonTok c
    if t.any (· == '\n') then return none
    if !t.isEmpty then head := if head.isEmpty then t else head ++ " " ++ t
  if head.isEmpty then return none
  if head.length + 6 > (← read).layout.lineWidth then return none
  match ← whereBodyDoc? walk dargs[3]! with
  | some body => return some (.text (head ++ " where") ++ .nest 2 body)
  | none => return none

/-- `example <sig> := value`: keyword + signature single-line, the value via
    the shared head-value placement. -/
private def exampleDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (defn : Lean.Syntax)
            : EmitM (Option Doc) := do
  let dargs := defn.getArgs
  if dargs.size != 3 then return none
  let mut head := ""
  for c in dargs.extract 0 2 do
    if Lean4Fmt.Syntax.countSubtreeLineComments c > 0 then return none
    let t := Lean4Fmt.Emit.canonTok c
    -- flatten-first: a multi-line signature's canonical one-line spelling
    let wLim := (← read).layout.lineWidth
    let t := if t.any (· == '\n') then
        match Lean4Fmt.Emit.tokenJoinFlat? c with
        | some ft => if ft.length + 16 ≤ wLim then ft else t
        | none => t
      else t
    if t.any (· == '\n') then return none
    if !t.isEmpty then head := if head.isEmpty then t else head ++ " " ++ t
  if head.isEmpty then return none
  if dargs[2]!.getKind != ``Lean.Parser.Command.declValSimple then return none
  headValDoc? walk head dargs[2]!

/-- Value placement behind a Doc-valued (already multi-line) head: no inline
    path — the value glues or breaks per the knobs. -/
private def docHeadValDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (hd : Doc)
            (declVal : Lean.Syntax)
            : EmitM (Option Doc) := do
  let bodyOwnLine := (← read).breaking.bodyOwnLine
  match spanBodyBlank bodyOwnLine declVal (← valForm walk declVal) with
  | .span d => return some (hd ++ .text " " ++ d)
  | .body d glue =>
    if glue then
      return some (hd ++ .text " := " ++ (if bodyOwnLine then glueBodyBlank d else d))
    else if bodyOwnLine then return some (hd ++ .text " :=" ++ .nest 2 (.blank 1 ++ d))
    else return some (hd ++ .text " :=" ++ .nest 2 (.hardline ++ d))
  | .eqns _ => return none

/-- An `example` whose signature cannot flatten: binders via the kit, the
    TYPE walked at the continuation, value behind the Doc head. -/
private def exampleWalkedDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (defn : Lean.Syntax)
            : EmitM (Option Doc) := do
  let dargs := defn.getArgs
  if dargs.size != 3 then return none
  if Lean4Fmt.Syntax.interiorHasLineComment defn then return none
  if dargs[2]!.getKind != ``Lean.Parser.Command.declValSimple then return none
  let sa := dargs[1]!.getArgs
  if sa.size < 2 then return none
  let mut hd : Doc := .text ((bareSrc dargs[0]!).trimAscii.toString)
  for b in ((sa[0]?).map (·.getArgs)).getD #[] do
    let bd ← Lean4Fmt.Emit.binderDoc walk b
    if Lean4Fmt.Doc.hasMultilineVerbatim bd then return none
    hd := hd ++ .space ++ bd
  let tyNode := (sa[1]?.bind (fun x =>
    if x.getKind == ``Lean.Parser.Term.typeSpec then some x else x.getArgs[0]?)).getD .missing
  if tyNode.getKind != ``Lean.Parser.Term.typeSpec then return none
  let tyDoc ← walk (tyNode.getArgs[1]?.getD .missing)
  if Lean4Fmt.Doc.hasMultilineVerbatim tyDoc then return none
  let cont := (← read).layout.continuationIndent
  docHeadValDoc? walk
    (hd ++ .text " :" ++ .group (.nest cont (.line ++ tyDoc))) dargs[2]!

/-- Fallback for an `example` whose SIGNATURE spans lines (quasiquote types):
    the keyword rides active, everything from the signature on is ONE
    re-anchored span — the decl participates in module structure (blank
    rhythm) while its interior stays byte-exact. -/
private def exampleSpanDoc?
            (defn : Lean.Syntax)
            : EmitM (Option Doc) := do
  let dargs := defn.getArgs
  if dargs.size != 3 then return none
  let kwT := (bareSrc dargs[0]!).trimAscii.toString
  if kwT.isEmpty || kwT.any (· == '\n') then return none
  let rest := Lean.mkNullNode (dargs.extract 1 dargs.size)
  let t := bareSrc rest
  if t.isEmpty then return none
  return some (.text (kwT ++ " ") ++ (← verbatimQuiet rest) )

/-- Active layout for `instance` declarations: head on one line
    (`instance (prio)? (name)? <binders> : τ`), then `:= value` (walked, the
    same placement rules as a def) or `where` + one field per line at +2 (the
    seam loop owning inter-field trivia). Falls back to whole-declaration
    verbatim on: equation-style values, `where`-decls suffixes, comments in
    seamless zones, multi-line head pieces, or an over-wide head. -/
private def instanceDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (defn : Lean.Syntax)
            : EmitM (Option Doc) := do
  let a := defn.getArgs
  if a.size != 6 then return none
  let attrT := (bareSrc a[0]!).trimAscii.toString
  let prioT := (bareSrc a[2]!).trimAscii.toString
  let idT := (bareSrc a[3]!).trimAscii.toString
  if attrT.any (· == '\n') || prioT.any (· == '\n') || idT.any (· == '\n') then return none
  let mut head := (if attrT.isEmpty then "" else attrT ++ " ") ++ "instance"
  if !prioT.isEmpty then head := head ++ " " ++ prioT
  if !idT.isEmpty then head := head ++ " " ++ idT
  let sig := a[4]!.getArgs
  for b in ((sig[0]?).map (·.getArgs)).getD #[] do
    match Lean4Fmt.Emit.binderText? b (← read).spacing.preserveBinders with
    | some t => head := head ++ " " ++ t
    | none =>
      let t := (bareSrc b).trimAscii.toString
      if t.isEmpty || t.any (· == '\n') then return none
      head := head ++ " " ++ t
  -- a MULTI-LINE instance type walks (chains at the continuation); the head
  -- becomes a Doc and only the `where` form is supported for it
  let mut headTail : Option Doc := none
  match sig[1]? with
  | some ts =>
    let tyStx := (ts.getArgs[1]?).getD .missing
    let t := Lean4Fmt.Emit.canonTok tyStx
    if t.isEmpty then return none
    -- flatten-first: the canonical one-line spelling when it fits
    let wLim := (← read).layout.lineWidth
    let t := if t.any (· == '\n') then
        match Lean4Fmt.Emit.tokenJoinFlat? tyStx with
        | some ft => if head.length + 3 + ft.length + 6 ≤ wLim
            then ft else t
        | none => t
      else t
    if t.any (· == '\n') then
      let tyDoc ← walk tyStx
      if Lean4Fmt.Doc.hasMultilineVerbatim tyDoc then return none
      let cont := (← read).layout.continuationIndent
      headTail := some (.text " :" ++ .group (.nest cont (.line ++ tyDoc)))
    else
      head := head ++ " : " ++ t
  | none => return none
  let w := (← read).layout.lineWidth
  if headTail.isNone && head.length + 6 > w then return none
  match headTail with
  | some tail =>
    -- only `… where` supports the broken head for now
    let declVal := a[5]!
    if declVal.getKind != ``Lean.Parser.Command.whereStructInst then return none
    match ← whereBodyDoc? walk declVal with
    | some body => return some (.text head ++ tail ++ .text " where" ++ .nest 2 body)
    | none => return none
  | none => pure ()
  let declVal := a[5]!
  if declVal.getKind == ``Lean.Parser.Command.declValSimple then
    headValDoc? walk head declVal
  else if declVal.getKind == ``Lean.Parser.Command.whereStructInst then
    match ← whereBodyDoc? walk declVal with
    | some body => return some (.text (head ++ " where") ++ .nest 2 body)
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
  let preserveLB := (← read).breaking.preserveLineBreaks
  let attrsOwnLineKnob := (← read).breaking.attributesOwnLine
  -- preserve: the attrs↔keyword break comes from the source (the newline
  -- lives in the MODIFIERS node's trailing trivia)
  -- preserve: the attrs↔keyword break comes from the source. The break sits
  -- before whatever FOLLOWS the attributes — a visibility modifier
  -- (`protected`, inside the modifiers node) or the declaration keyword.
  let attrsOwnLine :=
    if preserveLB then
      let afterAttr? := (a[0]?.map (·.getArgs.toList.drop 2)).getD [] |>.findSome?
        (fun c => if (bareSrc c).isEmpty then none else Lean4Fmt.Syntax.leading? c)
      ((afterAttr?.getD ((Lean4Fmt.Syntax.leading? defn).getD ""))).any (· == '\n')
    else attrsOwnLineKnob
  let dargs := defn.getArgs
  let valKind := dargs[3]?.map (·.getKind)
  let isEqns := valKind == some ``Lean.Parser.Command.declValEqns
  let isActiveVal := valKind == some ``Lean.Parser.Command.declValSimple || isEqns
  if defn.getKind == ``Lean.Parser.Command.instance then
    if (a[0]?.map (modifiersCommentHazard · defn)).getD false then
      return (← verbatim stx)
    match ← instanceDoc? walk defn with
    | some d =>
      let (modsDoc, _) := match a[0]? with
        | some m => modifiersDoc attrsOwnLine m
        | none => (.nil, 0)
      return modsDoc ++ d
    | none => return (← verbatim stx)
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
    let inner? ← if defn.getKind == ``Lean.Parser.Command.inductive
      then Command.inductiveDoc? walk defn al.trailingComments al.maxDelta preserveLB
      else Command.structureDoc? walk defn al.trailingComments al.structFields
             al.maxDelta preserveLB
    match inner? with
    | some d =>
      let (modsDoc, _) := match a[0]? with
        | some m => modifiersDoc attrsOwnLine m
        | none => (.nil, 0)
      return modsDoc ++ d
    | none => return (← verbatim stx)
  if defn.getKind == ``Lean.Parser.Command.example then
    -- example: no declId — [kw, optDeclSig, declVal]
    if (a[0]?.map (modifiersCommentHazard · defn)).getD false then
      return (← verbatim stx)
    match ← (do match ← exampleDoc? walk defn with
                | some d => pure (some d)
                | none =>
                  match ← exampleWalkedDoc? walk defn with
                  | some d => pure (some d)
                  | none => exampleSpanDoc? defn) with
    | some d =>
      let (modsDoc, _) := match a[0]? with
        | some m => modifiersDoc attrsOwnLine m
        | none => (.nil, 0)
      return modsDoc ++ d
    | none => return (← verbatim stx)
  if isDefShape defn.getKind && valKind == some ``Lean.Parser.Command.whereStructInst then
    -- `def … where` (struct-instance value on a def)
    if (a[0]?.map (modifiersCommentHazard · defn)).getD false then
      return (← verbatim stx)
    match ← defWhereDoc? walk defn with
    | some d =>
      let (modsDoc, _) := match a[0]? with
        | some m => modifiersDoc attrsOwnLine m
        | none => (.nil, 0)
      return modsDoc ++ d
    | none => return (← verbatim stx)
  -- multi-line SIG-ONLY decls (axiom/opaque with a forall/arrow type that
  -- spans lines): kw+id active, binders via the binder kit, the type WALKED
  -- (chains lay out at the continuation)
  let sigOnlyDoc? : EmitM (Option Doc) := do
    let dargs := defn.getArgs
    if dargs.size < 3 then return none
    let kwT := (bareSrc dargs[0]!).trimAscii.toString
    let idT := (bareSrc dargs[1]!).trimAscii.toString
    if kwT.isEmpty || kwT.any (· == '\n') || idT.any (· == '\n') then return none
    for c in dargs.extract 3 dargs.size do
      if !(bareSrc c).trimAscii.toString.isEmpty then return none
    if Lean4Fmt.Syntax.interiorHasLineComment defn then return none
    let sig := dargs[2]!
    let sa := sig.getArgs
    if sa.size < 2 then return none
    let mut hd : Doc := .text (kwT ++ (if idT.isEmpty then "" else " " ++ idT))
    for b in ((sa[0]?).map (·.getArgs)).getD #[] do
      let bd ← Lean4Fmt.Emit.binderDoc walk b
      if Lean4Fmt.Doc.hasMultilineVerbatim bd then return none
      hd := hd ++ .space ++ bd
    let tyNode := (sa[1]?.bind (fun x =>
      if x.getKind == ``Lean.Parser.Term.typeSpec then some x else x.getArgs[0]?)).getD .missing
    if tyNode.getKind != ``Lean.Parser.Term.typeSpec then return none
    let tyDoc ← walk (tyNode.getArgs[1]?.getD .missing)
    if Lean4Fmt.Doc.hasMultilineVerbatim tyDoc then return none
    let cont := (← read).layout.continuationIndent
    return some (hd ++ .text " :" ++ .group (.nest cont (.line ++ tyDoc)))
  if !isDefShape defn.getKind || !isActiveVal then
    -- sig-only decls (axiom, opaque, variable …) and unported value forms:
    -- modifiers (docstring on its own line, attrs per the knob) place
    -- structurally; a SINGLE-LINE decl tail rides canonically respaced.
    -- Multi-line tails stay verbatim (the remaining task-#7 queue).
    if (a[0]?.map (modifiersCommentHazard · defn)).getD false then
      return (← verbatim stx)
    let t := bareSrc defn
    if !t.isEmpty && !t.any (· == '\n') then
      match Lean4Fmt.Emit.tokenJoin? defn with
      | some t' =>
        let (modsDoc, _) := match a[0]? with
          | some m => modifiersDoc attrsOwnLine m
          | none => (.nil, 0)
        return modsDoc ++ .text t'
      | none => return (← verbatim stx)
    match ← sigOnlyDoc? with
    | some d =>
      let (modsDoc, _) := match a[0]? with
        | some m => modifiersDoc attrsOwnLine m
        | none => (.nil, 0)
      return modsDoc ++ d
    | none => return (← verbatim stx)     -- multi-line tail: reproduce
  if isEqns && !eqnsFormattable (dargs[3]?.getD .missing) then
    return (← verbatim stx)     -- comment/where/termination-bearing eqns: whole-decl verbatim
  if (a[0]?.map (modifiersCommentHazard · defn)).getD false then
    return (← verbatim stx)     -- comment hiding in the modifiers region: whole-decl verbatim
  let (modsDoc, modsWidth) := match a[0]? with
    | some m =>
      if preserveLB && !(bareSrc m).trimAscii.toString.isEmpty then
        -- byte-exact modifiers region; the break before the keyword comes
        -- from the source (covers `@[a] protected⏎def` and every other split)
        let mSrc := (bareSrc m).trimAscii.toString
        let kwGap := ((Lean4Fmt.Syntax.leading? defn).getD " ")
        let sepD : Doc := if kwGap.any (· == '\n') then .hardline else .text " "
        if mSrc.any (· == '\n') then (Doc.verbatim mSrc 0 ++ sepD, 0)
        else (Doc.text mSrc ++ sepD,
              if kwGap.any (· == '\n') then 0 else mSrc.length + 1)
      else modifiersDoc attrsOwnLine m
    | none => (.nil, 0)
  return modsDoc ++ (← defnDoc walk modsWidth defn)

end Lean4Fmt.Emit.Decl
