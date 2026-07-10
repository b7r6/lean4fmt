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

/-- The comment block (if any) inside a trivia string: the non-whitespace-only
    lines, dedented to column 0 (so a caller can re-anchor them with
    `.verbatim … 0`). `none` when the trivia is pure whitespace. Lets onePerLine
    preserve inter-binder comments instead of dropping them (which would otherwise
    force the gate's identity fallback). -/
private def commentBlock? (trivia : String) : Option String := Id.run do
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
    term alone (no colon) and `colonTypeDoc` is the whole `: τ` byte-exact (with
    the colon). Callers use `termDoc` (adding their own `: `) when it is single
    line, and `colonTypeDoc` when it is multi-line or an unexpected shape (so the
    colon is never lost). -/
private def typeInfo
            (sig : Lean.Syntax)
            : EmitM (Option (Doc × Doc × Nat × Bool)) := do
  let a := sig.getArgs
  let tsNode : Option Lean.Syntax := a[1]?.bind (fun x =>
    if x.getKind == ``Lean.Parser.Term.typeSpec then some x else x.getArgs[0]?)
  match tsNode with
  | some ts =>
    if ts.getKind == ``Lean.Parser.Term.typeSpec then
      let term ← verbatim (ts.getArgs[1]?.getD .missing)
      let colonType ← verbatim ts
      return some (term, colonType, (Lean4Fmt.Doc.flatWidth term).getD 0,
                   Lean4Fmt.Doc.hasMultilineVerbatim term)
    else
      let ct ← verbatim ts
      return some (ct, ct, (Lean4Fmt.Doc.flatWidth ct).getD 0, true)  -- unexpected: use whole span
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
            (nameCol prefixWidth reserve : Nat)
            (sig : Lean.Syntax)
            : EmitM Doc := do
  let a := sig.getArgs
  let binders := (a[0]?.map (·.getArgs)).getD #[]
  let ti ← typeInfo sig
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
      d := d ++ .hardline ++ (← verbatim b)
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
      let bd ← verbatim b
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
      let bd ← verbatim b
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
      || kind.toString == "«term[_]»"
      || kind == ``Lean.Parser.Term.let
      || kind == ``Lean.Parser.Term.match
      || Lean4Fmt.Syntax.isBinOp kind

/-- How a definition value is to be placed. `span` is a whole `:= …` reproduced
    verbatim (where/termination/equation/multi-line-opaque cases — the `:=` is
    inside it). `body` is the value BODY alone (no `:=`), which the caller joins
    to `:=`; `glue` means keep it on the `:=` line (a `do` block, compactDo). -/
private inductive ValForm
  | span (doc : Doc)
  | body (doc : Doc) (glue : Bool)

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
      let clean := !Lean4Fmt.Syntax.subtreeHasLineComment v
        && !Lean4Fmt.Doc.hasMultilineVerbatim vdoc
      if v.getKind == ``Lean.Parser.Term.do && clean then return .body vdoc true    -- glue `:= do`
      if isActiveMultiline v.getKind && clean then return .body vdoc false
      match Lean4Fmt.Doc.flatWidth vdoc with
      | some _ => return .body (.flatten vdoc) false                                 -- dense flat body
      | none => return .span (← verbatim declVal)                                    -- multi-line: safe span
    | none => return .span (← verbatim declVal)
  else
    return .span (← verbatim declVal)   -- declValEqns / where-struct: literal span

/-- Flat width the value contributes to the `:= …` line (`none` if it can't be one
    line). span includes `:=` (+1 for the leading space); body adds ` := ` (4). -/
private def ValForm.flatWidth : ValForm → Option Nat
  | .span d => (Lean4Fmt.Doc.flatWidth d).map (· + 1)
  | .body d _ => (Lean4Fmt.Doc.flatWidth d).map (· + 4)

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
    let bd ← verbatim b
    bInline := bInline ++ .space ++ bd
    bW := bW + 1 + (Lean4Fmt.Doc.flatWidth bd).getD 0
  let ti ← match sigStx with | some s => typeInfo s | none => pure none
  let typeOK := match ti with | some (_, _, _, multi) => !multi | none => true
  let typeW := match ti with | some (_, _, tw, false) => 3 + tw | _ => 0
  let vFlat := vf.flatWidth
  let noComment := !Lean4Fmt.Syntax.subtreeHasLineComment defn
  let total := prefixWidth + bW + typeW + (vFlat.getD 1000000)
  -- inline form of the value (` := body`, or the span reproduced flat)
  let valInline : Doc := match vf with
    | .span d => .space ++ .flatten d
    | .body d _ => .text " := " ++ .flatten d
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
    let reserve := (Lean4Fmt.Doc.firstLineWidth valBroken).1
    let sig ← match sigStx with | some s => sigDoc nameCol prefixWidth reserve s | none => pure .nil
    return .text kw ++ .space ++ .text declId ++ sig ++ valBroken

/-- Emit a declaration (bare — `Module` places its leading trivia), recursing
    via `walk` where needed. Only plain `:= term` defs are actively formatted;
    `where`-instance / equation / other value forms reproduce whole-verbatim
    (their sig↔value boundary trivia is subtle — deferred to later depth). -/
def emit
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.EmitM Doc := do
  let a := stx.getArgs
  let some defn := a[1]? | return (← verbatim stx)
  let dargs := defn.getArgs
  let isSimpleVal := (dargs[3]?.map (·.getKind)) == some ``Lean.Parser.Command.declValSimple
  if !isDefShape defn.getKind || !isSimpleVal then
    return (← verbatim stx)     -- structure/inductive/instance/where/eqns: reproduce
  let attrsOwnLine := (← read).breaking.attributesOwnLine
  let (modsDoc, modsWidth) := match a[0]? with
    | some m => modifiersDoc attrsOwnLine m
    | none => (.nil, 0)
  return modsDoc ++ (← defnDoc walk modsWidth defn)

end Lean4Fmt.Emit.Decl
