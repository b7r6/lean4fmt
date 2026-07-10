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

namespace Lean4Fmt.Emit.Decl

open Lean Lean4Fmt.Doc Lean4Fmt.Emit

/-- Emit a declaration's `declModifiers` = [docComment?, attributes?, visibility?,
    …]. The doc comment (always first) goes on its own line (literal `textRaw` —
    it may be multi-line — then a `hardline`); the remaining modifiers
    (attributes/visibility/…) sit on the declaration's own line, space-joined,
    followed by a single space before the keyword. This fixes the v1-era gluing of
    `/-- … -/` onto the `def` line while staying token-preserving and idempotent
    (decls sit at column 0, so the literal doc comment re-emits byte-exactly).
    Returns the doc and the width of the INLINE prefix it contributes to the
    keyword's line (attributes/visibility + trailing space; the doc comment is on
    its own line so contributes 0) — used for signature width coupling. -/
private def modifiersDoc (m : Lean.Syntax) : Doc × Nat := Id.run do
  let margs := m.getArgs
  let docText := (margs[0]?.map bareSrc).getD "" |>.trimAscii.toString
  let restParts := (margs.toList.drop 1).filterMap (fun c =>
    let s := (bareSrc c).trimAscii.toString; if s.isEmpty then none else some s)
  let docDoc : Doc := if docText.isEmpty then .nil else .textRaw docText ++ .hardline
  let restStr := String.intercalate " " restParts
  let restDoc : Doc := if restParts.isEmpty then .nil else .text restStr ++ .space
  let inlineWidth := if restParts.isEmpty then 0 else restStr.length + 1
  return (docDoc ++ restDoc, inlineWidth)

/-- Keyword-led definition shapes we actively format. -/
private def isDefShape (kind : SyntaxNodeKind) : Bool :=
  kind == ``Lean.Parser.Command.definition
    || kind == ``Lean.Parser.Command.theorem
    || kind == ``Lean.Parser.Command.abbrev
    || kind == ``Lean.Parser.Command.opaque
    || kind == ``Lean.Parser.Command.example

/-- Signature return-type info: `none` if there is no type spec, else
    `(termDoc, colonTypeDoc, flatWidth, multiline?)` where `termDoc` is the type
    term alone (no colon) and `colonTypeDoc` is the whole `: τ` byte-exact (with
    the colon). Callers use `termDoc` (adding their own `: `) when it is single
    line, and `colonTypeDoc` when it is multi-line or an unexpected shape (so the
    colon is never lost). -/
private def typeInfo (sig : Lean.Syntax) : EmitM (Option (Doc × Doc × Nat × Bool)) := do
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
private def sigDoc (nameCol prefixWidth reserve : Nat) (sig : Lean.Syntax) : EmitM Doc := do
  let a := sig.getArgs
  let binders := (a[0]?.map (·.getArgs)).getD #[]
  let ti ← typeInfo sig
  let mode := (← read).breaking.binders
  let cont := (← read).layout.continuationIndent
  let w := (← read).layout.lineWidth
  match mode with
  | .onePerLine =>
    let mut d : Doc := .nil
    for b in binders do d := d ++ .hardline ++ (← verbatim b)
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
private def isActiveMultiline (kind : SyntaxNodeKind) : Bool :=
  kind.toString == "termIfThenElse"
    || kind.toString == "termDepIfThenElse"
    || kind == ``Lean.Parser.Term.app
    || kind == ``Lean.Parser.Term.anonymousCtor
    || kind.toString == "«term[_]»"
    || kind == ``Lean.Parser.Term.let
    || kind == ``Lean.Parser.Term.match

/-- `:= value` — actively format the value when it lays out flat (single line);
    for a ported active kind, compose `:=` + a width-aware group so the value sits
    on the same line if it fits or drops to an indented next line otherwise (the
    construct's own group then breaks internally). Any other multi-line value is
    reproduced as the whole `declValSimple` span (`:=` as anchor line), which
    keeps the separator and multi-line indentation correct. -/
private def valDoc (walk : Lean4Fmt.Emit.Walk) (declVal : Lean.Syntax) : EmitM Doc := do
  if declVal.getKind == ``Lean.Parser.Command.declValSimple then
    let a := declVal.getArgs
    -- a[2] = termination suffix, a[3] = where clause — if either is present we must
    -- reproduce the whole span (walking only the value would drop them).
    let hasSuffix := (a[2]?.map (fun s => !(bareSrc s).trimAscii.toString.isEmpty)).getD false
    let hasWhere := (a[3]?.map (fun s => !s.getArgs.isEmpty)).getD false
    match a[1]? with
    | some v =>
      if hasSuffix || hasWhere then return .space ++ (← verbatim declVal)
      let vdoc ← walk v
      let clean := !Lean4Fmt.Syntax.subtreeHasLineComment v
        && !Lean4Fmt.Doc.hasMultilineVerbatim vdoc
      -- `do` is glued to `:=` (compact style, Style.breaking.compactDo): its own
      -- nest indents statements by 2 from the declaration, not from a dropped line.
      if v.getKind == ``Lean.Parser.Term.do && clean then
        return .text " := " ++ vdoc
      -- Active layout is safe (idempotent) exactly when the value contains no
      -- multi-line verbatim block: active rendering then only emits
      -- text/line/nest/hardline, never re-anchors an opaque block. Ported active
      -- kinds (no line comment) lay out width-aware; anything with an embedded
      -- multi-line opaque block falls back to the proven-safe whole-span.
      if isActiveMultiline v.getKind && clean then
        return .text " :=" ++ .group (.nest 2 (.line ++ vdoc))
      match Lean4Fmt.Doc.flatWidth vdoc with
      | some _ => return .text " := " ++ .flatten vdoc          -- dense flat, no suffix
      | none => return .space ++ (← verbatim declVal)           -- multi-line: safe span
    | none => return .space ++ (← verbatim declVal)
  else
    return .space ++ (← verbatim declVal)   -- declValEqns / where-struct: literal span

/-- Format the inner definition node `[kw, declId, sig, declVal, …]`. `modsWidth`
    is the inline width the modifiers add to the keyword's line (for signature
    width coupling). -/
private def defnDoc (walk : Lean4Fmt.Emit.Walk) (modsWidth : Nat) (defn : Lean.Syntax) : EmitM Doc := do
  let a := defn.getArgs
  let kw := match a[0]? with | some (.atom _ v) => v | _ => "def"
  let declId := (a[1]?.map bareSrc).getD ""
  -- Value first: its first-line width (up to its own first break, e.g. `:= by`)
  -- is reserved when deciding whether the signature's type breaks after the colon.
  let val ← match a[3]? with | some v => valDoc walk v | none => pure .nil
  let reserve := (Lean4Fmt.Doc.firstLineWidth val).1
  let nameCol := modsWidth + kw.length + 1              -- column where the declId starts
  let prefixWidth := nameCol + declId.length            -- column where binders start
  let sig ← match a[2]? with | some s => sigDoc nameCol prefixWidth reserve s | none => pure .nil
  return .text kw ++ .space ++ .text declId ++ sig ++ val

/-- Emit a declaration (bare — `Module` places its leading trivia), recursing
    via `walk` where needed. Only plain `:= term` defs are actively formatted;
    `where`-instance / equation / other value forms reproduce whole-verbatim
    (their sig↔value boundary trivia is subtle — deferred to later depth). -/
def emit (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.EmitM Doc := do
  let a := stx.getArgs
  let some defn := a[1]? | return (← verbatim stx)
  let dargs := defn.getArgs
  let isSimpleVal := (dargs[3]?.map (·.getKind)) == some ``Lean.Parser.Command.declValSimple
  if !isDefShape defn.getKind || !isSimpleVal then
    return (← verbatim stx)     -- structure/inductive/instance/where/eqns: reproduce
  let (modsDoc, modsWidth) := match a[0]? with
    | some m => modifiersDoc m
    | none => (.nil, 0)
  return modsDoc ++ (← defnDoc walk modsWidth defn)

end Lean4Fmt.Emit.Decl
