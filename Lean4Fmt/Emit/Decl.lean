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
    (decls sit at column 0, so the literal doc comment re-emits byte-exactly). -/
private def modifiersDoc (m : Lean.Syntax) : Doc := Id.run do
  let margs := m.getArgs
  let docText := (margs[0]?.map bareSrc).getD "" |>.trimAscii.toString
  let restParts := (margs.toList.drop 1).filterMap (fun c =>
    let s := (bareSrc c).trimAscii.toString; if s.isEmpty then none else some s)
  let docDoc : Doc := if docText.isEmpty then .nil else .textRaw docText ++ .hardline
  let restDoc : Doc :=
    if restParts.isEmpty then .nil else .text (String.intercalate " " restParts) ++ .space
  return docDoc ++ restDoc

/-- Keyword-led definition shapes we actively format. -/
private def isDefShape (kind : SyntaxNodeKind) : Bool :=
  kind == ``Lean.Parser.Command.definition
    || kind == ``Lean.Parser.Command.theorem
    || kind == ``Lean.Parser.Command.abbrev
    || kind == ``Lean.Parser.Command.opaque
    || kind == ``Lean.Parser.Command.example

/-- Reflow an `optDeclSig`/`declSig` = [binders, typeSpec?] with normalized
    single spaces on one line (Straylight is horizontally dense; a width-aware
    signature-breaking policy is §Breaking depth work). -/
private def sigDoc (sig : Lean.Syntax) : EmitM Doc := do
  let a := sig.getArgs
  let binders := (a[0]?.map (·.getArgs)).getD #[]
  let mut d : Doc := .nil
  for b in binders do
    d := d ++ .space ++ (← verbatim b)
  -- typeSpec (": τ") — space before the colon
  match a[1]? with
  | some ts => if !ts.getArgs.isEmpty then d := d ++ .space ++ (← verbatim ts)
  | none => pure ()
  return d

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
      -- Active layout is safe (idempotent) exactly when the value contains no
      -- multi-line verbatim block: active rendering then only emits
      -- text/line/nest/hardline, never re-anchors an opaque block. Ported active
      -- kinds (no line comment) lay out width-aware; anything with an embedded
      -- multi-line opaque block falls back to the proven-safe whole-span.
      if isActiveMultiline v.getKind && !Lean4Fmt.Syntax.subtreeHasLineComment v
          && !Lean4Fmt.Doc.hasMultilineVerbatim vdoc then
        return .text " :=" ++ .group (.nest 2 (.line ++ vdoc))
      match Lean4Fmt.Doc.flatWidth vdoc with
      | some _ => return .text " := " ++ .flatten vdoc          -- dense flat, no suffix
      | none => return .space ++ (← verbatim declVal)           -- multi-line: safe span
    | none => return .space ++ (← verbatim declVal)
  else
    return .space ++ (← verbatim declVal)   -- declValEqns / where-struct: literal span

/-- Format the inner definition node `[kw, declId, sig, declVal, …]`. -/
private def defnDoc (walk : Lean4Fmt.Emit.Walk) (defn : Lean.Syntax) : EmitM Doc := do
  let a := defn.getArgs
  let kw := match a[0]? with | some (.atom _ v) => v | _ => "def"
  let declId := (a[1]?.map bareSrc).getD ""
  let sig ← match a[2]? with | some s => sigDoc s | none => pure .nil
  let val ← match a[3]? with | some v => valDoc walk v | none => pure .nil
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
  let modsDoc : Doc := match a[0]? with
    | some m => modifiersDoc m
    | none => .nil
  return modsDoc ++ (← defnDoc walk defn)

end Lean4Fmt.Emit.Decl
