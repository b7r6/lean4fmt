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

/-- Keyword-led definition shapes we actively format. -/
private def isDefShape (kind : SyntaxNodeKind) : Bool :=
  kind == ``Lean.Parser.Command.definition
    || kind == ``Lean.Parser.Command.theorem
    || kind == ``Lean.Parser.Command.abbrev
    || kind == ``Lean.Parser.Command.opaque
    || kind == ``Lean.Parser.Command.example

/-- Reflow an `optDeclSig`/`declSig` = [binders, typeSpec?] as a breakable group:
    `(x : α) (y : β) : τ`, each binder on a `line`. -/
private def sigDoc (sig : Lean.Syntax) : EmitM Doc := do
  let a := sig.getArgs
  let binders := (a[0]?.map (·.getArgs)).getD #[]
  let mut d : Doc := .nil
  for b in binders do
    d := d ++ .line ++ (← verbatim b)
  -- typeSpec (": τ") — space before the colon; present in optDeclSig args[1]
  match a[1]? with
  | some ts => if !ts.getArgs.isEmpty then d := d ++ .line ++ (← verbatim ts)
  | none => pure ()
  return .group d

/-- `:= value` (declValSimple) — value laid out after `:=`, breakable. Other
    value forms (equations, where-struct) pass through verbatim. -/
private def valDoc (declVal : Lean.Syntax) : EmitM Doc := do
  if declVal.getKind == ``Lean.Parser.Command.declValSimple then
    let a := declVal.getArgs
    match a[1]? with
    | some v => return .group (.text " :=" ++ .nest 2 (.line ++ (← verbatim v)))
    | none => return (← verbatim declVal)
  else
    return .space ++ (← verbatim declVal)

/-- Format the inner definition node `[kw, declId, sig, declVal, …]`. -/
private def defnDoc (defn : Lean.Syntax) : EmitM Doc := do
  let a := defn.getArgs
  let kw := match a[0]? with | some (.atom _ v) => v | _ => "def"
  let declId := (a[1]?.map bareSrc).getD ""       -- name (+ univ params), bare
  let sig ← match a[2]? with | some s => sigDoc s | none => pure .nil
  let val ← match a[3]? with | some v => valDoc v | none => pure .nil
  return .text kw ++ .space ++ .text declId ++ sig ++ val

/-- Emit a declaration (bare — `Module` places its leading trivia), recursing
    via `walk` where needed. -/
def emit (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.EmitM Doc := do
  let _ := walk
  let a := stx.getArgs
  let some defn := a[1]? | return (← verbatim stx)
  if !isDefShape defn.getKind then
    return (← verbatim stx)     -- e.g. instance/axiom: reproduce for now
  -- modifiers (doc comment / attrs / visibility) — reproduce bare, then a space
  let modsDoc : Doc := match a[0]? with
    | some m => let s := bareSrc m; if s.trimAscii.toString.isEmpty then .nil else .text s ++ .space
    | none => .nil
  return modsDoc ++ (← defnDoc defn)

end Lean4Fmt.Emit.Decl
