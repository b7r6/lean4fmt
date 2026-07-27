/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // LEAN4FMT // EMIT // BINDERS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Binder rendering shared by Decl (signatures) and Term (fun/forall): active
    single-line text via binderText?; multi-line binder TYPES walk (chains lay
    out inside the brackets).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Emit.Monad
import Lean4Fmt.Emit.Tokens

namespace Lean4Fmt.Emit

open Lean Lean4Fmt.Doc

/-- A binder as a single active line: bracket atoms from source, the interior
    segments trimmed and single-spaced (`(x  :  Nat)` → `(x : Nat)`). Only the
    bracketed binder kinds; `none` (caller falls back to per-binder verbatim)
    on anything else, a multi-line piece, or a comment (a line comment forces a
    newline into its segment, so the '\n' guard covers it). -/
def binder_text? (b : Lean.Syntax) (preserve : Bool := false) : Option String :=
  Id.run
    do
      let k := b.getKind
      if k != ``Lean.Parser.Term.explicitBinder && k != ``Lean.Parser.Term.implicitBinder
          && k != ``Lean.Parser.Term.strictImplicitBinder && k != ``Lean.Parser.Term.instBinder then
        return none
      let a := b.getArgs
      if a.size < 3 then
        return none
      let l := (bare_src a[0]!).trimAscii.toString
      let r := (bare_src a[a.size-1]!).trimAscii.toString
      if l.isEmpty || r.isEmpty then
        return none
      if preserve then
        -- byte-exact interior (the author's `s: String` survives)
        let t := (bare_src b).trimAscii.toString
        if t.isEmpty || t.any (· == '\n') then
          return none
        return some t
      let mut interior := ""
      for c in a.extract 1 (a.size - 1) do
        let t := Lean4Fmt.Emit.canon_tok c
        if t.any (· == '\n') then
          return none
        if !t.isEmpty then interior := if interior.isEmpty then t else interior ++ " " ++ t
      if interior.isEmpty then
        return none
      return some (l ++ interior ++ r)

private
structure binder_build_state where
  head    : String := ""
  valid   : Bool := true
  typeDoc : Doc := .nil

private
def broken_binder_doc (walk : Lean4Fmt.Emit.Walk) (binder : Lean.Syntax) : emit_m Doc := do
  let kind := binder.getKind
  if (kind == ``Lean.Parser.Term.explicitBinder || kind == ``Lean.Parser.Term.implicitBinder
      || kind == ``Lean.Parser.Term.strictImplicitBinder || kind == ``Lean.Parser.Term.instBinder)
      && !Lean4Fmt.Syntax.interior_has_line_comment binder then
    let arguments := binder.getArgs
    if arguments.size ≥ 3 then
      let left := (bare_src arguments[0]!).trimAscii.toString
      let right := (bare_src arguments[arguments.size - 1]!).trimAscii.toString
      let mut state : binder_build_state := {}
      for child in arguments.extract 1 (arguments.size - 1) do
        let text := (bare_src child).trimAscii.toString
        if text.isEmpty then continue
        if !text.any (· == '\n') then
          state := { state with
            head := if state.head.isEmpty then text else state.head ++ " " ++ text }
        else
          let childArguments := child.getArgs
          if childArguments.size == 2
              && (bare_src childArguments[0]!).trimAscii.toString == ":" then
            let typeDoc ← walk childArguments[1]!
            if Lean4Fmt.Doc.hasMultilineVerbatim typeDoc then
              state := { state with valid := false }
            else
              state := { state with typeDoc := .text " : " ++ typeDoc }
          else
            state := { state with valid := false }
      if state.valid && !state.head.isEmpty then
        return .text (left ++ state.head) ++ state.typeDoc ++ .text right
  verbatim binder

/-- A binder doc: active single-line text when `binderText?` can hold it;
    a MULTI-LINE binder walks its type (chains/apps lay out actively inside
    the brackets); verbatim only when the shape offers no seam. -/
def binder_doc (walk : Lean4Fmt.Emit.Walk) (b : Lean.Syntax) : emit_m Doc := do
  match binder_text? b (← read).spacing.preserveBinders with
  | some t => pure (.text t)
  | none => broken_binder_doc walk b

end Lean4Fmt.Emit
