/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // LEAN4FMT // EMIT // BINDERS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Binder rendering shared by Decl (signatures) and Term (fun/forall): active
    single-line text via binderText?; multi-line binder TYPES walk (chains lay
    out inside the brackets).
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.emit.monad
import lean_4_fmt.emit.tokens

namespace Lean4Fmt.Emit

open Lean Lean4Fmt.Doc

/-- A binder as a single active line: bracket atoms from source, the interior
    segments trimmed and single-spaced (`(x  :  Nat)` → `(x : Nat)`). Only the
    bracketed binder kinds; `none` (caller falls back to per-binder verbatim)
    on anything else, a multi-line piece, or a comment (a line comment forces a
    newline into its segment, so the '\n' guard covers it). -/
def binder_text? (rightValue : Lean.Syntax) (preserve : Bool := false) : Option String :=
  Id.run
    do
      let kind := rightValue.getKind
      if kind != ``Lean.Parser.Term.explicitBinder && kind != ``Lean.Parser.Term.implicitBinder
          && kind != ``Lean.Parser.Term.strictImplicitBinder
          && kind != ``Lean.Parser.Term.instBinder then
        return none
      let args := rightValue.getArgs
      if args.size < 3 then
        return none
      let leftDelim := (bare_src args[0]!).trimAscii.toString
      let rightDelim := (bare_src args[args.size-1]!).trimAscii.toString
      if leftDelim.isEmpty || rightDelim.isEmpty then
        return none
      if preserve then
        -- byte-exact interior (the author's `s: String` survives)
        let text := (bare_src rightValue).trimAscii.toString
        if text.isEmpty || text.any (· == '\n') then
          return none
        return some text
      let mut interior := ""
      for character in args.extract 1 (args.size - 1) do
        let text := Lean4Fmt.Emit.canon_tok character
        if text.any (· == '\n') then
          return none
        if !text.isEmpty then interior := if interior.isEmpty then text else interior ++ " " ++ text
      if interior.isEmpty then
        return none
      return some (leftDelim ++ interior ++ rightDelim)

private
structure binder_build_state where
  head    : String := ""
  valid   : Bool := true
  sawType : Bool := false
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
          if state.sawType then
            -- A default value follows the type (`(x : T := v)`). Moving that
            -- suffix into the accumulated head would reorder it before `T`.
            state := { state with valid := false }
          else
            state := { state with
              head := if state.head.isEmpty then text else state.head ++ " " ++ text }
        else
          let childArguments := child.getArgs
          if !state.sawType && childArguments.size == 2
              && (bare_src childArguments[0]!).trimAscii.toString == ":" then
            let typeDoc ← walk childArguments[1]!
            if Lean4Fmt.Doc.hasMultilineVerbatim typeDoc then
              state := { state with valid := false }
            else
              state := { state with sawType := true, typeDoc := .text " : " ++ typeDoc }
          else
            state := { state with valid := false }
      if state.valid && !state.head.isEmpty then
        return .text (left ++ state.head) ++ state.typeDoc ++ .text right
  verbatim binder

/-- A binder doc: active single-line text when `binderText?` can hold it;
    a MULTI-LINE binder walks its type (chains/apps lay out actively inside
    the brackets); verbatim only when the shape offers no seam. -/
def binder_doc (walk : Lean4Fmt.Emit.Walk) (rightValue : Lean.Syntax) : emit_m Doc := do
  match binder_text? rightValue (← read).spacing.preserveBinders with
  | some trailing => pure (.text trailing)
  | none => broken_binder_doc walk rightValue

end Lean4Fmt.Emit
