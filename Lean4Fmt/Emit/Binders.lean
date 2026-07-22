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
def binderText?
    (b : Lean.Syntax)
    (preserve : Bool := false)
    : Option String :=

  Id.run
    do
      let k := b.getKind
      if k != ``Lean.Parser.Term.explicitBinder && k != ``Lean.Parser.Term.implicitBinder
          && k != ``Lean.Parser.Term.strictImplicitBinder && k != ``Lean.Parser.Term.instBinder then
        return none
      let a := b.getArgs
      if a.size < 3 then
        return none
      let l := (bareSrc a[0]!).trimAscii.toString
      let r := (bareSrc a[a.size-1]!).trimAscii.toString
      if l.isEmpty || r.isEmpty then
        return none
      if preserve then
        -- byte-exact interior (the author's `s: String` survives)
        let t := (bareSrc b).trimAscii.toString
        if t.isEmpty || t.any (· == '\n') then
          return none
        return some t
      let mut interior := ""
      for c in a.extract 1 (a.size - 1) do
        let t := Lean4Fmt.Emit.canonTok c
        if t.any (· == '\n') then
          return none
        if !t.isEmpty then interior := if interior.isEmpty then t else interior ++ " " ++ t
      if interior.isEmpty then
        return none
      return some (l ++ interior ++ r)

/-- A binder doc: active single-line text when `binderText?` can hold it;
    a MULTI-LINE binder walks its type (chains/apps lay out actively inside
    the brackets); verbatim only when the shape offers no seam. -/
def binderDoc
    (walk : Lean4Fmt.Emit.Walk)
    (b : Lean.Syntax)
    : EmitM Doc := do

  match binderText? b (← read).spacing.preserveBinders with
  | some t => pure (.text t)
  | none =>
    -- [l, names…, (":" type)?, r] — names single-line, type WALKED
    let k := b.getKind
    if (k == ``Lean.Parser.Term.explicitBinder || k == ``Lean.Parser.Term.implicitBinder
        || k == ``Lean.Parser.Term.strictImplicitBinder || k == ``Lean.Parser.Term.instBinder)
        && !Lean4Fmt.Syntax.interiorHasLineComment b then
      let a := b.getArgs
      if a.size ≥ 3 then
        let l := (bareSrc a[0]!).trimAscii.toString
        let r := (bareSrc a[a.size-1]!).trimAscii.toString
        -- the interior: leading name tokens single-line, then a type slot
        -- whose LAST child is the type term (walked)
        let mut head := ""
        let mut ok := true
        let mut tyDoc : Doc := .nil
        for c in a.extract 1 (a.size - 1) do
          let t := (bareSrc c).trimAscii.toString
          if t.isEmpty then continue
          if !t.any (· == '\n') then
            head := if head.isEmpty then t else head ++ " " ++ t
          else
            -- multi-line piece: the `: τ` slot — walk the type term
            let ca := c.getArgs
            if ca.size == 2 && (bareSrc ca[0]!).trimAscii.toString == ":" then
              let d ← walk ca[1]!
              if Lean4Fmt.Doc.hasMultilineVerbatim d then ok := false
              else tyDoc := .text " : " ++ d
            else ok := false
        if ok && !head.isEmpty then
          return .text (l ++ head) ++ tyDoc ++ .text r
    verbatim b

end Lean4Fmt.Emit
