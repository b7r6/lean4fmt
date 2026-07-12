/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // EMIT // Tactic
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Open-recursion emitter for the Tactic category (DESIGN_V2 §11): the `by`
    block as a statement sequence — one tactic per line at +2, inter-tactic
    comment/blank lines placed structurally, same-line trailing comments
    re-appended (the same seam loop as do-blocks — `DoNotation.seqLinesDoc?`).
    Individual TACTICS reproduce verbatim (the tactic language is extensible;
    unknown kinds ride through byte-exact — per-tactic layouts are ported here
    over time). Explicit `;` separators, the bracketed shape, and structural
    surprises fall back to whole-block verbatim. The kind-spine gate check
    (Frontend §4.2) is what makes active tactic layout safe at all: in a
    whitespace-sensitive block, identical tokens can parse to a DIFFERENT tree.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Emit.Monad
import Lean4Fmt.Emit.DoNotation

namespace Lean4Fmt.Emit.Tactic

open Lean Lean4Fmt.Doc

/-- Emit `by <tactics>`, one tactic per line at +2. -/
def emit
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.EmitM Doc := do
  if stx.getKind != ``Lean.Parser.Term.byTactic then
    return (← Lean4Fmt.Emit.verbatim stx)
  let a := stx.getArgs
  if a.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
  -- a comment on the `by` line itself has no home in the layout
  if !((Lean4Fmt.Syntax.trailing? a[0]!).getD "").trimAscii.toString.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  let s := a[1]!
  if s.getKind != ``Lean.Parser.Tactic.tacticSeq then
    return (← Lean4Fmt.Emit.verbatim stx)
  let s1 := (s.getArgs[0]?).getD .missing
  if s1.getKind != ``Lean.Parser.Tactic.tacticSeq1Indented then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some inner := s1.getArgs[0]? | return (← Lean4Fmt.Emit.verbatim stx)
  let mut items : Array Lean.Syntax := #[]
  for c in inner.getArgs do
    if c.isAtom then
      -- an explicit `;` separator would be lost by the line layout
      if !(Lean4Fmt.Emit.bareSrc c).trimAscii.toString.isEmpty then
        return (← Lean4Fmt.Emit.verbatim stx)
    else items := items.push c
  if items.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
  match ← DoNotation.seqLinesDoc? walk items true with
  | some body => return .text "by" ++ .nest 2 body
  | none => return (← Lean4Fmt.Emit.verbatim stx)

end Lean4Fmt.Emit.Tactic
