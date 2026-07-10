/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // EMIT // DoNotation
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Open-recursion emitter for the DoNotation category (DESIGN_V2 §11). SCAFFOLD:
    reproduces verbatim for now; active Doc production is ported here per
    construct (from the v1 Emitter reference), guarded by the safety gate so
    every intermediate state stays correct.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Emit.Monad

namespace Lean4Fmt.Emit.DoNotation

open Lean Lean4Fmt.Doc

/-- Emit `do <seq>`, one statement per line indented by 2. Only the plain
    `doSeqIndent` shape is handled (each statement walked; the newline is the
    separator); the bracketed `{ … }` shape and any structural surprise fall back
    to verbatim so no token is dropped. A statement carrying a multi-line opaque
    block trips the valDoc gate to the safe whole-span. -/
def emit
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.EmitM Doc := do
  let a := stx.getArgs
  let some seq := a[1]? | return (← Lean4Fmt.Emit.verbatim stx)
  if seq.getKind != ``Lean.Parser.Term.doSeqIndent then
    return (← Lean4Fmt.Emit.verbatim stx)
  let mut items : Array Lean.Syntax := #[]
  for g in seq.getArgs do
    for c in g.getArgs do
      if c.getKind == ``Lean.Parser.Term.doSeqItem then items := items.push c
  if items.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
  -- Guard: a doSeqItem with a non-empty terminator (explicit `;`) would lose that
  -- token if we walked only the statement — bail to verbatim for those.
  for it in items do
    let ia := it.getArgs
    if ia.size > 1 && !((Lean4Fmt.Emit.bareSrc (ia[ia.size-1]!)).trimAscii.toString.isEmpty) then
      return (← Lean4Fmt.Emit.verbatim stx)
  let mut body : Doc := .nil
  let mut first := true
  for it in items do
    let sDoc ← walk (it.getArgs[0]?.getD .missing)
    body := body ++ (if first then .nil else .hardline) ++ sDoc
    first := false
  return .text "do" ++ .nest 2 (.hardline ++ body)

end Lean4Fmt.Emit.DoNotation
