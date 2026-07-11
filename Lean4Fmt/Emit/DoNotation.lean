/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // EMIT // DoNotation
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Open-recursion emitter for the DoNotation category (DESIGN_V2 §11): the `do`
    block itself plus its binding statements (`doLet`, `doLetArrow`, `doReassign`,
    `doReassignArrow` — their values walked so they lay out actively). Everything
    else (`doIf`, `for`, pattern-arrow lets with an `| else` tail, …) reproduces
    verbatim, guarded by the safety gate so every intermediate state stays
    correct.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Emit.Monad

namespace Lean4Fmt.Emit.DoNotation

open Lean Lean4Fmt.Doc

/-- `x (: τ)? ← v` — the monadic-bind decl inside doLetArrow / doReassignArrow.
    The arrow atom is reproduced from source (`←` or `<-` — the token gate cares);
    the value inside the `doExpr` is walked, flat on the arrow line when it fits,
    else on the next line at +2. A `do` value glues to the arrow (its body brings
    its own hardline). `none` on any structural surprise or a value carrying a
    multi-line opaque block — the caller reproduces the whole statement verbatim. -/
private def idDeclDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (d : Lean.Syntax)
            : Lean4Fmt.Emit.EmitM (Option Doc) := do
  if d.getKind != ``Lean.Parser.Term.doIdDecl then return none
  let a := d.getArgs
  if a.size != 4 then return none
  let idT := (Lean4Fmt.Emit.bareSrc a[0]!).trimAscii.toString
  let tyT := (Lean4Fmt.Emit.bareSrc a[1]!).trimAscii.toString
  let arrowT := (Lean4Fmt.Emit.bareSrc a[2]!).trimAscii.toString
  let head := String.intercalate " " ([idT, tyT].filter (fun s => !s.isEmpty))
  if head.isEmpty || head.any (· == '\n') || arrowT.any (· == '\n') then return none
  let ex := a[3]!
  if ex.getKind != ``Lean.Parser.Term.doExpr then return none
  let some v := ex.getArgs[0]? | return none
  let vdoc ← walk v
  if Lean4Fmt.Doc.hasMultilineVerbatim vdoc then return none
  if v.getKind == ``Lean.Parser.Term.do then
    return some (.text head ++ .text (" " ++ arrowT ++ " ") ++ vdoc)
  return some (.text head ++ .text (" " ++ arrowT) ++ .group (.nest 2 (.line ++ vdoc)))

/-- Emit `do <seq>`, one statement per line indented by 2, or one of the binding
    statements (see module header). Only the plain `doSeqIndent` shape of `do` is
    handled (each statement walked; the newline is the separator); the bracketed
    `{ … }` shape and any structural surprise fall back to verbatim so no token
    is dropped. A statement carrying a multi-line opaque block trips the valDoc
    gate to the safe whole-span. -/
def emit
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.EmitM Doc := do
  let kind := stx.getKind
  let a := stx.getArgs
  if kind == ``Lean.Parser.Term.doLet || kind == ``Lean.Parser.Term.doLetArrow then
    -- `let (mut)? (config)? decl` = [let, mut?, letConfig, decl] where decl is a
    -- letDecl (`:=`, walked — Term handles the 5-slot shape) or a doIdDecl (`←`).
    -- The pattern-arrow form (doPatDecl, with its optional `| else` tail) stays
    -- verbatim.
    if Lean4Fmt.Syntax.subtreeHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    if a.size != 4 then return (← Lean4Fmt.Emit.verbatim stx)
    let mutT := (Lean4Fmt.Emit.bareSrc a[1]!).trimAscii.toString
    let cfgT := (Lean4Fmt.Emit.bareSrc a[2]!).trimAscii.toString
    if mutT.any (· == '\n') || cfgT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let headD : Doc := .text "let " ++ (if mutT.isEmpty then .nil else .text (mutT ++ " "))
      ++ (if cfgT.isEmpty then .nil else .text (cfgT ++ " "))
    if kind == ``Lean.Parser.Term.doLet then
      let dDoc ← walk a[3]!
      if Lean4Fmt.Doc.hasMultilineVerbatim dDoc then return (← Lean4Fmt.Emit.verbatim stx)
      return headD ++ dDoc
    else
      match ← idDeclDoc? walk a[3]! with
      | some d => return headD ++ d
      | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == ``Lean.Parser.Term.doReassign then
    -- bare `x := v` = [letIdDeclNoBinders] — the inner decl IS the statement
    if Lean4Fmt.Syntax.subtreeHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    let some inner := a[0]? | return (← Lean4Fmt.Emit.verbatim stx)
    let dDoc ← walk inner
    if Lean4Fmt.Doc.hasMultilineVerbatim dDoc then return (← Lean4Fmt.Emit.verbatim stx)
    return dDoc
  else if kind == ``Lean.Parser.Term.doReassignArrow then
    -- bare `x ← v` = [doIdDecl]
    if Lean4Fmt.Syntax.subtreeHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    let some inner := a[0]? | return (← Lean4Fmt.Emit.verbatim stx)
    match ← idDeclDoc? walk inner with
    | some d => return d
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind != ``Lean.Parser.Term.do then
    return (← Lean4Fmt.Emit.verbatim stx)
  else
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
