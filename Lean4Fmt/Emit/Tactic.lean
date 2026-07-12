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

/-- The items of a `tacticSeq` (unwrapping `tacticSeq1Indented`), skipping the
    empty separator slots; `none` on an explicit `;` (the line layout would
    lose it) or a structural surprise. -/
private def tacticItems?
            (seq : Lean.Syntax)
            : Option (Array Lean.Syntax) := Id.run do
  if seq.getKind != ``Lean.Parser.Tactic.tacticSeq then return none
  let s1 := (seq.getArgs[0]?).getD .missing
  if s1.getKind != ``Lean.Parser.Tactic.tacticSeq1Indented then return none
  let some inner := s1.getArgs[0]? | return none
  let mut items : Array Lean.Syntax := #[]
  for c in inner.getArgs do
    if (Lean4Fmt.Emit.bareSrc c).trimAscii.toString.isEmpty then continue  -- separator slot
    if c.isAtom then return none   -- explicit `;`
    items := items.push c
  if items.isEmpty then return none
  return some items

/-- An arm body (`induction … with | alt => <tactics>`): a single clean flat
    tactic goes width-aware after the `=>` (inline when it fits); anything else
    one tactic per line at +2. `none` when the sequence has no safe layout. -/
private def armSeqDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (seq : Lean.Syntax)
            : Lean4Fmt.Emit.EmitM (Option Doc) := do
  let some items := tacticItems? seq | return none
  if items.size == 1 then
    let lead := (Lean4Fmt.Syntax.leading? items[0]!).getD ""
    let plainLead := ((lead.splitOn "\n").drop 1).dropLast.isEmpty
    if plainLead then
      let tDoc ← walk items[0]!
      if (Lean4Fmt.Doc.flatWidth tDoc).isSome && !Lean4Fmt.Doc.hasMultilineVerbatim tDoc then
        return some (.group (.nest 2 (.line ++ tDoc)))
  match ← DoNotation.seqLinesDoc? walk items true with
  | some body => return some (.nest 2 body)
  | none => return none

/-- Emit a Tactic-category construct: the `by` block (one tactic per line at
    +2), and the ported tactic interiors — `exact`/`apply`/`refine` (term
    walked, width-aware), `rw` (rule list as a commaList), `unfold` (idents as
    text), `induction`/`cases … with` alternatives (arm bodies via the branch
    layout). Unknown tactics reproduce verbatim — the tactic language is
    extensible and byte-exact passthrough is the contract. -/
def emit
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.EmitM Doc := do
  let kind := stx.getKind
  let a := stx.getArgs
  if kind == ``Lean.Parser.Tactic.exact || kind == ``Lean.Parser.Tactic.apply
      || kind == ``Lean.Parser.Tactic.refine then
    -- [kw, term] — the term walked, flat on the kw line when it fits
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    if a.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
    let kwT := (Lean4Fmt.Emit.bareSrc a[0]!).trimAscii.toString
    let tDoc ← walk a[1]!
    if Lean4Fmt.Doc.hasMultilineVerbatim tDoc then return (← Lean4Fmt.Emit.verbatim stx)
    return .text kwT ++ .group (.nest 2 (.line ++ tDoc))
  else if kind == ``Lean.Parser.Tactic.rwSeq then
    -- ["rw", optConfig, rwRuleSeq ["[", rules, "]"], location?]
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    if a.size != 4 then return (← Lean4Fmt.Emit.verbatim stx)
    if !(Lean4Fmt.Emit.bareSrc a[1]!).trimAscii.toString.isEmpty then
      return (← Lean4Fmt.Emit.verbatim stx)   -- config: verbatim for now
    let rs := a[2]!
    if rs.getKind != ``Lean.Parser.Tactic.rwRuleSeq || rs.getArgs.size != 3 then
      return (← Lean4Fmt.Emit.verbatim stx)
    let mut ds : Array Doc := #[]
    for r in (rs.getArgs[1]?.map (·.getArgs)).getD #[] do
      if r.isAtom then continue
      let t := (Lean4Fmt.Emit.bareSrc r).trimAscii.toString
      if t.isEmpty || t.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
      ds := ds.push (.text t)
    if ds.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
    let locT := ((a[3]?.map Lean4Fmt.Emit.bareSrc).getD "").trimAscii.toString
    if locT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let locD : Doc := if locT.isEmpty then .nil else .text (" " ++ locT)
    return .text "rw " ++ Lean4Fmt.Doc.commaList "[" "]" ds ++ locD
  else if kind == ``Lean.Parser.Tactic.unfold then
    -- ["unfold", idents, location?] — plain text, token-for-token
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    let mut line := ""
    for c in a do
      let t := (Lean4Fmt.Emit.bareSrc c).trimAscii.toString
      if t.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
      if !t.isEmpty then line := if line.isEmpty then t else line ++ " " ++ t
    if line.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
    return .text line
  else if kind == ``Lean.Parser.Tactic.induction || kind == ``Lean.Parser.Tactic.cases then
    -- [kw, targets, …, alts?] — head token-for-token; `with` alternatives as
    -- arms: `| pat =>` + body via the branch layout. No alternatives (bare
    -- `induction n`) is a plain text line.
    if a.size == 0 then return (← Lean4Fmt.Emit.verbatim stx)
    let mut head := ""
    for c in a.extract 0 (a.size - 1) do
      let t := (Lean4Fmt.Emit.bareSrc c).trimAscii.toString
      if t.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
      if !t.isEmpty then head := if head.isEmpty then t else head ++ " " ++ t
    if head.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
    let altsSlot := a[a.size - 1]!
    let altsT := (Lean4Fmt.Emit.bareSrc altsSlot).trimAscii.toString
    if altsT.isEmpty then return (.text head)
    let some altsNode := altsSlot.getArgs[0]? | return (← Lean4Fmt.Emit.verbatim stx)
    if altsNode.getKind != ``Lean.Parser.Tactic.inductionAlts || altsNode.getArgs.size != 3 then
      return (← Lean4Fmt.Emit.verbatim stx)
    if !(Lean4Fmt.Emit.bareSrc altsNode.getArgs[1]!).trimAscii.toString.isEmpty then
      return (← Lean4Fmt.Emit.verbatim stx)
    let alts := altsNode.getArgs[2]!.getArgs
    let mut d : Doc := .text (head ++ " with")
    for alt in alts do
      if alt.getKind != ``Lean.Parser.Tactic.inductionAlt || alt.getArgs.size != 2 then
        return (← Lean4Fmt.Emit.verbatim stx)
      if Lean4Fmt.Syntax.interiorHasLineComment alt then return (← Lean4Fmt.Emit.verbatim stx)
      let lhsT := (Lean4Fmt.Emit.bareSrc alt.getArgs[0]!).trimAscii.toString
      if lhsT.isEmpty || lhsT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
      let rhs := alt.getArgs[1]!.getArgs
      if rhs.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
      let some seq := rhs[1]? | return (← Lean4Fmt.Emit.verbatim stx)
      let some bD ← armSeqDoc? walk seq | return (← Lean4Fmt.Emit.verbatim stx)
      d := d ++ .hardline ++ .text (lhsT ++ " =>") ++ bD
    return d
  else if kind != ``Lean.Parser.Term.byTactic then
    return (← Lean4Fmt.Emit.verbatim stx)
  else
  if a.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
  -- a comment on the `by` line itself has no home in the layout
  if !((Lean4Fmt.Syntax.trailing? a[0]!).getD "").trimAscii.toString.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  let some items := tacticItems? a[1]! | return (← Lean4Fmt.Emit.verbatim stx)
  match ← DoNotation.seqLinesDoc? walk items true with
  | some body => return .text "by" ++ .nest 2 body
  | none => return (← Lean4Fmt.Emit.verbatim stx)

end Lean4Fmt.Emit.Tactic
