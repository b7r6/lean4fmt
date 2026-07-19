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
import Lean4Fmt.Emit.Tokens
import Lean4Fmt.Emit.DoNotation

namespace Lean4Fmt.Emit.Tactic

open Lean Lean4Fmt.Doc

/-- The items of a `tacticSeq` (unwrapping `tacticSeq1Indented`), grouped into
    LINES: an explicit `;` joins its neighbors into one group (rendered as one
    line, `t1; t2; t3`); empty separator slots (newlines) split groups. `none`
    on a trailing `;` or a structural surprise. -/
private def seqGroupsCore?
            (seqKind seq1Kind : Lean.Name)
            (seq : Lean.Syntax)
            : Option (Array (Array Lean.Syntax)) := Id.run do
  if seq.getKind != seqKind then return none
  let s1 := (seq.getArgs[0]?).getD .missing
  if s1.getKind != seq1Kind then return none
  let some inner := s1.getArgs[0]? | return none
  let mut groups : Array (Array Lean.Syntax) := #[]
  let mut cur : Array Lean.Syntax := #[]
  let mut joinNext := false
  for c in inner.getArgs do
    if (Lean4Fmt.Emit.bareSrc c).trimAscii.toString.isEmpty then continue -- newline slot
    if c.isAtom then
      if (Lean4Fmt.Emit.bareSrc c).trimAscii.toString == ";" then
        if cur.isEmpty then return none
        joinNext := true
        continue
      else return none
    if joinNext then
      cur := cur.push c
      joinNext := false
    else
      if !cur.isEmpty then groups := groups.push cur
      cur := #[c]
  if joinNext then return none          -- dangling `;`
  if !cur.isEmpty then groups := groups.push cur
  if groups.isEmpty then return none
  return some groups

private def tacticGroups? (seq : Lean.Syntax) : Option (Array (Array Lean.Syntax)) :=
  seqGroupsCore? ``Lean.Parser.Tactic.tacticSeq ``Lean.Parser.Tactic.tacticSeq1Indented seq

private def convGroups? (seq : Lean.Syntax) : Option (Array (Array Lean.Syntax)) :=
  seqGroupsCore? `Lean.Parser.Tactic.Conv.convSeq `Lean.Parser.Tactic.Conv.convSeq1Indented seq

/-- One `;`-joined run as a single line: items token-for-token joined by
    `"; "`. `none` when an item is multi-line, carries an interior comment, or
    an INTERMEDIATE item has trailing trivia content (a comment there would
    comment out the rest of the joined line). -/
private def groupText?
            (g : Array Lean.Syntax)
            : Option String := Id.run do
  let mut txt := ""
  for j in [0:g.size] do
    let it := g[j]!
    if Lean4Fmt.Syntax.interiorHasLineComment it then return none
    let t := (Lean4Fmt.Emit.tokenJoin? it).getD
      ((Lean4Fmt.Emit.bareSrc it).trimAscii.toString)
    if t.isEmpty || t.any (· == '\n') then return none
    if j + 1 < g.size then
      let tr := (Lean4Fmt.Syntax.trailing? it).getD ""
      if !tr.trimAscii.toString.isEmpty || tr.any (· == '\n') then return none
    if j > 0 then
      let ld := (Lean4Fmt.Syntax.leading? it).getD ""
      if !ld.trimAscii.toString.isEmpty || ld.any (· == '\n') then return none
    txt := if txt.isEmpty then t else txt ++ "; " ++ t
  if txt.isEmpty then return none
  return some txt

/-- One group's doc: a single tactic walks (active layouts apply); a
    `;`-joined run rides as one text line. -/
private def groupDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (g : Array Lean.Syntax)
            : Lean4Fmt.Emit.EmitM (Option Doc) := do
  if g.size == 1 then return some (← walk g[0]!)
  return (groupText? g).map Doc.text

/-- The seam loop over groups (mirrors `DoNotation.seqLinesDoc?`): each group
    one line, its leading trivia placed structurally, same-line trailing
    comments re-appended (leading of the group's FIRST item, trailing of its
    LAST). -/
private def seqGroupsDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (groups : Array (Array Lean.Syntax))
            (lastOwned : Bool)
            : Lean4Fmt.Emit.EmitM (Option Doc) := do
  let mut body : Doc := .nil
  for h : i in [0:groups.size] do
    let g := groups[i]
    let first := g[0]!
    let glast := g[g.size - 1]!
    let trailT := ((Lean4Fmt.Syntax.trailing? glast).getD "").trimAscii.toString
    let last := i + 1 == groups.size
    if !last && trailT.any (· == '\n') then return none
    if last && !lastOwned && !trailT.isEmpty then return none
    let trailDoc : Doc := if !last && !trailT.isEmpty then .text (" " ++ trailT) else .nil
    let lead := (Lean4Fmt.Syntax.leading? first).getD ""
    -- first group: comment-free blank runs after the block opener are LAYOUT
    -- (dropped; the style re-adds its own) — see seqLinesDoc?
    let sep ← if i == 0 && lead.toList.all (·.isWhitespace) then pure Doc.hardline
      else match Lean4Fmt.Emit.leadingSep? lead with
        | some s => pure s
        | none => return none
    let some gDoc ← groupDoc? walk g | return none
    body := body ++ sep ++ gDoc ++ trailDoc
  return some body

/-- An arm body (`induction … with | alt => <tactics>`): a single clean flat
    tactic goes width-aware after the `=>` (inline when it fits); anything else
    one tactic per line at +2. `none` when the sequence has no safe layout. -/
private def armSeqDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (seq : Lean.Syntax)
            (conv : Bool := false)
            : Lean4Fmt.Emit.EmitM (Option Doc) := do
  let some groups := (if conv then convGroups? seq else tacticGroups? seq) | return none
  if groups.size == 1 then
    let lead := (Lean4Fmt.Syntax.leading? groups[0]![0]!).getD ""
    let plainLead := ((lead.splitOn "\n").drop 1).dropLast.isEmpty
    let srcInline := !lead.any (· == '\n')
    if plainLead && (!(← read).breaking.preserveLineBreaks || srcInline) then
      let some tDoc ← groupDoc? walk groups[0]! | return none
      if (Lean4Fmt.Doc.flatWidth tDoc).isSome && !Lean4Fmt.Doc.hasMultilineVerbatim tDoc then
        return some (.group (.nest 2 (.line ++ tDoc)))
  match ← seqGroupsDoc? walk groups true with
  | some body => return some (.nest 2 body)
  | none => return none

/-- Items of a bracket-list slice (`a, b, c` between `[` and `]`): comma atoms
    skipped, one level of null nesting flattened; `none` on a multi-line item. -/
private def listItems?
            (slice : Array Lean.Syntax)
            : Option (Array Doc) := Id.run do
  let mut items : Array Doc := #[]
  -- an authored TRAILING comma (`[a, b,]`) has no slot in the rebuilt list
  -- (commas go BETWEEN items) — bail rather than drop the token (gate-caught)
  let mut lastComma := false
  for c in slice do
    if c.isAtom then
      if (Lean4Fmt.Emit.bareSrc c).trimAscii.toString == "," then lastComma := true
      continue
    let subs := if c.getKind == Lean.nullKind then c.getArgs else #[c]
    for d in subs do
      if d.isAtom then
        if (Lean4Fmt.Emit.bareSrc d).trimAscii.toString == "," then lastComma := true
        continue
      let t := Lean4Fmt.Emit.canonTok d
      if t.isEmpty || t.any (· == '\n') then return none
      items := items.push (.text t)
      lastComma := false
  if items.isEmpty || lastComma then return none
  return some items

/-- Generic token-line tactic: tokens single-spaced on ONE line, except
    bracket lists (`[a, b, c]` — simp lemmas, rw rules) which render as
    width-aware commaLists, so a long list BREAKS instead of forcing the whole
    tactic (and its enclosing body) verbatim. `none` on a multi-line piece
    outside a bracket list. -/
private partial def lineWords?
            (stx : Lean.Syntax)
            (fill : Bool := false)
            : Option (Array Doc) := Id.run do
  let a := stx.getArgs
  let mut out : Array Doc := #[]
  let mut i := 0
  while i < a.size do
    let c := a[i]!
    if c.isAtom && (Lean4Fmt.Emit.bareSrc c).trimAscii.toString == "[" then
      let mut close : Option Nat := none
      let mut j := i + 1
      while j < a.size do
        if a[j]!.isAtom && (Lean4Fmt.Emit.bareSrc a[j]!).trimAscii.toString == "]" then
          close := some j
          break
        j := j + 1
      let some jc := close | return none
      let some items := listItems? (a.extract (i + 1) jc) | return none
      out := out.push (if fill then Lean4Fmt.Doc.fillList "[" "]" items
        else Lean4Fmt.Doc.commaList "[" "]" items)
      i := jc + 1
      continue
    let t := (Lean4Fmt.Emit.bareSrc c).trimAscii.toString
    if t.isEmpty then
      i := i + 1
      continue
    let hasBracket := c.getArgs.any fun x =>
      x.isAtom && (Lean4Fmt.Emit.bareSrc x).trimAscii.toString == "["
    if !t.any (· == '\n') && !hasBracket then
      out := out.push (.text ((Lean4Fmt.Emit.tokenJoin? c).getD t))
    else
      match lineWords? c fill with
      | some ws => out := out ++ ws
      | none => return none
    i := i + 1
  return some out

/-- Join line words with single spaces. -/
private def joinWords (ws : Array Doc) : Doc :=
  ws.foldl (fun d w => match d with | .nil => w | _ => d ++ .text " " ++ w) .nil

/-- A head-block tactic (`next h => …`, `case foo => …`, `all_goals …`,
    `repeat …`, `conv at x => …`): head tokens single-line joined, the body
    sequence via the branch layout (inline when a single clean flat group
    fits; else one line per group at +2). The body's inter-group comments ride
    the seam loop; comments in the HEAD have no home → `none`. -/
private def headBlockDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (stx : Lean.Syntax)
            (conv : Bool := false)
            : Lean4Fmt.Emit.EmitM (Option Doc) := do
  let a := stx.getArgs
  if a.size < 2 then return none
  let mut head := ""
  for h : i in [0:a.size - 1] do
    let c := a[i]!
    -- first child's leading = the FORM's own leading — the enclosing seam
    -- owns it (see exampleDoc?); interior comments still bail
    let ownLead := if i == 0
      then Lean4Fmt.Syntax.countLineComments ((Lean4Fmt.Syntax.leading? c).getD "")
      else 0
    if Lean4Fmt.Syntax.countSubtreeLineComments c > ownLead then return none
    let t := Lean4Fmt.Emit.canonTok c
    if t.any (· == '\n') then return none
    if !t.isEmpty then head := if head.isEmpty then t else head ++ " " ++ t
  if head.isEmpty then return none
  let some bD ← armSeqDoc? walk a[a.size - 1]! conv | return none
  return some (.text head ++ bD)

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
    -- trailing comma (`rw [a, b, ]`): no slot in the rebuilt list — bail
    let mut lastComma := false
    for r in (rs.getArgs[1]?.map (·.getArgs)).getD #[] do
      if r.isAtom then
        if (Lean4Fmt.Emit.bareSrc r).trimAscii.toString == "," then lastComma := true
        continue
      let t := Lean4Fmt.Emit.canonTok r
      if t.isEmpty || t.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
      ds := ds.push (.text t)
      lastComma := false
    if ds.isEmpty || lastComma then return (← Lean4Fmt.Emit.verbatim stx)
    let locT := (a[3]?.map Lean4Fmt.Emit.canonTok).getD ""
    if locT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let locD : Doc := if locT.isEmpty then .nil else .text (" " ++ locT)
    let listD := if (← read).breaking.listFill then Lean4Fmt.Doc.fillList "[" "]" ds
      else Lean4Fmt.Doc.commaList "[" "]" ds
    return .text "rw " ++ listD ++ locD
  else if kind == ``Lean.Parser.Tactic.tacticHave__
      || kind == `Lean.Parser.Tactic.tacticLet__ then
    -- ["have"/"let", letConfig, letDecl] — the doLet shape minus `mut`; the
    -- letDecl walks through the existing 5-slot machinery
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    if a.size != 3 then return (← Lean4Fmt.Emit.verbatim stx)
    let kwT := (Lean4Fmt.Emit.bareSrc a[0]!).trimAscii.toString
    let cfgT := Lean4Fmt.Emit.canonTok a[1]!
    if cfgT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let dDoc ← walk a[2]!
    if Lean4Fmt.Doc.hasMultilineVerbatim dDoc then return (← Lean4Fmt.Emit.verbatim stx)
    return .text (kwT ++ " ") ++ (if cfgT.isEmpty then Doc.nil else .text (cfgT ++ " ")) ++ dDoc
  else if kind == ``Lean.Parser.Tactic.simp || kind == ``Lean.Parser.Tactic.simpAll
      || kind == `Lean.Parser.Tactic.dsimp || kind == `Lean.Parser.Tactic.simpa
      || kind == `Lean.Parser.Tactic.tacticRwa__ then
    -- simp family + rwa: tokens on one line, bracket lists as width-aware
    -- commaLists (a long lemma list breaks instead of going verbatim)
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    match lineWords? stx ((← read).breaking.listFill) with
    | some ws => if ws.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
                 else return joinWords ws
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == `Lean.Parser.Tactic.«tactic_<;>_» then
    -- [lhs, <;>, rhs] left-nested chain: elements walked (active layouts
    -- apply), packed width-aware; a break leads the continuation with
    -- `<;> ` at +2 (the mathlib shape). Bounded spine walk keeps this total.
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    let mut elems : Array Lean.Syntax := #[]
    let mut cur := stx
    for _ in [0:64] do
      if cur.getKind == `Lean.Parser.Tactic.«tactic_<;>_» && cur.getArgs.size == 3 then
        elems := elems.push cur.getArgs[2]!
        cur := cur.getArgs[0]!
    if cur.getKind == `Lean.Parser.Tactic.«tactic_<;>_» then
      return (← Lean4Fmt.Emit.verbatim stx)   -- absurd depth: bail whole
    elems := elems.push cur
    let chain := elems.reverse
    let mut head : Doc := .nil
    let mut tail : Doc := .nil
    for h : i in [0:chain.size] do
      let eDoc ← walk chain[i]
      if Lean4Fmt.Doc.hasMultilineVerbatim eDoc then return (← Lean4Fmt.Emit.verbatim stx)
      if i == 0 then head := eDoc
      else tail := tail ++ .group (.line ++ .text "<;> " ++ eDoc)
    -- nest ONLY the continuation: nesting the head too would shift the whole
    -- chain right when it lands after a pending newline (a seq seam)
    return head ++ .nest 2 tail
  else if kind == `Lean.Parser.Tactic.first then
    -- single-line `first | a | b` rides the token line; the block form is
    -- `first` + one `| <body>` per alternative at the same indent
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    if !(Lean4Fmt.Emit.bareSrc stx).any (· == '\n') then
      match lineWords? stx ((← read).breaking.listFill) with
      | some ws => if ws.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
                   else return joinWords ws
      | none => return (← Lean4Fmt.Emit.verbatim stx)
    if a.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
    let mut d : Doc := .text "first"
    for g in a[1]!.getArgs do
      let ga := g.getArgs
      if ga.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
      let some bD ← armSeqDoc? walk ga[1]! | return (← Lean4Fmt.Emit.verbatim stx)
      d := d ++ .hardline ++ .text "|" ++ bD
    return d
  else if kind == `Lean.Parser.Tactic.match then
    -- tactic-match: head `match … with` single-line, arms `| pats =>` + body
    -- via the branch layout (mirrors induction alternatives)
    if a.size < 2 then return (← Lean4Fmt.Emit.verbatim stx)
    let mut head := ""
    for h : i in [0:a.size - 1] do
      let c := a[i]!
      -- first child's leading = the FORM's own leading — the enclosing seam
      -- owns it (see exampleDoc?); interior comments still bail
      let ownLead := if i == 0
        then Lean4Fmt.Syntax.countLineComments ((Lean4Fmt.Syntax.leading? c).getD "")
        else 0
      if Lean4Fmt.Syntax.countSubtreeLineComments c > ownLead then
        return (← Lean4Fmt.Emit.verbatim stx)
      let t := Lean4Fmt.Emit.canonTok c
      if t.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
      if !t.isEmpty then head := if head.isEmpty then t else head ++ " " ++ t
    if head.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
    let some altsWrap := a[a.size - 1]!.getArgs[0]? | return (← Lean4Fmt.Emit.verbatim stx)
    let mut d : Doc := .text head
    for alt in altsWrap.getArgs do
      let ala := alt.getArgs
      if ala.size != 4 then return (← Lean4Fmt.Emit.verbatim stx)
      if Lean4Fmt.Syntax.interiorHasLineComment alt then return (← Lean4Fmt.Emit.verbatim stx)
      let mut lhs := ""
      for c in ala.extract 0 3 do
        let t := Lean4Fmt.Emit.canonTok c
        if t.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
        if !t.isEmpty then lhs := if lhs.isEmpty then t else lhs ++ " " ++ t
      let some bD ← armSeqDoc? walk ala[3]! | return (← Lean4Fmt.Emit.verbatim stx)
      d := d ++ .hardline ++ .text lhs ++ bD
    return d
  else if kind == ``Lean.Parser.Tactic.unfold then
    -- ["unfold", idents, location?] — plain text, token-for-token
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    let mut line := ""
    for c in a do
      let t := (Lean4Fmt.Emit.tokenJoin? c).getD
        ((Lean4Fmt.Emit.bareSrc c).trimAscii.toString)
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
      let t := Lean4Fmt.Emit.canonTok c
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
      let lhsT := Lean4Fmt.Emit.canonTok alt.getArgs[0]!
      if lhsT.isEmpty || lhsT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
      let rhs := alt.getArgs[1]!.getArgs
      if rhs.size == 0 then
        -- arrow-less alt (`with | _ a h ih` — the body tactics are the
        -- induction's SIBLINGS at outer indent): the pattern line alone
        d := d ++ .hardline ++ .text lhsT
        continue
      if rhs.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
      let some seq := rhs[1]? | return (← Lean4Fmt.Emit.verbatim stx)
      -- arrow spelling from SOURCE (rhs[0] is the arrow atom; `=>` vs `↦`)
      let arrowT := ((rhs[0]?.map Lean4Fmt.Emit.bareSrc).getD "").trimAscii.toString
      let arrowT := if arrowT.isEmpty then "=>" else arrowT
      if seq.getKind == ``Lean.Parser.Term.syntheticHole
          || seq.getKind == ``Lean.Parser.Term.hole then
        -- hole RHS (`=> ?_`): the grammar's non-seq alternative — plain text
        let hT := Lean4Fmt.Emit.canonTok seq
        if hT.isEmpty || hT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
        d := d ++ .hardline ++ .text (lhsT ++ " " ++ arrowT ++ " " ++ hT)
        continue
      let some bD ← armSeqDoc? walk seq | return (← Lean4Fmt.Emit.verbatim stx)
      d := d ++ .hardline ++ .text (lhsT ++ " " ++ arrowT) ++ bD
    return d
  else if kind == `Lean.Parser.Tactic.«tacticNext_=>_» || kind == ``Lean.Parser.Tactic.case
      || kind == ``Lean.Parser.Tactic.allGoals || kind == `Lean.Parser.Tactic.tacticRepeat_ then
    match ← headBlockDoc? walk stx with
    | some d => return d
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == `Lean.Parser.Tactic.classical then
    -- [atom, tacticSeq] — the parser's block form: the sequence continues at
    -- the SAME column as the keyword (nest 0), NOT indented under it
    if a.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
    let kwTrail := (Lean4Fmt.Syntax.trailing? a[0]!).getD ""
    if !kwTrail.trimAscii.toString.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
    let kwT := (Lean4Fmt.Emit.bareSrc a[0]!).trimAscii.toString
    let some groups := tacticGroups? a[1]! | return (← Lean4Fmt.Emit.verbatim stx)
    -- ALWAYS the block form: the inline form (`classical exact h`) with a
    -- tactic doc that breaks internally re-parses to a DIFFERENT tree (the
    -- continuation lines fall out of the whitespace-sensitive block; error
    -- recovery can silently drop them — gate-caught on Denumerable)
    match ← seqGroupsDoc? walk groups true with
    | some body => return .text kwT ++ body
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == `Lean.Parser.Tactic.Conv.conv then
    match ← headBlockDoc? walk stx (conv := true) with
    | some d => return d
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == `Lean.calcTactic
      && (← read).breaking.preserveLineBreaks
      && (Lean4Fmt.Emit.bareSrc stx).any (· == '\n') then
    -- preserve: the author's step alignment is load-bearing
    return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == `Lean.calcTactic then
    -- basic calc: `calc` + steps, each step token-exact single-line, aligned
    -- under the first step (indent 5 = "calc ")
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    if a.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
    let steps := a[1]!.getArgs
    let mut ds : Array Doc := #[]
    for st in steps do
      let t := Lean4Fmt.Emit.canonTok st
      if t.isEmpty || t.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
      ds := ds.push (.text t)
    if ds.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
    let mut d : Doc := .text "calc " ++ ds[0]!
    for i in [1:ds.size] do
      d := d ++ .nest 5 (.hardline ++ ds[i]!)
    return d
  else if kind == `Lean.cdot then
    -- bullet: [cdotTk, tacticSeq] — first group rides the bullet line
    -- (`· intro l; exact h`), the rest one line per group at +2 under it
    if a.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
    if !((Lean4Fmt.Syntax.trailing? a[0]!).getD "").trimAscii.toString.isEmpty then
      return (← Lean4Fmt.Emit.verbatim stx)   -- comment on the `·` itself
    let tkT := (Lean4Fmt.Emit.bareSrc a[0]!).trimAscii.toString
    let some groups := tacticGroups? a[1]! | return (← Lean4Fmt.Emit.verbatim stx)
    let g0 := groups[0]!
    let lead0 := (Lean4Fmt.Syntax.leading? g0[0]!).getD ""
    if ((lead0.splitOn "\n").drop 1).dropLast.any (fun l => !l.trimAscii.toString.isEmpty) then
      return (← Lean4Fmt.Emit.verbatim stx)   -- comment lines between `·` and first tactic
    let some d0 ← groupDoc? walk g0 | return (← Lean4Fmt.Emit.verbatim stx)
    if Lean4Fmt.Doc.hasMultilineVerbatim d0 then return (← Lean4Fmt.Emit.verbatim stx)
    let trail0T := ((Lean4Fmt.Syntax.trailing? g0[g0.size - 1]!).getD "").trimAscii.toString
    if groups.size == 1 then
      if !trail0T.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)   -- owned by parent seam
      return .text (tkT ++ " ") ++ d0
    if trail0T.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let trail0 : Doc := if trail0T.isEmpty then .nil else .text (" " ++ trail0T)
    match ← seqGroupsDoc? walk (groups.extract 1 groups.size) true with
    | some rest => return .text (tkT ++ " ") ++ d0 ++ trail0 ++ .nest 2 rest
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == ``Lean.Parser.Tactic.tacticRfl || kind == ``Lean.Parser.Tactic.omega
      || kind == ``Lean.Parser.Tactic.decide || kind == ``Lean.Parser.Tactic.nativeDecide
      || kind == ``Lean.Parser.Tactic.constructor || kind == ``Lean.Parser.Tactic.tacticTrivial
      || kind == ``Lean.Parser.Tactic.contradiction || kind == ``Lean.Parser.Tactic.assumption
      || kind == ``Lean.Parser.Tactic.tacticAnd_intros || kind == ``Lean.Parser.Tactic.simpAll
      || kind == ``Lean.Parser.Tactic.intro || kind == ``Lean.Parser.Tactic.intros
      || kind == ``Lean.Parser.Tactic.split || kind == `Lean.Parser.Tactic.obtain
      || kind == `Lean.Parser.Tactic.rcases || kind == ``Lean.Parser.Tactic.show
      || kind == `Lean.Parser.Tactic.subst || kind == `Lean.Parser.Tactic.«tacticExists_,,»
      || kind == ``Lean.Parser.Tactic.change || kind == `«tacticBy_cases_:_»
      || kind == `Lean.Parser.Tactic.tacticSuffices_
      || kind == `Lean.Parser.Tactic.congr || kind == `Lean.Parser.Tactic.renameI
      || kind == `Lean.Parser.Tactic.bvDecide || kind == `Lean.Parser.Tactic.left
      || kind == `Lean.Parser.Tactic.right || kind == `Lean.Parser.Tactic.revert
      || kind == `Lean.Parser.Tactic.injection
      || kind == `Lean.Parser.Tactic.tacticInfer_instance
      || kind == `Lean.Parser.Tactic.tacticExfalso
      || kind == `Lean.Parser.Tactic.«tacticNomatch_,,»
      || kind == `Lean.Parser.Tactic.paren
      || kind == `Lean.Parser.Tactic.generalize then
    -- token-line tactics: single line, token-for-token, single-spaced
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    let mut line := ""
    for c in a do
      let t := (Lean4Fmt.Emit.tokenJoin? c).getD
        ((Lean4Fmt.Emit.bareSrc c).trimAscii.toString)
      if t.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
      if !t.isEmpty then line := if line.isEmpty then t else line ++ " " ++ t
    if line.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
    return .text line
  else if kind != ``Lean.Parser.Term.byTactic && kind != `Lean.Parser.Term.byTactic' then
    return (← Lean4Fmt.Emit.verbatim stx)
  else
  if a.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
  -- a comment on the `by` line itself has no home in the layout
  if !((Lean4Fmt.Syntax.trailing? a[0]!).getD "").trimAscii.toString.isEmpty then
    return (← Lean4Fmt.Emit.verbatim stx)
  -- the branch layout: a single clean flat group is width-aware (`by rfl`
  -- stays inline when it fits — flatWidth is exact, T2); anything else one
  -- line per group at +2
  match ← armSeqDoc? walk a[1]! with
  | some body => return .text "by" ++ body
  | none => return (← Lean4Fmt.Emit.verbatim stx)

end Lean4Fmt.Emit.Tactic
