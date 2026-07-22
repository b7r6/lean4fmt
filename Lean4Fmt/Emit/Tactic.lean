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

/-- Whether any node STARTING before `limit` is NEWLINE-SEMANTIC — a
    let-in-term (its newline IS the `in`), do, by, or comma-less structInst:
    flatten-joining such a head produces a DIFFERENT PARSE (gate-caught on
    Proofs.lean: a five-line suffices goal with a let-in-term flattened into
    an application). -/
private partial def headWsSensitive
                    (limit : Nat)
                    (s : Lean.Syntax)
                    : Bool :=

  match s with
  | .node _ k args =>
    (((s.getPos?.map (·.byteIdx)).getD limit) < limit
        && (k == ``Lean.Parser.Term.let || k == ``Lean.Parser.Term.letrec
            || k == ``Lean.Parser.Term.do
            || k == ``Lean.Parser.Term.byTactic
            || k == `Lean.Parser.Term.byTactic'
            || k == ``Lean.Parser.Term.structInst))
        || args.any (headWsSensitive limit)
  | _ => false

/-- The deepest final `by`-block descendant (last-child descent) — the
    position-split ports slice the head bytes before it. -/
private partial def lastByDescendant?
                    (s : Lean.Syntax)
                    : Option Lean.Syntax :=

  -- BOTH by kinds: tactic-position `by` is byTactic' (the prime variant) —
  -- matching only byTactic descended THROUGH a suffices' own by into a deep
  -- `<| by` tail and flattened the whole proof body into the "head"
  -- (gate-caught on Fixed + CosetCover, tokens, ~300 tokens reflowed)
  if s.getKind == ``Lean.Parser.Term.byTactic
      || s.getKind == `Lean.Parser.Term.byTactic' then
    some s
  else
    match (s.getArgs.filter
        (fun c => !(Lean4Fmt.Emit.bareSrc c).trimAscii.toString.isEmpty)).back? with
    | some c => lastByDescendant? c
    | none => none

/-- The items of a `tacticSeq` (unwrapping `tacticSeq1Indented`), grouped into
    LINES: an explicit `;` joins its neighbors into one group (rendered as one
    line, `t1; t2; t3`); empty separator slots (newlines) split groups. `none`
    on a trailing `;` or a structural surprise. -/
private def seqGroupsCore?
            (seqKind seq1Kind : Lean.Name)
            (seq : Lean.Syntax)
            : Option (Array (Array Lean.Syntax)) :=

  Id.run
    do
      if seq.getKind != seqKind then
        return none
      let s1 := (seq.getArgs[0]?).getD .missing
      if s1.getKind != seq1Kind then
        return none
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

private def tacticGroups?
            (seq : Lean.Syntax)
            : Option (Array (Array Lean.Syntax)) :=

  seqGroupsCore? ``Lean.Parser.Tactic.tacticSeq ``Lean.Parser.Tactic.tacticSeq1Indented seq

private def convGroups?
            (seq : Lean.Syntax)
            : Option (Array (Array Lean.Syntax)) :=

  seqGroupsCore? `Lean.Parser.Tactic.Conv.convSeq `Lean.Parser.Tactic.Conv.convSeq1Indented seq

/-- One `;`-joined run as a single line: items token-for-token joined by
    `"; "`. `none` when an item is multi-line, carries an interior comment, or
    an INTERMEDIATE item has trailing trivia content (a comment there would
    comment out the rest of the joined line). -/
private def groupText?
            (g : Array Lean.Syntax)
            : Option String :=

  Id.run do
    let mut txt := ""
    for j in [0:g.size] do
      let it := g[j]!
      if Lean4Fmt.Syntax.interiorHasLineComment it then
        return none
      let t := (Lean4Fmt.Emit.tokenJoin? it).getD ((Lean4Fmt.Emit.bareSrc it).trimAscii.toString)
      if t.isEmpty || t.any (· == '\n') then
        return none
      if j + 1 < g.size then
        let tr := (Lean4Fmt.Syntax.trailing? it).getD ""
        if !tr.trimAscii.toString.isEmpty || tr.any (· == '\n') then
          return none
      if j > 0 then
        let ld := (Lean4Fmt.Syntax.leading? it).getD ""
        if !ld.trimAscii.toString.isEmpty || ld.any (· == '\n') then
          return none
      txt := if txt.isEmpty then t else txt ++ "; " ++ t
    if txt.isEmpty then
      return none
    return some txt

/-- One group's doc: a single tactic walks (active layouts apply); a
    `;`-joined run rides as one text line. -/
private def groupDoc?
            (walk : Lean4Fmt.Emit.Walk)
            (g : Array Lean.Syntax)
            : Lean4Fmt.Emit.EmitM (Option Doc) := do

  if g.size == 1 then
    return some (← walk g[0]!)
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
    if !last && trailT.any (· == '\n') then
      return none
    if last && !lastOwned && !trailT.isEmpty then
      return none
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
            : Option (Array Doc) :=

  Id.run
    do
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
          if t.isEmpty || t.any (· == '\n') then
            return none
          items := items.push (.text t)
          lastComma := false
      if items.isEmpty || lastComma then
        return none
      return some items

/-- Generic token-line tactic: tokens single-spaced on ONE line, except
    bracket lists (`[a, b, c]` — simp lemmas, rw rules) which render as
    width-aware commaLists, so a long list BREAKS instead of forcing the whole
    tactic (and its enclosing body) verbatim. `none` on a multi-line piece
    outside a bracket list. -/
private partial def lineWords?
                    (stx : Lean.Syntax)
                    (fill : Bool := false)
                    : Option (Array Doc) :=

  Id.run do
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
      let hasBracket :=
        c.getArgs.any fun x => x.isAtom && (Lean4Fmt.Emit.bareSrc x).trimAscii.toString == "["
      if !t.any (· == '\n') && !hasBracket then
        out := out.push (.text ((Lean4Fmt.Emit.tokenJoin? c).getD t))
      else
        match lineWords? c fill with
        | some ws => out := out ++ ws
        | none => return none
      i := i + 1
    return some out

/-- Join line words with single spaces. -/
private def joinWords
            (ws : Array Doc)
            : Doc :=

  ws.foldl
    (fun d w => match d with
      | .nil => w
      | _    => d ++ .text " " ++ w)
    .nil

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
  if a.size < 2 then
    return none
  let mut head := ""
  for h : i in [0:a.size - 1] do
    let c := a[i]!
    -- first child's leading = the FORM's own leading — the enclosing seam
    -- owns it (see exampleDoc?); interior comments still bail
    let ownLead :=
      if i == 0 then Lean4Fmt.Syntax.countLineComments ((Lean4Fmt.Syntax.leading? c).getD "") else 0
    if Lean4Fmt.Syntax.countSubtreeLineComments c > ownLead then
      return none
    let t := Lean4Fmt.Emit.canonTok c
    if t.any (· == '\n') then
      return none
    if !t.isEmpty then head := if head.isEmpty then t else head ++ " " ++ t
  if head.isEmpty then
    return none
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
      if t.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
      if t.any (· == '\n') then
        -- a MULTI-LINE rule (a `<|` chain, an app with `(by …)` — 10K of
        -- the wide census) WALKS its TERM (rwRule = [←?, term]; the arrow
        -- reattaches as text): newlines are free inside the brackets, so an
        -- active rule doc breaking at its own group is parse-safe; only an
        -- opaque piece (bare verbatim / midline hazard) keeps the whole
        let (arrowT, term) :=
          if r.getKind == ``Lean.Parser.Tactic.rwRule && r.getArgs.size == 2 then
            ((((r.getArgs[0]?.map Lean4Fmt.Emit.bareSrc).getD "").trimAscii.toString),
              r.getArgs[1]!)
          else ("", r)
        let rDoc ← walk term
        if (match rDoc with | .verbatim _ _ => true | _ => false)
            || Lean4Fmt.Doc.hasMidlineReanchor rDoc then
          return (← Lean4Fmt.Emit.verbatim stx)
        ds := ds.push ((if arrowT.isEmpty then Doc.nil else .text (arrowT ++ " ")) ++ rDoc)
      else
        ds := ds.push (.text t)
      lastComma := false
    if ds.isEmpty || lastComma then return (← Lean4Fmt.Emit.verbatim stx)
    let locT := (a[3]?.map Lean4Fmt.Emit.canonTok).getD ""
    if locT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let locD : Doc := if locT.isEmpty then .nil else .text (" " ++ locT)
    -- fillList force-flattens items: a rule too wide to fit flat (a walked
    -- multi-line chain) must route to commaList, where its own group breaks
    let w := (← read).layout.lineWidth
    let anyWide := ds.any (fun d => ((Lean4Fmt.Doc.flatWidth d).getD (w + 1)) + 12 > w)
    -- a SINGLE wide rule glues the bracket and breaks inside its own group
    -- (`rw [long_app\n  arg …]`) — the vertical bracket is for lists
    if ds.size == 1 && anyWide then
      return .text "rw [" ++ ds[0]! ++ .text "]" ++ locD
    let listD := if (← read).breaking.listFill && !anyWide then Lean4Fmt.Doc.fillList "[" "]" ds
      else Lean4Fmt.Doc.commaList "[" "]" ds
    return .text "rw " ++ listD ++ locD
  else if kind == ``Lean.Parser.Tactic.tacticHave__
      || kind == `Lean.Parser.Tactic.tacticLet__ then
    -- ["have"/"let", letConfig, letDecl] — the doLet shape minus `mut`; the
    -- letDecl walks through the existing 5-slot machinery. NO blanket
    -- comment bail (the over-guard class): a `:= by` value's interior
    -- comments live at sequence seams the by machinery owns; comment-bearing
    -- HEADS go multi-line under canonTok and bail below; anything unowned
    -- is the comments gate's to catch (fallback, never damage).
    if a.size != 3 then return (← Lean4Fmt.Emit.verbatim stx)
    let kwT := (Lean4Fmt.Emit.bareSrc a[0]!).trimAscii.toString
    let cfgT := Lean4Fmt.Emit.canonTok a[1]!
    if cfgT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let dDoc ← walk a[2]!
    -- trust the letDecl path's OWN guards: a glued-by value's interior
    -- verbatims sit at sequence seams (an undispatched multi-line tactic
    -- inside `have h : T := by …` wrongly killed the whole have via the old
    -- blanket hasMultilineVerbatim — the 5.2KB mathlib tacticHave class);
    -- only a BARE whole-verbatim binding (the inner path bailed) stays out
    match dDoc with
    | .verbatim _ _ => return (← Lean4Fmt.Emit.verbatim stx)
    | _ =>
      return .text (kwT ++ " ") ++ (if cfgT.isEmpty then Doc.nil else .text (cfgT ++ " ")) ++ dDoc
  else if kind == `Lean.Parser.Tactic.obtain then
    -- ["obtain", pat?, (":" type)?, (":=" target,+)?] (Batteries rcases).
    -- The letIdDecl dual in tactic position: head token-for-token (pattern
    -- and type single-line), the := VALUE walked — `by`/`do` glues (its
    -- body brings the hardlines; interior verbatims sit at sequence
    -- seams), else flat-or-broken at +2. 32.2KB of the wide census rode
    -- verbatim through the token-line path (any newline bailed).
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    if a.size != 4 then return (← Lean4Fmt.Emit.verbatim stx)
    let mut head := (Lean4Fmt.Emit.bareSrc a[0]!).trimAscii.toString
    if head != "obtain" then return (← Lean4Fmt.Emit.verbatim stx)
    let patT := Lean4Fmt.Emit.canonTok a[1]!
    if patT.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    if !patT.isEmpty then head := head ++ " " ++ patT
    let tyT := Lean4Fmt.Emit.canonTok a[2]!
    let headDoc : Doc ← do
      if tyT.isEmpty then pure (.text head)
      else if !tyT.any (· == '\n') then pure (.text (head ++ " " ++ tyT))
      else
        -- multi-line TYPE: the broken-head recipe (the letIdDecl dual) —
        -- `obtain ⟨…⟩ :` + the walked type at +4, the := tail glues after
        -- the type's last line
        let ta := a[2]!.getArgs
        let tyNode :=
          if ta.size == 2 && (Lean4Fmt.Emit.bareSrc ta[0]!).trimAscii.toString == ":" then
            ta[1]!
          else .missing
        if tyNode.isMissing then return (← Lean4Fmt.Emit.verbatim stx)
        let tyDoc ← walk tyNode
        if (match tyDoc with | .verbatim _ _ => true | _ => false)
            || Lean4Fmt.Doc.hasMultilineVerbatim tyDoc then
          return (← Lean4Fmt.Emit.verbatim stx)
        pure (.text (head ++ " :") ++ .group (.nest 4 (.line ++ tyDoc)))
    let asgn := a[3]!
    if (Lean4Fmt.Emit.bareSrc asgn).trimAscii.toString.isEmpty then
      -- no := tail: the head IS the tactic
      return headDoc
    -- [":=", sepBy(casesTarget)]: exactly one target this round (a comma
    -- list of targets keeps the whole verbatim)
    if asgn.getArgs.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
    let targets := asgn.getArgs[1]!.getArgs
    if targets.size != 1 then return (← Lean4Fmt.Emit.verbatim stx)
    let v0 := targets[0]!
    -- a casesTarget wraps `(ident " : ")? term` — an unnamed one unwraps to
    -- its term; a NAMED target (`h : e`) keeps the wrapper and rides the
    -- bare-verbatim bails below
    let v :=
      if v0.getKind == `Lean.Parser.Tactic.casesTarget && v0.getArgs.size == 2
          && (Lean4Fmt.Emit.bareSrc v0.getArgs[0]!).trimAscii.toString.isEmpty then
        v0.getArgs[1]!
      else v0
    let vdoc ← walk v
    let vIsBlock := v.getKind == ``Lean.Parser.Term.do
        || v.getKind == ``Lean.Parser.Term.byTactic
    if vIsBlock then
      match vdoc with
      | .verbatim _ _ => return (← Lean4Fmt.Emit.verbatim stx)
      | _ => return headDoc ++ .text " := " ++ vdoc
    if Lean4Fmt.Doc.hasMultilineVerbatim vdoc then
      match vdoc with
      | .verbatim _ _ => return (← Lean4Fmt.Emit.verbatim stx)
      | _ =>
        if Lean4Fmt.Doc.hasMidlineReanchor vdoc then return (← Lean4Fmt.Emit.verbatim stx)
        return headDoc ++ .text " :=" ++ .nest 2 (.hardline ++ vdoc)
    return headDoc ++ .text " :=" ++ .group (.nest 2 (.line ++ vdoc))
  else if kind == ``Lean.Parser.Tactic.simp || kind == ``Lean.Parser.Tactic.simpAll
      || kind == `Lean.Parser.Tactic.dsimp || kind == `Lean.Parser.Tactic.simpa
      || kind == `Lean.Parser.Tactic.tacticRwa__
      || kind == `Mathlib.Tactic.tacticSimp_rw___ then
    -- simp family + rwa: tokens on one line, bracket lists as width-aware
    -- commaLists (a long lemma list breaks instead of going verbatim)
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    -- a multi-line tail AFTER the bracket list (`simpa […] using <multi-line
    -- term>`) must not naive-join: the space-join spaced a projection dot
    -- and the reparse minted an anonymous field (gate-caught on mathlib
    -- Determinant, tokens). Until the tail is walked, such tails ride
    -- verbatim; a multi-line bracket LIST alone still breaks via commaList.
    if ((Lean4Fmt.Emit.bareSrc stx).splitOn "]").getLast!.any (· == '\n') then
      return (← Lean4Fmt.Emit.verbatim stx)
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
      -- an arm the machinery can't carry rides verbatim WHOLE at its own
      -- hardline seam (the sequence-seam invariant makes the re-anchor
      -- deterministic) — the OTHER arms stay active. Whole-node bails here
      -- previously killed 22.9K of the wide census on the biggest sites.
      -- The arm's LEADING comment lines (`-- case docs` between arms) are
      -- OUR seam: place via the kit; unownable → whole verbatim (a per-arm
      -- verbatim would DROP the leading — bareSrc excludes it).
      let altLead := (Lean4Fmt.Syntax.leading? alt).getD ""
      let hasLeadContent :=
        ((altLead.splitOn "\n").drop 1).dropLast.any (fun l => !l.trimAscii.toString.isEmpty)
      let sep? : Option Doc :=
        if !hasLeadContent then some .hardline else Lean4Fmt.Emit.leadingSep? altLead
      let some sepD := sep? | return (← Lean4Fmt.Emit.verbatim stx)
      let armDoc? ← do
        if alt.getKind != ``Lean.Parser.Tactic.inductionAlt || alt.getArgs.size != 2 then
          pure none
        else
        let lhsT := Lean4Fmt.Emit.canonTok alt.getArgs[0]!
        if lhsT.isEmpty || lhsT.any (· == '\n') then pure none else
        let rhs := alt.getArgs[1]!.getArgs
        if rhs.size == 0 then
          -- arrow-less alt (`with | _ a h ih` — the body tactics are the
          -- induction's SIBLINGS at outer indent): the pattern line alone
          pure (some (Doc.text lhsT))
        else if rhs.size != 2 then pure none else
        match rhs[1]? with
        | none => pure none
        | some seq =>
          -- arrow spelling from SOURCE (rhs[0] is the arrow atom; `=>` vs `↦`)
          let arrowT := ((rhs[0]?.map Lean4Fmt.Emit.bareSrc).getD "").trimAscii.toString
          let arrowT := if arrowT.isEmpty then "=>" else arrowT
          -- `=> -- note` (the case-label idiom): the comment lives in the
          -- ARROW atom's trailing — own it on the arm-head line; ALL groups
          -- go below (nothing shares the line with a comment)
          let arrTrail := ((rhs[0]?.bind Lean4Fmt.Syntax.trailing?).getD "").trimAscii.toString
          if arrTrail.any (· == '\n') || (!arrTrail.isEmpty && !arrTrail.startsWith "--") then
            pure none
          else if seq.getKind == ``Lean.Parser.Term.syntheticHole
              || seq.getKind == ``Lean.Parser.Term.hole then
            -- hole RHS (`=> ?_`): the grammar's non-seq alternative — plain text
            let hT := Lean4Fmt.Emit.canonTok seq
            if hT.isEmpty || hT.any (· == '\n') || !arrTrail.isEmpty then pure none
            else pure (some (Doc.text (lhsT ++ " " ++ arrowT ++ " " ++ hT)))
          else if !arrTrail.isEmpty then
            let some groups := tacticGroups? seq | pure none
            match ← seqGroupsDoc? walk groups true with
            | some rest =>
              pure (some (.text (lhsT ++ " " ++ arrowT ++ " " ++ arrTrail) ++ .nest 2 rest))
            | none => pure none
          else
            match ← armSeqDoc? walk seq with
            | some bD => pure (some (.text (lhsT ++ " " ++ arrowT) ++ bD))
            | none => pure none
      match armDoc? with
      | some ad => d := d ++ sepD ++ ad
      | none => d := d ++ sepD ++ (← Lean4Fmt.Emit.verbatim alt)
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
    -- ws-sensitivity CLASS 1 (Emit/WsSensitivity): ALWAYS the block form —
    -- the inline form (`classical exact h`) with a tactic doc that breaks
    -- internally re-parses to a DIFFERENT tree (the continuation lines fall
    -- out of the whitespace-sensitive block; error recovery can silently
    -- drop them)
    match ← seqGroupsDoc? walk groups true with
    | some body => return .text kwT ++ body
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == `Lean.Parser.Tactic.Conv.conv then
    match ← headBlockDoc? walk stx (conv := true) with
    | some d => return d
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if (kind == `Lean.calcTactic || kind == `Lean.calc)
      && (← read).breaking.preserveLineBreaks
      && (Lean4Fmt.Emit.bareSrc stx).any (· == '\n') then
    -- preserve: the author's step alignment is load-bearing
    return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == `Lean.calcTactic || kind == `Lean.calc then
    -- ["calc", calcSteps[first, null[step*]]] — tactic AND term position
    -- share the node shape. Every step token-exact single-line → aligned
    -- under `calc ` (the flat form). Otherwise `calc` alone, steps one per
    -- line at +2: REL ` := ` PF with the proof WALKED (`:= by` glues, its
    -- body brings the hardlines; else flat-or-broken group at +2). A step
    -- the machinery can't carry rides verbatim WHOLE at its own hardline
    -- seam (sequence-seam invariant) — the other steps stay active.
    if Lean4Fmt.Syntax.interiorHasLineComment stx then return (← Lean4Fmt.Emit.verbatim stx)
    if a.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
    let sa := a[1]!.getArgs
    if sa.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
    let steps := #[sa[0]!] ++ sa[1]!.getArgs
    if steps.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
    -- flat decision PARSE-DERIVED per step (the flatten-first decision law:
    -- canonTok's bareSrc fallback is byte-dependent and flipped the decision
    -- pass-to-pass — gate-caught as fixed-point on the house calc), and
    -- width-guarded (+7 = "calc "/step alignment reserve)
    let w := (← read).layout.lineWidth
    let mut flats : Option (Array String) := some #[]
    for st in steps do
      -- head-ws law: a step containing by/do/let (newline-SEMANTIC kinds)
      -- must not flatten-join — joining two tactics without `;` reparses as
      -- an application (tree class, gate-caught on mathlib Divisors:
      -- `:= by apply f` + `simp […]` joined into `apply f simp […]`)
      if headWsSensitive (1 <<< 60) st then flats := none else
      match Lean4Fmt.Emit.tokenJoinFlat? st with
      | some t => if t.isEmpty || t.length + 7 > w then flats := none
                  else flats := flats.map (·.push t)
      | none => flats := none
    match flats with
    | some ts =>
      let mut d : Doc := .text "calc " ++ .text ts[0]!
      for i in [1:ts.size] do
        d := d ++ .nest 5 (.hardline ++ .text ts[i]!)
      return d
    | none => pure ()
    -- broken form: `calc ` + first step on the keyword line, later steps
    -- one per line at +2. Each step: REL walked (binop chains break at the
    -- continuation indent) ++ the proof part nested +4 — a by/do body at
    -- the STEP column would TERMINATE the step list on reparse (calcStep
    -- is column-sensitive), so proof blocks must sit strictly deeper.
    let mut body : Doc := .nil
    let mut first := true
    for st in steps do
      let stDoc? ← do
        let sargs := st.getArgs
        -- calcFirstStep = [rel, null[":=", pf]] ; calcStep = [rel, ":=", pf]
        let pf? : Option Lean.Syntax :=
          if sargs.size == 3 && (Lean4Fmt.Emit.bareSrc sargs[1]!).trimAscii.toString == ":=" then
            some sargs[2]!
          else if sargs.size == 2 then
            let asgn := sargs[1]!
            if asgn.getKind == Lean.nullKind && asgn.getArgs.size == 2
                && (Lean4Fmt.Emit.bareSrc asgn.getArgs[0]!).trimAscii.toString == ":=" then
              some asgn.getArgs[1]!
            else none
          else none
        match pf?, sargs[0]? with
        | some pf, some rel =>
          let relDoc ← walk rel
          if (match relDoc with | .verbatim _ _ => true | _ => false)
              || Lean4Fmt.Doc.hasMultilineVerbatim relDoc then pure none else
          let pfDoc ← walk pf
          if pf.getKind == ``Lean.Parser.Term.do || pf.getKind == ``Lean.Parser.Term.byTactic then
            match pfDoc with
            | .verbatim _ _ => pure none
            | _ => pure (some (relDoc ++ .nest 4 (.text " := " ++ pfDoc)))
          else if Lean4Fmt.Doc.hasMultilineVerbatim pfDoc then pure none
          else pure (some (relDoc ++ .nest 4 (.text " :=" ++ .group (.line ++ pfDoc))))
        | _, _ => pure none
      match stDoc?, first with
      | some d, true => body := .text "calc " ++ d
      | some d, false => body := body ++ .nest 2 (.hardline ++ d)
      | none, true =>
        -- a bailed FIRST step would glue verbatim mid-line after `calc ` —
        -- the master fixed-point hazard: whole-calc verbatim
        return (← Lean4Fmt.Emit.verbatim stx)
      | none, false => body := body ++ .nest 2 (.hardline ++ (← Lean4Fmt.Emit.verbatim st))
      first := false
    return body
  else if kind == `Lean.cdot then
    -- bullet: [cdotTk, tacticSeq] — first group rides the bullet line
    -- (`· intro l; exact h`), the rest one line per group at +2 under it
    if a.size != 2 then return (← Lean4Fmt.Emit.verbatim stx)
    -- a same-line comment on the `·` itself (`· -- the goal name` — the
    -- mathlib case-label idiom) is OUR zone: it rides the bullet line and
    -- ALL groups go below at +2 (nothing shares the bullet line with it)
    let tkTrail := ((Lean4Fmt.Syntax.trailing? a[0]!).getD "").trimAscii.toString
    if tkTrail.startsWith "--" && !tkTrail.any (· == '\n') then
      let tkT := (Lean4Fmt.Emit.bareSrc a[0]!).trimAscii.toString
      let some groups := tacticGroups? a[1]! | return (← Lean4Fmt.Emit.verbatim stx)
      match ← seqGroupsDoc? walk groups true with
      | some rest =>
        return .align (.text (tkT ++ " " ++ tkTrail) ++ .nest 2 rest)
      | none => return (← Lean4Fmt.Emit.verbatim stx)
    if !tkTrail.isEmpty then
      return (← Lean4Fmt.Emit.verbatim stx)   -- non-comment surprise on the `·`
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
      -- ws-sensitivity CLASS 2 (Emit/WsSensitivity): d0's interior breaks
      -- must anchor at the bullet CONTENT column, not the bullet line's
      -- indent — two columns shallow re-parses the glued block's lines as
      -- bullet-seq SIBLINGS; `.align` is the cure
      return .text (tkT ++ " ") ++ .align d0
    if trail0T.any (· == '\n') then return (← Lean4Fmt.Emit.verbatim stx)
    let trail0 : Doc := if trail0T.isEmpty then .nil else .text (" " ++ trail0T)
    match ← seqGroupsDoc? walk (groups.extract 1 groups.size) true with
    | some rest =>
      -- ws-sensitivity CLASS 2 (Emit/WsSensitivity): the rest-groups' nest
      -- must anchor at the BULLET column, not the line indent — glued
      -- placements (`<;> · intro` + a second tactic) otherwise land the
      -- continuation SHALLOWER than the bullet content and the reparse's
      -- recovery silently drops it (gate-caught on mathlib
      -- ArchimedeanDensely, tokens). The outer `.align` re-anchors the whole
      -- bullet at its own start column; at line start it is a no-op.
      return .align (.text (tkT ++ " ") ++ .align d0 ++ trail0 ++ .nest 2 rest)
    | none => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == `Lean.Parser.Tactic.tacticSuffices_
      && (Lean4Fmt.Emit.bareSrc stx).any (· == '\n') then
    -- POSITION-SPLIT port: `suffices h : T by tac` / `have h : T := by tac`
    -- — find the final by-block descendant (last-child descent), slice the
    -- HEAD bytes positionally (no shape enumeration), flatten-join the head,
    -- glue the by (members at sequence seams). Heads carrying strings or
    -- comments, non-by tails, and whole-verbatim bys fall back; by-INTERIOR
    -- comments are the by emitter's own seam business.
    let bare := Lean4Fmt.Emit.bareSrc stx
    match lastByDescendant? stx, stx.getPos?, (lastByDescendant? stx).bind (·.getPos?) with
    | some byN, some p0, some pb =>
      -- TAIL-EXACTNESS: the by must END the tactic — a mid-node `(by …)`
      -- with trailing bytes would lose them to the slice
      if byN.getTailPos? != stx.getTailPos? then return (← Lean4Fmt.Emit.verbatim stx)
      if headWsSensitive pb.byteIdx stx then return (← Lean4Fmt.Emit.verbatim stx)
      let headB := (String.fromUTF8? (bare.toUTF8.extract 0 (pb.byteIdx - p0.byteIdx))).getD ""
      if headB.isEmpty || headB.toList.any (· == '"')
          || (headB.splitOn "--").length > 1 || (headB.splitOn "/-").length > 1 then
        return (← Lean4Fmt.Emit.verbatim stx)
      let headF := String.intercalate " "
        (((headB.split (fun c => c == '\n' || c == ' ' || c == '\t')).toList.map
            (·.toString)).filter (fun s => !s.isEmpty))
      if headF.isEmpty then return (← Lean4Fmt.Emit.verbatim stx)
      let byDoc ← walk byN
      match byDoc with
      | .verbatim _ _ => return (← Lean4Fmt.Emit.verbatim stx)
      | _ => return .text (headF ++ " ") ++ byDoc
    | _, _, _ => return (← Lean4Fmt.Emit.verbatim stx)
  else if kind == ``Lean.Parser.Tactic.tacticRfl || kind == ``Lean.Parser.Tactic.omega
      || kind == ``Lean.Parser.Tactic.decide || kind == ``Lean.Parser.Tactic.nativeDecide
      || kind == ``Lean.Parser.Tactic.constructor || kind == ``Lean.Parser.Tactic.tacticTrivial
      || kind == ``Lean.Parser.Tactic.contradiction || kind == ``Lean.Parser.Tactic.assumption
      || kind == ``Lean.Parser.Tactic.tacticAnd_intros || kind == ``Lean.Parser.Tactic.simpAll
      || kind == ``Lean.Parser.Tactic.intro || kind == ``Lean.Parser.Tactic.intros
      || kind == ``Lean.Parser.Tactic.split
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
