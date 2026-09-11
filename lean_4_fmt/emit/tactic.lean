/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // EMIT // Tactic
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Open-recursion emitter for the Tactic category (doc/design.md §6): the `by`
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

import lean_4_fmt.emit.monad
import lean_4_fmt.emit.tokens
import lean_4_fmt.emit.do_notation

namespace Lean4Fmt.Emit.Tactic

open Lean Lean4Fmt.Doc

/-- Whether any node STARTING before `limit` is NEWLINE-SEMANTIC — a
    let-in-term (its newline IS the `in`), do, by, or comma-less structInst:
    flatten-joining such a head produces a DIFFERENT PARSE (gate-caught on
    Proofs.lean: a five-line suffices goal with a let-in-term flattened into
    an application). -/
private partial
def head_ws_sensitive (limit : Nat) (source : Lean.Syntax) : Bool :=
  match source with
  | .node _ kind args =>
    (
      ((source.getPos?.map (·.byteIdx)).getD limit) < limit
          && (
            kind == ``Lean.Parser.Term.let || kind == ``Lean.Parser.Term.letrec
                || kind == ``Lean.Parser.Term.do
                || kind == ``Lean.Parser.Term.byTactic
                || kind == `Lean.Parser.Term.byTactic'
                || kind == ``Lean.Parser.Term.structInst
          )
    )
        || args.any (head_ws_sensitive limit)
  | _ => false

/-- The deepest final `by`-block descendant (last-child descent) — the
    position-split ports slice the head bytes before it. -/
private partial
def last_by_descendant? (source : Lean.Syntax) : Option Lean.Syntax :=

  -- BOTH by kinds: tactic-position `by` is byTactic' (the prime variant) —
  -- matching only byTactic descended THROUGH a suffices' own by into a deep
  -- `<| by` tail and flattened the whole proof body into the "head"
  -- (gate-caught on Fixed + CosetCover, tokens, ~300 tokens reflowed)
  if source.getKind == ``Lean.Parser.Term.byTactic
      || source.getKind == `Lean.Parser.Term.byTactic' then
    some source
  else
    match (source.getArgs.filter
        (fun child => !(Lean4Fmt.Emit.bare_src child).trimAscii.toString.isEmpty)).back? with
    | some headChar => last_by_descendant? headChar
    | none => none

/-- The items of a `tacticSeq` (unwrapping `tacticSeq1Indented`), grouped into
    LINES: an explicit `;` joins its neighbors into one group (rendered as one
    line, `t1; t2; t3`); empty separator slots (newlines) split groups. `none`
    on a trailing `;` or a structural surprise. -/
private
structure seq_group_state where
  groups   : Array (Array Lean.Syntax) := #[]
  current  : Array Lean.Syntax := #[]
  joinNext : Bool := false

private
def seq_groups_core?
    (seqKind seq1Kind : Lean.Name)
    (seq : Lean.Syntax)
    : Option (Array (Array Lean.Syntax)) :=
  Id.run
    do
      if seq.getKind != seqKind then
        return none
      let sequence := (seq.getArgs[0]?).getD .missing
      if sequence.getKind != seq1Kind then
        return none
      let some inner := sequence.getArgs[0]? | return none
      let mut state : seq_group_state := {}
      for child in inner.getArgs do
        if (Lean4Fmt.Emit.bare_src child).trimAscii.toString.isEmpty then continue -- newline slot
        if child.isAtom then
          if (Lean4Fmt.Emit.bare_src child).trimAscii.toString == ";" then
            if state.current.isEmpty then
              return none
            state := { state with joinNext := true }
            continue
          else
            return none
        if state.joinNext then
          state := { state with current := state.current.push child, joinNext := false }
        else
          let groups :=
            if state.current.isEmpty then state.groups else state.groups.push state.current
          state := { state with groups, current := #[child] }
      if state.joinNext then
        return none -- dangling `;`
      let groups := if state.current.isEmpty then state.groups else state.groups.push state.current
      if groups.isEmpty then
        return none
      return some groups

private
def tactic_groups? (seq : Lean.Syntax) : Option (Array (Array Lean.Syntax)) :=
  seq_groups_core? ``Lean.Parser.Tactic.tacticSeq ``Lean.Parser.Tactic.tacticSeq1Indented seq

private
def conv_groups? (seq : Lean.Syntax) : Option (Array (Array Lean.Syntax)) :=
  seq_groups_core? `Lean.Parser.Tactic.Conv.convSeq `Lean.Parser.Tactic.Conv.convSeq1Indented seq

/-- One `;`-joined run as a single line: items token-for-token joined by
    `"; "`. `none` when an item is multi-line, carries an interior comment, or
    an INTERMEDIATE item has trailing trivia content (a comment there would
    comment out the rest of the joined line). -/
private
def group_text? (groupValue : Array Lean.Syntax) : Option String :=
  Id.run do
    let mut txt := ""
    for idx in [0:groupValue.size] do
      let item := groupValue[idx]!
      if Lean4Fmt.Syntax.interior_has_line_comment item then
        return none
      let text :=
        (Lean4Fmt.Emit.token_join? item).getD ((Lean4Fmt.Emit.bare_src item).trimAscii.toString)
      if text.isEmpty || text.any (· == '\n') then
        return none
      if idx + 1 < groupValue.size then
        let trailing := (Lean4Fmt.Syntax.trailing? item).getD ""
        if !trailing.trimAscii.toString.isEmpty || trailing.any (· == '\n') then
          return none
      if idx > 0 then
        let leading := (Lean4Fmt.Syntax.leading? item).getD ""
        if !leading.trimAscii.toString.isEmpty || leading.any (· == '\n') then
          return none
      txt := if txt.isEmpty then text else txt ++ "; " ++ text
    if txt.isEmpty then
      return none
    return some txt

/-- One group's doc: a single tactic walks (active layouts apply); a
    `;`-joined run rides as one text line. -/
private
def group_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (groupValue : Array Lean.Syntax)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  if groupValue.size == 1 then
    return some (← walk groupValue[0]!)
  return (group_text? groupValue).map Doc.text

/-- The seam loop over groups (mirrors `DoNotation.seqLinesDoc?`): each group
    one line, its leading trivia placed structurally, same-line trailing
    comments re-appended (leading of the group's FIRST item, trailing of its
    LAST). -/
private
def seq_groups_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (groups : Array (Array Lean.Syntax))
    (lastOwned : Bool)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let mut body : Doc := .nil
  for h : idx in [0:groups.size] do
    let group := groups[idx]
    let first := group[0]!
    let glast := group[group.size - 1]!
    let trailT := ((Lean4Fmt.Syntax.trailing? glast).getD "").trimAscii.toString
    let last := idx + 1 == groups.size
    if !last && trailT.any (· == '\n') then
      return none
    if last && !lastOwned && !trailT.isEmpty then
      return none
    let trailDoc : Doc := if !last && !trailT.isEmpty then .text (" " ++ trailT) else .nil
    let lead := (Lean4Fmt.Syntax.leading? first).getD ""
    -- first group: comment-free blank runs after the block opener are LAYOUT
    -- (dropped; the style re-adds its own) — see seqLinesDoc?
    let sep ← if idx == 0 && lead.toList.all (·.isWhitespace) then pure Doc.hardline
    else
      match Lean4Fmt.Emit.leading_sep? lead with
      | some textValue => pure textValue
      | none => return none
    let some gDoc ← group_doc? walk group | return none
    body := body ++ sep ++ gDoc ++ trailDoc
  return some body

/-- An arm body (`induction … with | alt => <tactics>`): a single clean flat
    tactic goes width-aware after the `=>` (inline when it fits); anything else
    one tactic per line at +2. `none` when the sequence has no safe layout. -/
private
def arm_seq_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (seq : Lean.Syntax)
    (conv : Bool := false)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let some groups := (if conv then conv_groups? seq else tactic_groups? seq) | return none
  if groups.size == 1 then
    let lead := (Lean4Fmt.Syntax.leading? groups[0]![0]!).getD ""
    -- blank-only intervening lines are LAYOUT (seqGroupsDoc drops them, re-adds
    -- the style's own break) — they must NOT divert a single clean group off the
    -- inline path. If they did, the dropped blank flips the flatten decision
    -- pass-to-pass: break (blank present ⇒ flatWidth none), blank gone, then
    -- inline — a 2-step convergence the 1-step gate rejects. A COMMENT line is
    -- content and still forces the structural (broken) placement below.
    let plainLead := (((lead.splitOn "\n").drop 1).dropLast).all (·.trimAscii.toString.isEmpty)
    let srcInline := !lead.any (· == '\n')
    if plainLead && (!(← read).breaking.preserveLineBreaks || srcInline) then
      let some tDoc ← group_doc? walk groups[0]! | return none
      if (Lean4Fmt.Doc.flat_width tDoc).isSome && !Lean4Fmt.Doc.hasMultilineVerbatim tDoc then
        return some (.group (.nest 2 (.line ++ tDoc)))
  match ← seq_groups_doc? walk groups true with
  | some body => return some (.nest 2 body)
  | none => return none

/-- Items of a bracket-list slice (`a, b, c` between `[` and `]`): comma atoms
    skipped, one level of null nesting flattened; `none` on a multi-line item. -/
private
def list_items? (slice : Array Lean.Syntax) : Option (Array Doc) :=
  Id.run
    do
      let mut items : Array Doc := #[]
      -- an authored TRAILING comma (`[a, b,]`) has no slot in the rebuilt list
      -- (commas go BETWEEN items) — bail rather than drop the token (gate-caught)
      let mut lastComma := false
      for child in slice do
        if child.isAtom then
          if (Lean4Fmt.Emit.bare_src child).trimAscii.toString == "," then lastComma := true
          continue
        let subs := if child.getKind == Lean.nullKind then child.getArgs else #[child]
        for descendant in subs do
          if descendant.isAtom then
            if (Lean4Fmt.Emit.bare_src descendant).trimAscii.toString == "," then lastComma := true
            continue
          let text := Lean4Fmt.Emit.canon_tok descendant
          if text.isEmpty || text.any (· == '\n') then
            return none
          items := items.push (.text text)
          lastComma := false
      if items.isEmpty || lastComma then
        return none
      return some items

/-- Generic token-line tactic: tokens single-spaced on ONE line, except
    bracket lists (`[a, b, c]` — simp lemmas, rw rules) which render as
    width-aware commaLists, so a long list BREAKS instead of forcing the whole
    tactic (and its enclosing body) verbatim. `none` on a multi-line piece
    outside a bracket list. -/
private
def closing_bracket? (args : Array Lean.Syntax) (start : Nat) : Option Nat :=
  let rec loop (idx : Nat) : Option Nat :=
    if h : idx < args.size then
      if args[idx].isAtom && (Lean4Fmt.Emit.bare_src args[idx]).trimAscii.toString == "]" then
        some idx
      else
        loop (idx + 1)
    else
      none
  loop start

private
structure line_words_state where
  docs : Array Doc := #[]
  idx  : Nat := 0

private partial
def line_words? (stx : Lean.Syntax) (fill : Bool := false) : Option (Array Doc) :=
  Id.run do
    let args := stx.getArgs
    let mut state : line_words_state := {}
    while state.idx < args.size do
      let child := args[state.idx]!
      if child.isAtom && (Lean4Fmt.Emit.bare_src child).trimAscii.toString == "[" then
        let some closeIdx := closing_bracket? args (state.idx + 1) | return none
        let some items := list_items? (args.extract (state.idx + 1) closeIdx) | return none
        let docs :=
          state.docs.push
            (
              if fill then
                Lean4Fmt.Doc.fill_list "[" "]" items
              else
                Lean4Fmt.Doc.comma_list "[" "]" items
            )
        state := { docs, idx := closeIdx + 1 }
        continue
      let text := (Lean4Fmt.Emit.bare_src child).trimAscii.toString
      if text.isEmpty then
        state := { state with idx := state.idx + 1 }
        continue
      if child.getKind == ``Lean.Parser.Tactic.location then
        let location := Lean4Fmt.Emit.canon_tok child
        if location.isEmpty || location.any (· == '\n') then
          return none
        state := { state with docs := state.docs.push (.text location), idx := state.idx + 1 }
        continue
      let hasBracket :=
        child.getArgs.any fun descendant =>
          descendant.isAtom && (Lean4Fmt.Emit.bare_src descendant).trimAscii.toString == "["
      if !text.any (· == '\n') && !hasBracket then
        state :=
          { state with
            docs := state.docs.push (.text ((Lean4Fmt.Emit.token_join? child).getD text)) }
      else
        match line_words? child fill with
        | some words => state := { state with docs := state.docs ++ words }
        | none => return none
      state := { state with idx := state.idx + 1 }
    return some state.docs

/-- Find the `using <term>` tail of a simpa-family tactic (a null node
    `["using"/"using!", term]`, searched shallowly), returning the tactic with
    the TERM pruned (the `using` atom stays) and the term itself. `none` when
    no such tail exists. -/
private partial
def prune_using? (source : Lean.Syntax) : Option (Lean.Syntax × Lean.Syntax) :=
  match source with
  | .node info kind args => visitNode info kind args
  | _ => none

  where
    visitNode (info : Lean.SourceInfo) (kind : Lean.SyntaxNodeKind) (args : Array Lean.Syntax) :
        Option (Lean.Syntax × Lean.Syntax) := Id.run do
      for h : idx in [0:args.size] do
        let child := args[idx]
        if child.getKind == `null && child.getArgs.size == 2 then
          if let .atom _ value := child.getArgs[0]! then
            if value.startsWith "using" then
              let term := child.getArgs[1]!
              let pruned :=
                Lean.Syntax.node info kind (args.set! idx (Lean.mkNullNode #[child.getArgs[0]!]))
              return some (pruned, term)
        match prune_using? child with
        | some (prunedChild, term) =>
          return some (Lean.Syntax.node info kind (args.set! idx prunedChild), term)
        | none => pure ()
      return none

/-- Join line words with single spaces. -/
private
def join_words (whitespace : Array Doc) : Doc :=
  whitespace.foldl
    (
      fun document word => match document with
        | .nil => word
        | _    => document ++ .text " " ++ word
    )
    .nil

/-- A head-block tactic (`next h => …`, `case foo => …`, `all_goals …`,
    `repeat …`, `conv at x => …`): head tokens single-line joined, the body
    sequence via the branch layout (inline when a single clean flat group
    fits; else one line per group at +2). The body's inter-group comments ride
    the seam loop; comments in the HEAD have no home → `none`. -/
private
def head_block_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    (conv : Bool := false)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let args := stx.getArgs
  if args.size < 2 then
    return none
  let mut head := ""
  for h : idx in [0:args.size - 1] do
    let child := args[idx]!
    -- first child's leading = the FORM's own leading — the enclosing seam
    -- owns it (see exampleDoc?); interior comments still bail
    let ownLead :=
      if idx == 0 then
        Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? child).getD "")
      else
        0
    if Lean4Fmt.Syntax.count_subtree_line_comments child > ownLead then
      return none
    let text := Lean4Fmt.Emit.canon_tok child
    if text.any (· == '\n') then
      return none
    if !text.isEmpty then head := if head.isEmpty then text else head ++ " " ++ text
  if head.isEmpty then
    return none
  let some branchDoc ← arm_seq_doc? walk args[args.size - 1]! conv | return none
  return some (.text head ++ branchDoc)

private
inductive Dispatch where
  | handled (doc : Doc)
  | unhandled

private
def fallback (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Dispatch := do
  return .handled (← Lean4Fmt.Emit.verbatim stx)

private
def dispatch_exact
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  let kind := stx.getKind
  if kind != ``Lean.Parser.Tactic.exact && kind != ``Lean.Parser.Tactic.apply
      && kind != ``Lean.Parser.Tactic.refine then
    return .unhandled
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← fallback stx)
  let args := stx.getArgs
  if args.size != 2 then
    return (← fallback stx)
  let source := Lean4Fmt.Emit.bare_src stx
  if source.any (· == '\n') && (source.splitOn "⟨").length > 1 then
    return (← fallback stx)
  let keyword := (Lean4Fmt.Emit.bare_src args[0]!).trimAscii.toString
  let termDoc ← walk args[1]!
  let layout : Doc := .text keyword ++ .group (.nest 2 (.line ++ termDoc))
  if (match termDoc with | .verbatim _ _ => true | _ => false)
      || Lean4Fmt.Doc.has_midline_reanchor layout then
    return (← fallback stx)
  return .handled layout

private
def dispatch_binding
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  let kind := stx.getKind
  if kind != ``Lean.Parser.Tactic.tacticHave__
      && kind != `Lean.Parser.Tactic.tacticLet__
      && kind != `Lean.Parser.Tactic.tacticHaveI__
      && kind != `Lean.Parser.Tactic.tacticLetI__
      && kind != ``Lean.Parser.Tactic.replace then
    return .unhandled
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← fallback stx)
  let args := stx.getArgs
  if args.size != 3 && args.size != 2 then
    return (← fallback stx)
  let keyword := (Lean4Fmt.Emit.bare_src args[0]!).trimAscii.toString
  let config := if args.size == 3 then Lean4Fmt.Emit.canon_tok args[1]! else ""
  if config.any (· == '\n') then
    return (← fallback stx)
  let declDoc ← walk args[args.size - 1]!
  if !(declDoc matches .verbatim _ _)
      && !Lean4Fmt.Doc.hasMultilineVerbatim declDoc
      && !Lean4Fmt.Doc.has_midline_reanchor declDoc then
    return .handled
      (.text (keyword ++ " ") ++ (if config.isEmpty then Doc.nil else .text (config ++ " "))
          ++ declDoc)
  return (← fallback stx)

private
def dispatch_simp
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  let kind := stx.getKind
  if kind != ``Lean.Parser.Tactic.simp && kind != ``Lean.Parser.Tactic.simpAll
      && kind != `Lean.Parser.Tactic.dsimp && kind != `Lean.Parser.Tactic.simpa
      && kind != `Lean.Parser.Tactic.simpaUsingBang
      && kind != `Lean.Parser.Tactic.tacticRwa__
      && kind != `Mathlib.Tactic.tacticSimp_rw___ then
    return .unhandled
  if ((Lean4Fmt.Emit.bare_src stx).splitOn ").").length > 1 then
    return (← fallback stx)
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← fallback stx)
  if ((Lean4Fmt.Emit.bare_src stx).splitOn "]").getLast!.any (· == '\n') then
    let some (pruned, term) := prune_using? stx | return (← fallback stx)
    if !(Lean4Fmt.Emit.bare_src term).any (· == '\n') then
      return (← fallback stx)
    let some words := line_words? pruned ((← read).breaking.listFill) | return (← fallback stx)
    if words.isEmpty then
      return (← fallback stx)
    let termDoc ← walk term
    let layout := join_words words ++ .group (.nest 2 (.line ++ termDoc))
    if (match termDoc with | .verbatim _ _ => true | _ => false)
        || Lean4Fmt.Doc.has_midline_reanchor layout then
      return (← fallback stx)
    return .handled layout
  let some words := line_words? stx ((← read).breaking.listFill) | return (← fallback stx)
  if words.isEmpty then
    return (← fallback stx)
  return .handled (join_words words)

private
def dispatch_unfold (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Dispatch := do
  if stx.getKind != ``Lean.Parser.Tactic.unfold then
    return .unhandled
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← fallback stx)
  let mut line := ""
  for child in stx.getArgs do
    let token :=
      (Lean4Fmt.Emit.token_join? child).getD ((Lean4Fmt.Emit.bare_src child).trimAscii.toString)
    if token.any (· == '\n') then
      return (← fallback stx)
    if !token.isEmpty then line := if line.isEmpty then token else line ++ " " ++ token
  if line.isEmpty then
    return (← fallback stx)
  return .handled (.text line)

private
structure chain_state where
  elements : Array Lean.Syntax := #[]
  cursor   : Lean.Syntax
  head     : Doc := .nil
  tail     : Doc := .nil

private
def dispatch_chain
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  if stx.getKind != `Lean.Parser.Tactic.«tactic_<;>_» then
    return .unhandled
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← fallback stx)
  let mut state : chain_state := { cursor := stx }
  for _ in [0:64] do
    if state.cursor.getKind == `Lean.Parser.Tactic.«tactic_<;>_»
        && state.cursor.getArgs.size == 3 then
      state :=
        { state with
          elements := state.elements.push state.cursor.getArgs[2]!
          cursor := state.cursor.getArgs[0]! }
  if state.cursor.getKind == `Lean.Parser.Tactic.«tactic_<;>_» then
    return (← fallback stx)
  let chain := (state.elements.push state.cursor).reverse
  for h : idx in [0:chain.size] do
    let elementDoc ← walk chain[idx]
    if Lean4Fmt.Doc.hasMultilineVerbatim elementDoc then
      return (← fallback stx)
    if idx == 0 then state := { state with head := elementDoc }
    else state := { state with tail := state.tail ++ .group (.line ++ .text "<;> " ++ elementDoc) }
  return .handled (state.head ++ .nest 2 state.tail)

private
def dispatch_first
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  if stx.getKind != `Lean.Parser.Tactic.first then
    return .unhandled
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← fallback stx)
  if !(Lean4Fmt.Emit.bare_src stx).any (· == '\n') then
    let some words := line_words? stx ((← read).breaking.listFill) | return (← fallback stx)
    if words.isEmpty then
      return (← fallback stx)
    return .handled (join_words words)
  let args := stx.getArgs
  if args.size != 2 then
    return (← fallback stx)
  let mut doc : Doc := .text "first"
  for group in args[1]!.getArgs do
    let groupArgs := group.getArgs
    if groupArgs.size != 2 then
      return (← fallback stx)
    let some body ← arm_seq_doc? walk groupArgs[1]! | return (← fallback stx)
    doc := doc ++ .hardline ++ .text "|" ++ body
  return .handled doc

private
def match_head? (stx : Lean.Syntax) : Option (String × Lean.Syntax) := do
  let args := stx.getArgs
  if args.size < 2 then none
  else
    let head ← Id.run do
      let mut head := ""
      for h : idx in [0:args.size - 1] do
        let child := args[idx]!
        let ownLead :=
          if idx == 0 then
            Lean4Fmt.Syntax.count_line_comments ((Lean4Fmt.Syntax.leading? child).getD "")
          else
            0
        if Lean4Fmt.Syntax.count_subtree_line_comments child > ownLead then
          return none
        let token := Lean4Fmt.Emit.canon_tok child
        if token.any (· == '\n') then
          return none
        if !token.isEmpty then head := if head.isEmpty then token else head ++ " " ++ token
      if head.isEmpty then none
      else some head
    let alternatives ← args[args.size - 1]!.getArgs[0]?
    return (head, alternatives)

private
def dispatch_match
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  if stx.getKind != `Lean.Parser.Tactic.match then
    return .unhandled
  let some (head, alternatives) := match_head? stx | return (← fallback stx)
  let mut doc : Doc := .text head
  for alternative in alternatives.getArgs do
    let args := alternative.getArgs
    if args.size != 4 || Lean4Fmt.Syntax.interior_has_line_comment alternative then
      return (← fallback stx)
    let lhs? : Option String :=
      Id.run do
        let mut lhs := ""
        for child in args.extract 0 3 do
          let token := Lean4Fmt.Emit.canon_tok child
          if token.any (· == '\n') then
            return none
          if !token.isEmpty then lhs := if lhs.isEmpty then token else lhs ++ " " ++ token
        return some lhs
    let some lhs := lhs? | return (← fallback stx)
    let some body ← arm_seq_doc? walk args[3]! | return (← fallback stx)
    doc := doc ++ .hardline ++ .text lhs ++ body
  return .handled doc

private
def rw_rule_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (rule : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let token := Lean4Fmt.Emit.canon_tok rule
  if token.isEmpty then
    return none
  if !token.any (· == '\n') then
    return some (.text token)
  let (arrow, term) :=
    if rule.getKind == ``Lean.Parser.Tactic.rwRule && rule.getArgs.size == 2 then
      (
        (((rule.getArgs[0]?.map Lean4Fmt.Emit.bare_src).getD "").trimAscii.toString),
        rule.getArgs[1]!
      )
    else
      ("", rule)
  let termDoc ← walk term
  if (match termDoc with | .verbatim _ _ => true | _ => false)
      || Lean4Fmt.Doc.has_midline_reanchor termDoc then
    return none
  return some ((if arrow.isEmpty then Doc.nil else .text (arrow ++ " ")) ++ termDoc)

private
structure rw_rules where
  docs      : Array Doc := #[]
  lastComma : Bool := false

private
def rw_rules?
    (walk : Lean4Fmt.Emit.Walk)
    (rules : Array Lean.Syntax)
    : Lean4Fmt.Emit.emit_m (Option (Array Doc)) := do
  let mut state : rw_rules := {}
  for rule in rules do
    if rule.isAtom then
      if (Lean4Fmt.Emit.bare_src rule).trimAscii.toString == "," then
        state := { state with lastComma := true }
    else
      let some doc ← rw_rule_doc? walk rule | return none
      state := { docs := state.docs.push doc, lastComma := false }
  if state.docs.isEmpty || state.lastComma then
    return none
  return some state.docs

private
def dispatch_rw
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  if stx.getKind != ``Lean.Parser.Tactic.rwSeq then
    return .unhandled
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← fallback stx)
  let args := stx.getArgs
  if args.size != 4 then
    return (← fallback stx)
  if !(Lean4Fmt.Emit.bare_src args[1]!).trimAscii.toString.isEmpty then
    return (← fallback stx)
  let rules := args[2]!
  if rules.getKind != ``Lean.Parser.Tactic.rwRuleSeq || rules.getArgs.size != 3 then
    return (← fallback stx)
  let some docs ← rw_rules? walk ((rules.getArgs[1]?.map (·.getArgs)).getD #[])
    | return (← fallback stx)
  let location := (args[3]?.map Lean4Fmt.Emit.canon_tok).getD ""
  if location.any (· == '\n') then return (← fallback stx)
  let locationDoc : Doc := if location.isEmpty then .nil else .text (" " ++ location)
  let width := (← read).layout.lineWidth
  let anyWide := docs.any (fun doc => ((Lean4Fmt.Doc.flat_width doc).getD (width + 1)) + 12 > width)
  if docs.size == 1 && anyWide then
    return .handled (.text "rw [" ++ docs[0]! ++ .text "]" ++ locationDoc)
  let listDoc :=
    if (← read).breaking.listFill && !anyWide then
      Lean4Fmt.Doc.fill_list "[" "]" docs
    else
      Lean4Fmt.Doc.comma_list "[" "]" docs
  return .handled (.text "rw " ++ listDoc ++ locationDoc)

private
def dispatch_head_block
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  let kind := stx.getKind
  let ordinary :=
    kind == `Lean.Parser.Tactic.«tacticNext_=>_» || kind == ``Lean.Parser.Tactic.case
        || kind == ``Lean.Parser.Tactic.allGoals
        || kind == `Lean.Parser.Tactic.tacticRepeat_
  let conv := kind == `Lean.Parser.Tactic.Conv.conv
  if !ordinary && !conv then
    return .unhandled
  let some doc ← head_block_doc? walk stx (conv := conv) | return (← fallback stx)
  return .handled doc

private
def dispatch_classical
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  if stx.getKind != `Lean.Parser.Tactic.classical then
    return .unhandled
  let args := stx.getArgs
  if args.size != 2 then
    return (← fallback stx)
  let keywordTrail := (Lean4Fmt.Syntax.trailing? args[0]!).getD ""
  if !keywordTrail.trimAscii.toString.isEmpty then
    return (← fallback stx)
  let keyword := (Lean4Fmt.Emit.bare_src args[0]!).trimAscii.toString
  let some groups := tactic_groups? args[1]! | return (← fallback stx)
  let some body ← seq_groups_doc? walk groups true | return (← fallback stx)
  return .handled (.text keyword ++ body)

private
def dispatch_bullet
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  if stx.getKind != `Lean.cdot then
    return .unhandled
  let args := stx.getArgs
  if args.size != 2 then
    return (← fallback stx)
  let token := (Lean4Fmt.Emit.bare_src args[0]!).trimAscii.toString
  let tokenTrail := ((Lean4Fmt.Syntax.trailing? args[0]!).getD "").trimAscii.toString
  let some groups := tactic_groups? args[1]! | return (← fallback stx)
  if tokenTrail.startsWith "--" && !tokenTrail.any (· == '\n') then
    let some rest ← seq_groups_doc? walk groups true | return (← fallback stx)
    return .handled (.align (.text (token ++ " " ++ tokenTrail) ++ .nest 2 rest))
  if !tokenTrail.isEmpty then
    return (← fallback stx)
  let firstGroup := groups[0]!
  let firstLead := (Lean4Fmt.Syntax.leading? firstGroup[0]!).getD ""
  if ((firstLead.splitOn "\n").drop 1).dropLast.any
      (fun line => !line.trimAscii.toString.isEmpty) then
    return (← fallback stx)
  let some firstDoc ← group_doc? walk firstGroup | return (← fallback stx)
  if Lean4Fmt.Doc.hasMultilineVerbatim firstDoc then return (← fallback stx)
  let firstTrail :=
    ((Lean4Fmt.Syntax.trailing? firstGroup[firstGroup.size - 1]!).getD "").trimAscii.toString
  if groups.size == 1 then
    if !firstTrail.isEmpty then return (← fallback stx)
    return .handled (.text (token ++ " ") ++ .align firstDoc)
  if firstTrail.any (· == '\n') then return (← fallback stx)
  let trailDoc : Doc := if firstTrail.isEmpty then .nil else .text (" " ++ firstTrail)
  let some rest ← seq_groups_doc? walk (groups.extract 1 groups.size) true
    | return (← fallback stx)
  return .handled
    (.align (.text (token ++ " ") ++ .align firstDoc ++ trailDoc ++ .nest 2 rest))

private
def dispatch_suffices
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  if stx.getKind != `Lean.Parser.Tactic.tacticSuffices_
      || !(Lean4Fmt.Emit.bare_src stx).any (· == '\n') then
    return .unhandled
  let bare := Lean4Fmt.Emit.bare_src stx
  let some byNode := last_by_descendant? stx | return (← fallback stx)
  let some startPos := stx.getPos? | return (← fallback stx)
  let some byPos := byNode.getPos? | return (← fallback stx)
  if byNode.getTailPos? != stx.getTailPos? then
    return (← fallback stx)
  if head_ws_sensitive byPos.byteIdx stx then
    return (← fallback stx)
  let headBytes :=
    (String.fromUTF8? (bare.toUTF8.extract 0 (byPos.byteIdx - startPos.byteIdx))).getD ""
  if headBytes.isEmpty || headBytes.toList.any (· == '"')
      || (headBytes.splitOn "--").length > 1 || (headBytes.splitOn "/-").length > 1 then
    return (← fallback stx)
  let head :=
    String.intercalate
      " "
      (
        (
          (headBytes.split (fun char => char == '\n' || char == ' ' || char == '\t')).toList.map
            (·.toString)
        ).filter
          (fun word => !word.isEmpty)
      )
  if head.isEmpty then
    return (← fallback stx)
  let byDoc ← walk byNode
  let .verbatim _ _ := byDoc | return .handled (.text (head ++ " ") ++ byDoc)
  return (← fallback stx)

private
def is_token_line_kind (kind : Lean.Name) : Bool :=
  kind == ``Lean.Parser.Tactic.tacticRfl || kind == ``Lean.Parser.Tactic.omega
      || kind == ``Lean.Parser.Tactic.decide
      || kind == ``Lean.Parser.Tactic.nativeDecide
      || kind == ``Lean.Parser.Tactic.constructor
      || kind == ``Lean.Parser.Tactic.tacticTrivial
      || kind == ``Lean.Parser.Tactic.contradiction
      || kind == ``Lean.Parser.Tactic.assumption
      || kind == ``Lean.Parser.Tactic.tacticAnd_intros
      || kind == ``Lean.Parser.Tactic.simpAll
      || kind == ``Lean.Parser.Tactic.intro
      || kind == ``Lean.Parser.Tactic.intros
      || kind == ``Lean.Parser.Tactic.split
      || kind == `Lean.Parser.Tactic.rcases
      || kind == ``Lean.Parser.Tactic.show
      || kind == `Lean.Parser.Tactic.subst
      || kind == `Lean.Parser.Tactic.«tacticExists_,,»
      || kind == ``Lean.Parser.Tactic.change
      || kind == `«tacticBy_cases_:_»
      || kind == `Lean.Parser.Tactic.tacticSuffices_
      || kind == `Lean.Parser.Tactic.congr
      || kind == `Lean.Parser.Tactic.renameI
      || kind == `Lean.Parser.Tactic.bvDecide
      || kind == `Lean.Parser.Tactic.left
      || kind == `Lean.Parser.Tactic.right
      || kind == `Lean.Parser.Tactic.revert
      || kind == `Lean.Parser.Tactic.injection
      || kind == `Lean.Parser.Tactic.tacticInfer_instance
      || kind == `Lean.Parser.Tactic.tacticExfalso
      || kind == `Lean.Parser.Tactic.«tacticNomatch_,,»
      || kind == `Lean.Parser.Tactic.paren
      || kind == `Lean.Parser.Tactic.generalize

private
def dispatch_token_line (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Dispatch := do
  if !is_token_line_kind stx.getKind then
    return .unhandled
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← fallback stx)
  let mut line := ""
  for child in stx.getArgs do
    let token :=
      (Lean4Fmt.Emit.token_join? child).getD ((Lean4Fmt.Emit.bare_src child).trimAscii.toString)
    if token.any (· == '\n') then
      return (← fallback stx)
    if !token.isEmpty then line := if line.isEmpty then token else line ++ " " ++ token
  if line.isEmpty then
    return (← fallback stx)
  return .handled (.text line)

private
def dispatch_by
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  let kind := stx.getKind
  if kind != ``Lean.Parser.Term.byTactic && kind != `Lean.Parser.Term.byTactic' then
    return .unhandled
  let args := stx.getArgs
  if args.size != 2 then
    return (← fallback stx)
  if !((Lean4Fmt.Syntax.trailing? args[0]!).getD "").trimAscii.toString.isEmpty then
    return (← fallback stx)
  let some body ← arm_seq_doc? walk args[1]! | return (← fallback stx)
  return .handled (.text "by" ++ body)

private
def induction_arm_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (alt : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  if alt.getKind != ``Lean.Parser.Tactic.inductionAlt || alt.getArgs.size != 2 then
    return none
  let left := Lean4Fmt.Emit.canon_tok alt.getArgs[0]!
  if left.isEmpty || left.any (· == '\n') then
    return none
  let right := alt.getArgs[1]!.getArgs
  if right.size == 0 then
    return some (.text left)
  if right.size != 2 then
    return none
  let some seq := right[1]? | return none
  let arrowSource := ((right[0]?.map Lean4Fmt.Emit.bare_src).getD "").trimAscii.toString
  let arrow := if arrowSource.isEmpty then "=>" else arrowSource
  let arrowTrail := ((right[0]?.bind Lean4Fmt.Syntax.trailing?).getD "").trimAscii.toString
  if arrowTrail.any (· == '\n')
      || (!arrowTrail.isEmpty && !arrowTrail.startsWith "--") then
    return none
  if seq.getKind == ``Lean.Parser.Term.syntheticHole || seq.getKind == ``Lean.Parser.Term.hole then
    let hole := Lean4Fmt.Emit.canon_tok seq
    if hole.isEmpty || hole.any (· == '\n') || !arrowTrail.isEmpty then
      return none
    return some (.text (left ++ " " ++ arrow ++ " " ++ hole))
  if !arrowTrail.isEmpty then
    let some groups := tactic_groups? seq | return none
    let some rest ← seq_groups_doc? walk groups true | return none
    return some (.text (left ++ " " ++ arrow ++ " " ++ arrowTrail) ++ .nest 2 rest)
  let some body ← arm_seq_doc? walk seq | return none
  return some (.text (left ++ " " ++ arrow) ++ body)

private
def induction_alt_sep? (alt : Lean.Syntax) : Option Doc :=
  let leading := (Lean4Fmt.Syntax.leading? alt).getD ""
  let hasContent :=
    ((leading.splitOn "\n").drop 1).dropLast.any (fun line => !line.trimAscii.toString.isEmpty)
  if hasContent then Lean4Fmt.Emit.leading_sep? leading else some .hardline

private
def induction_arm_or_verbatim
    (walk : Lean4Fmt.Emit.Walk)
    (alt : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Doc := do
  let some doc ← induction_arm_doc? walk alt | return (← Lean4Fmt.Emit.verbatim alt)
  return doc

private
def dispatch_induction
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  let kind := stx.getKind
  if kind != ``Lean.Parser.Tactic.induction && kind != ``Lean.Parser.Tactic.cases then
    return .unhandled
  let args := stx.getArgs
  if args.isEmpty then
    return (← fallback stx)
  let mut head := ""
  for child in args.extract 0 (args.size - 1) do
    let token := Lean4Fmt.Emit.canon_tok child
    if token.any (· == '\n') then
      return (← fallback stx)
    if !token.isEmpty then head := if head.isEmpty then token else head ++ " " ++ token
  if head.isEmpty then
    return (← fallback stx)
  let alternativesSlot := args[args.size - 1]!
  if (Lean4Fmt.Emit.bare_src alternativesSlot).trimAscii.toString.isEmpty then
    return .handled (.text head)
  let some alternativesNode := alternativesSlot.getArgs[0]? | return (← fallback stx)
  if alternativesNode.getKind != ``Lean.Parser.Tactic.inductionAlts
      || alternativesNode.getArgs.size != 3 then
    return (← fallback stx)
  if !(Lean4Fmt.Emit.bare_src alternativesNode.getArgs[1]!).trimAscii.toString.isEmpty then
    return (← fallback stx)
  let mut doc : Doc := .text (head ++ " with")
  for alt in alternativesNode.getArgs[2]!.getArgs do
    let some separator := induction_alt_sep? alt | return (← fallback stx)
    doc := doc ++ separator ++ (← induction_arm_or_verbatim walk alt)
  return .handled doc

private
def obtain_head_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let args := stx.getArgs
  let mut head := (Lean4Fmt.Emit.bare_src args[0]!).trimAscii.toString
  if head != "obtain" then
    return none
  let pattern := Lean4Fmt.Emit.canon_tok args[1]!
  if pattern.any (· == '\n') then
    return none
  if !pattern.isEmpty then head := head ++ " " ++ pattern
  let typeText := Lean4Fmt.Emit.canon_tok args[2]!
  if typeText.isEmpty then
    return some (.text head)
  if !typeText.any (· == '\n') then
    return some (.text (head ++ " " ++ typeText))
  let typeArgs := args[2]!.getArgs
  let typeNode :=
    if typeArgs.size == 2 && (Lean4Fmt.Emit.bare_src typeArgs[0]!).trimAscii.toString == ":" then
      typeArgs[1]!
    else
      .missing
  if typeNode.isMissing then
    return none
  let typeDoc ← walk typeNode
  if (match typeDoc with | .verbatim _ _ => true | _ => false)
      || Lean4Fmt.Doc.hasMultilineVerbatim typeDoc then
    return none
  return some (.text (head ++ " :") ++ .group (.nest 4 (.line ++ typeDoc)))

private
def obtain_value? (assignment : Lean.Syntax) : Option Lean.Syntax :=
  if (Lean4Fmt.Emit.bare_src assignment).trimAscii.toString.isEmpty || assignment.getArgs.size != 2 then
    none
  else
    let targets := assignment.getArgs[1]!.getArgs
    if targets.size != 1 then
      none
    else
      let target := targets[0]!
      if target.getKind == `Lean.Parser.Tactic.casesTarget && target.getArgs.size == 2
          && (Lean4Fmt.Emit.bare_src target.getArgs[0]!).trimAscii.toString.isEmpty then
        some target.getArgs[1]!
      else
        some target

private
def obtain_value_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (headDoc : Doc)
    (value : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let valueDoc ← walk value
  let valueIsBlock :=
    value.getKind == ``Lean.Parser.Term.do || value.getKind == ``Lean.Parser.Term.byTactic
  if valueIsBlock then
    if valueDoc matches .verbatim _ _ then
      return none
    return some (headDoc ++ .text " := " ++ valueDoc)
  if Lean4Fmt.Doc.hasMultilineVerbatim valueDoc then
    if valueDoc matches .verbatim _ _ then
      return none
    if Lean4Fmt.Doc.has_midline_reanchor valueDoc then
      return none
    return some (headDoc ++ .text " :=" ++ .nest 2 (.hardline ++ valueDoc))
  return some (headDoc ++ .text " :=" ++ .group (.nest 2 (.line ++ valueDoc)))

private
def dispatch_obtain
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  if stx.getKind != `Lean.Parser.Tactic.obtain then
    return .unhandled
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← fallback stx)
  let args := stx.getArgs
  if args.size != 4 then
    return (← fallback stx)
  let some headDoc ← obtain_head_doc? walk stx | return (← fallback stx)
  if (Lean4Fmt.Emit.bare_src args[3]!).trimAscii.toString.isEmpty then
    return .handled headDoc
  let some value := obtain_value? args[3]! | return (← fallback stx)
  let some doc ← obtain_value_doc? walk headDoc value | return (← fallback stx)
  return .handled doc

private
def calc_steps? (stx : Lean.Syntax) : Option (Array Lean.Syntax) := do
  let args := stx.getArgs
  if args.size != 2 then none
  let stepArgs := args[1]!.getArgs
  if stepArgs.size != 2 then none
  let steps := #[stepArgs[0]!] ++ stepArgs[1]!.getArgs
  if steps.isEmpty then none
  else some steps

private
def calc_flat_doc? (steps : Array Lean.Syntax) (width : Nat) : Option Doc :=
  Id.run do
    let mut flatSteps : Array String := #[]
    for step in steps do
      if head_ws_sensitive (1 <<< 60) step then
        return none
      let some text := Lean4Fmt.Emit.token_join_flat? step | return none
      if text.isEmpty || text.length + 7 > width then
        return none
      flatSteps := flatSteps.push text
    let mut doc : Doc := .text "calc " ++ .text flatSteps[0]!
    for idx in [1:flatSteps.size] do
      doc := doc ++ .nest 5 (.hardline ++ .text flatSteps[idx]!)
    return some doc

private
def calc_proof? (stepArgs : Array Lean.Syntax) : Option Lean.Syntax :=
  if stepArgs.size == 3 && (Lean4Fmt.Emit.bare_src stepArgs[1]!).trimAscii.toString == ":=" then
    some stepArgs[2]!
  else if stepArgs.size == 2 then
    let assignment := stepArgs[1]!
    if assignment.getKind == Lean.nullKind && assignment.getArgs.size == 2
        && (Lean4Fmt.Emit.bare_src assignment.getArgs[0]!).trimAscii.toString == ":=" then
      some assignment.getArgs[1]!
    else
      none
  else
    none

private
def calc_step_doc?
    (walk : Lean4Fmt.Emit.Walk)
    (first : Bool)
    (step : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m (Option Doc) := do
  let args := step.getArgs
  let bareHead :=
    first && args.size == 2 && (Lean4Fmt.Emit.bare_src args[1]!).trimAscii.toString.isEmpty
  if bareHead then
    let some relation := args[0]? | return none
    let relationDoc ← walk relation
    if (match relationDoc with | .verbatim _ _ => true | _ => false)
        || Lean4Fmt.Doc.hasMultilineVerbatim relationDoc then
      return none
    return some relationDoc
  let some proof := calc_proof? args | return none
  let some relation := args[0]? | return none
  let relationDoc ← walk relation
  if (match relationDoc with | .verbatim _ _ => true | _ => false)
      || Lean4Fmt.Doc.hasMultilineVerbatim relationDoc then
    return none
  let proofDoc ← walk proof
  if proof.getKind == ``Lean.Parser.Term.do || proof.getKind == ``Lean.Parser.Term.byTactic then
    if proofDoc matches .verbatim _ _ then
      return none
    return some (relationDoc ++ .nest 4 (.text " := " ++ proofDoc))
  if Lean4Fmt.Doc.hasMultilineVerbatim proofDoc then
    return none
  return some (relationDoc ++ .nest 4 (.text " :=" ++ .group (.line ++ proofDoc)))

private
def calc_broken_doc
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    (steps : Array Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Doc := do
  let mut body : Doc := .nil
  let mut first := true
  for step in steps do
    let stepDoc? ← calc_step_doc? walk first step
    match stepDoc?, first with
    | some stepDoc, true => body := .text "calc " ++ stepDoc
    | some stepDoc, false => body := body ++ .nest 2 (.hardline ++ stepDoc)
    | none, true => return (← Lean4Fmt.Emit.verbatim stx)
    | none, false => body := body ++ .nest 2 (.hardline ++ (← Lean4Fmt.Emit.verbatim step))
    first := false
  return body

private
def dispatch_calc
    (walk : Lean4Fmt.Emit.Walk)
    (stx : Lean.Syntax)
    : Lean4Fmt.Emit.emit_m Dispatch := do
  let kind := stx.getKind
  if kind != `Lean.calcTactic && kind != `Lean.calc then
    return .unhandled
  if (← read).breaking.preserveLineBreaks && (Lean4Fmt.Emit.bare_src stx).any (· == '\n') then
    return (← fallback stx)
  if Lean4Fmt.Syntax.interior_has_line_comment stx then
    return (← fallback stx)
  let some steps := calc_steps? stx | return (← fallback stx)
  if let some doc := calc_flat_doc? steps (← read).layout.lineWidth then
    return .handled doc
  return .handled (← calc_broken_doc walk stx steps)

/-- Emit a Tactic-category construct: the `by` block (one tactic per line at
    +2), and the ported tactic interiors — `exact`/`apply`/`refine` (term
    walked, width-aware), `rw` (rule list as a commaList), `unfold` (idents as
    text), `induction`/`cases … with` alternatives (arm bodies via the branch
    layout). Unknown tactics reproduce verbatim — the tactic language is
    extensible and byte-exact passthrough is the contract. -/
private
abbrev Handler := Lean.Syntax → Lean4Fmt.Emit.emit_m Dispatch

mutual

  private partial
  def route_dispatch (handlers : List Handler) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc :=
    match handlers with
    | []              => Lean4Fmt.Emit.verbatim stx
    | handler :: rest => route_next handler rest stx

  private partial
  def route_next
      (handler : Handler)
      (rest : List Handler)
      (stx : Lean.Syntax)
      : Lean4Fmt.Emit.emit_m Doc := do
    let result ← handler stx
    route_result result rest stx

  private partial
  def route_result
      (result : Dispatch)
      (rest : List Handler)
      (stx : Lean.Syntax)
      : Lean4Fmt.Emit.emit_m Doc :=
    match result with
    | .handled doc => pure doc
    | .unhandled   => route_dispatch rest stx

end

/-- Emit a Tactic-category construct through ordered, family-local handlers.
    Unknown tactics reproduce verbatim. -/
def emit (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.emit_m Doc :=
  route_dispatch
    [
      dispatch_exact walk,
      dispatch_rw walk,
      dispatch_binding walk,
      dispatch_obtain walk,
      dispatch_simp walk,
      dispatch_chain walk,
      dispatch_first walk,
      dispatch_match walk,
      dispatch_unfold,
      dispatch_induction walk,
      dispatch_head_block walk,
      dispatch_classical walk,
      dispatch_calc walk,
      dispatch_bullet walk,
      dispatch_suffices walk,
      dispatch_token_line,
      dispatch_by walk
    ]
    stx

end Lean4Fmt.Emit.Tactic
