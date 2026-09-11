/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // LEAN4FMT // EMIT // MONAD
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The walk monad: `EmitM = ReaderT Style (StateM Diagnostics)`, producing `Doc`.
    The walker expresses INTENT; the renderer decides realization.

    Note on structure (doc/design.md §6): Lean can't have mutual recursion across
    modules, so the recursion lives in one place (`Emit.walk`) and the per-
    category emitters (`Emit/Module`, `Emit/Term`, …) are OPEN-RECURSION functions
    that take `walk` as a parameter. That is what lets the split live in separate
    files without a single 1.3k-line function.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import lean_4_fmt.doc
import lean_4_fmt.style
import lean_4_fmt.rules.diagnostic
import lean_4_fmt.syntax.trivia
import lean_4_fmt.syntax.kinds
import lean_4_fmt.emit.ws_sensitivity

namespace Lean4Fmt.Emit

open Lean Lean4Fmt.Doc Lean4Fmt.Style

abbrev emit_m := ReaderT Style (StateM (Array Rules.Diagnostic))

def style : emit_m Style := read
def emit_diag (document : Rules.Diagnostic) : emit_m Unit := modify (·.push document)

/-- The open-recursion walker type: category emitters receive `walk` so they can
    recurse into children without cross-module mutual recursion. -/
abbrev Walk := Lean.Syntax → emit_m Doc

/-- Bare source of a form (no leading/trailing trivia). -/
def bare_src (stx : Lean.Syntax) : String :=
  (stx.getSubstring? false false).map (·.toString) |>.getD ""

private
structure canonical_piece_state where
  output : String := ""
  cursor : Nat := 0

private
def append_canonical_piece
    (state : canonical_piece_state)
    (code quotation : String)
    (cursor : Nat)
    : canonical_piece_state :=
  { output := state.output ++ Lean4Fmt.Doc.canon_verbatim_ws code ++ quotation, cursor }

/-- `canonVerbatimWs` applied PIECEWISE around embedded quotation TERMS: the
    quotation interiors ride byte-exact (the quasiquotation pin), everything
    around them still collapses — a sibling statement's gap must not escape
    canonicalization just because the block also holds a `` `(…) ``. The
    perturber mirrors this boundary (it guards quotation-bearing lines).
    `skipBytes` shifts the range base when `s` is a SUFFIX of the node's bare
    source (spanBodyBlank hands us the tail lines). Whole-node fallbacks: no
    substring/position info, or range geometry that doesn't land inside `s`. -/
def canon_ws_piecewise (stx : Lean.Syntax) (source : String) (skipBytes : Nat := 0) : String :=
  Id.run
    do
      if Lean4Fmt.Syntax.has_quotation_command stx then
        return source
      let some ranges := Lean4Fmt.Syntax.quot_term_ranges? stx | return source
      if ranges.isEmpty then
        return Lean4Fmt.Doc.canon_verbatim_ws source
      let some sub := stx.getSubstring? false false | return source
      let base := sub.startPos.byteIdx + skipBytes
      let bytes := source.toUTF8
      let send := bytes.size
      -- range boundaries are token edges, so byte slices are valid UTF-8; any
      -- decode surprise bails to the whole text (content-safe)
      let piece? := fun (start stop : Nat) => String.fromUTF8? (bytes.extract start stop)
      let mut state : canonical_piece_state := {}
      for (quoteStart, quoteEnd) in ranges do
        if quoteEnd ≤ base then continue -- range before our suffix window
        let startOffset := quoteStart - base -- Nat sub clamps: partial overlap → 0
        let endOffset := quoteEnd - base
        if endOffset ≤ startOffset || startOffset < state.cursor || endOffset > send then
          return source
        match piece? state.cursor startOffset, piece? startOffset endOffset with
        | some code, some quot => state := append_canonical_piece state code quot endOffset
        | _, _ => return source
      match piece? state.cursor send with
      | some tail => return state.output ++ Lean4Fmt.Doc.canon_verbatim_ws tail
      | none => return source

/-- The opt-out trail entry (debug level): names the kind and position.
    `verbatim` emits it; PROBE constructions (docs built speculatively and
    possibly discarded) use `verbatimQuiet` and log at their decision site —
    the trail reports what is EMITTED, not what was considered. -/
def log_opt_out (stx : Lean.Syntax) (why : String := "") : emit_m Unit :=
  let pos := (stx.getPos?.map (·.byteIdx)).getD 0
  let len := ((stx.getTailPos?.map (·.byteIdx)).getD pos) - pos
  emit_diag
    { severity := .debug,
      pos := pos,
      rule := "verbatim",
      message := s!"opt-out: {stx.getKind} len={len}"
          ++ (if why.isEmpty then "" else s!" why={why}") }

/-- Opaque reproduction (§4.1): the safe default for any construct not yet
    actively formatted. Reproduces the BARE source as a re-anchorable `verbatim`
    doc whose `baseIndent` is the first token's source column (from leading
    trivia) — the renderer dedents continuations by that, so the block re-anchors
    correctly at whatever column it is placed (the composition seam, §0.3).
    This variant is TRAIL-QUIET — for speculative doc construction. -/
def verbatim_quiet (stx : Lean.Syntax) : emit_m Doc := do
  let lead := (Lean4Fmt.Syntax.leading? stx).getD ""
  let base :=
    if lead.any (· == '\n') then
      (((lead.splitOn "\n").getLastD "").toList.takeWhile (· == ' ')).length
    else
      0
  -- zero-passthrough closure for the opaque tail: interior ws-run collapse
  -- (canonVerbatimWs) makes even UNPORTED content a canonical function of the
  -- tokens+comments — spacing preservation is exactly what preservation mode
  -- means, so it is the one (non-preset) opt-out
  let preserve := (← read).breaking.preserveLineBreaks
  -- ws-canon with the quasiquotation pin honored piecewise: quotation-command
  -- subtrees ride whole-node byte-exact, embedded quotation TERMS byte-exact
  -- by range, templates via canonVerbatimWs' own template mode — everything
  -- else collapses
  let canon := fun text => if preserve then text else canon_ws_piecewise stx text
  let source := bare_src stx
  if source.isEmpty then
    match stx.reprint with
    | some row => pure (.verbatim (canon row) base)
    | none => pure .nil
  else pure (.verbatim (canon source) base)

/-- Opaque reproduction WITH the opt-out trail entry — the safe default. -/
def verbatim (stx : Lean.Syntax) (why : String := "") : emit_m Doc := do
  if !(bare_src stx).isEmpty then   -- an empty node emits nothing: not an opt-out
    log_opt_out stx why
  verbatim_quiet stx

/-- Source-exact reproduction for a layout-sensitive owner that already sits at
    its final column. Unlike `verbatim`, this does not canonicalize or reanchor
    token payloads whose internal whitespace is semantic. -/
def source_exact (stx : Lean.Syntax) (why : String) : emit_m Doc := do
  log_opt_out stx why
  pure (.verbatim (bare_src stx) 0)

/-- Byte-exact passthrough of a whole form INCLUDING its leading trivia. -/
def passthrough (stx : Lean.Syntax) : emit_m Doc := do
  emit_diag
    { severity := .debug,
      pos      := (stx.getPos?.map (·.byteIdx)).getD 0,
      rule     := "passthrough",
      message  := s!"opt-out: {stx.getKind}" }
  pure (.textRaw ((stx.getSubstring? true false).map (·.toString) |>.getD ""))

/-- Structural placement of a form's leading trivia, as the separator doc that
    goes BEFORE the form in a vertical sequence (a do-statement, an inductive
    constructor): each full line of the trivia is either a blank line (a
    `.blank` request, §8-clamped) or comment content (line or block comment —
    emitted `textRaw`, dedented by the run's minimum indent so relative offsets
    survive, re-anchored at the sequence indent). Two partial lines are dropped:
    the HEAD segment before the first newline (the remainder of the previous
    token's line — its newline IS the separator) and the TAIL segment (the
    form's own indentation — the renderer re-indents). Pure single-newline
    trivia degenerates to the plain `.hardline` separator. `none` when the head
    segment carries content (a comment the previous line's trailing did not
    capture — no seam for it; the caller goes verbatim). -/
def leading_sep? (lead : String) : Option Doc := Lean4Fmt.Doc.leading_sep? lead

/-- §7 matchArms: the aligned form `| pat => body` with the arrow column padded
    across a whole arm set — offered via `alignOr`, so the delta guardrail and
    the line width decide at render time; `fallback` is the ordinary per-arm
    layout. Only when EVERY arm has a flattenable pattern and an inline-capable
    body (a broken body opts the whole set out — mixed grids read worse than no
    grid). -/
def arms_aligned
    (mode : Lean4Fmt.Style.align_mode)
    (maxDelta : Nat)
    (arms : Array (Doc × Option Doc))
    (fallback : Doc)
    : Doc :=
  Id.run do
    if mode == Lean4Fmt.Style.align_mode.never || arms.size < 2 then
      return fallback
    let mut rows : List (List Doc) := []
    for (pattern, body?) in arms do
      let some rightValue := body? | return fallback
      if (Lean4Fmt.Doc.flat_width pattern).isNone || (Lean4Fmt.Doc.flat_width rightValue).isNone then
        return fallback
      rows := rows ++ [[Doc.text "| " ++ pattern, Doc.text "=>", rightValue]]
    let cap := if mode == Lean4Fmt.Style.align_mode.always then 1000000 else maxDelta
    return Doc.align_or { sep := " ", maxDelta := cap } rows fallback

/-- One arm of a comment-interleaved arm set, for the RUN-aligned layout. -/
structure arm_piece where
  /-- Structural leading (comments/blank requests) — positions the arm. -/
  sep : Doc
  /-- The sep is a bare newline: this arm may JOIN the run in progress. -/
  plain : Bool
  /-- The arm's ordinary layout, trailing comment included. -/
  doc : Doc
  /-- `pat × body` when grid-eligible (flat pattern, inline body, no trailing
      comment) — `none` rides plain and terminates its run. -/
  gridRow : Option (Doc × Option Doc)

private
structure arm_run_state where
  plainDoc : Doc := .nil
  rows     : Array (Doc × Option Doc) := #[]
  allGrid  : Bool := true

private
structure arm_runs_state where
  output      : Doc := .nil
  run         : Array arm_piece := #[]
  sectionLead : Doc := .nil

private
structure alt_pattern_state where
  groups  : Array String := #[]
  current : Array Lean.Syntax := #[]
  valid   : Bool := true
  doc     : Doc := .nil

/-- §7 matchArms with clang-format run semantics: a VISIBLE seam (comment or
    blank line) splits the arm set into sections, and each section aligns
    independently (`armsAligned` — delta-guarded; single-arm sections degrade
    to the plain layout). Within a section the whole-set judgment still holds:
    one grid-ineligible arm (broken body, trailing comment) opts its whole
    section out — mixed grids read worse than no grid. This is what lets a
    sectioned table (`-- ── ints ──` between arm groups) keep its grids
    instead of falling to plain arms because the set as a whole is
    seam-bearing. -/
def arms_aligned_runs
    (mode : Lean4Fmt.Style.align_mode)
    (maxDelta : Nat)
    (pieces : Array arm_piece)
    : Doc :=
  Id.run do
    let flush :=
      fun (out sectLead : Doc) (sect : Array arm_piece) =>
        Id.run do
          if sect.isEmpty then
            return out
          let mut state : arm_run_state := {}
          for h : idx in [0:sect.size] do
            let piece := sect[idx]
            state :=
              { state with
                plainDoc := state.plainDoc ++ (if idx == 0 then Doc.nil else Doc.hardline)
                    ++ piece.doc }
            match piece.gridRow with
            | some row => state := { state with rows := state.rows.push row }
            | none => state := { state with allGrid := false }
          let body :=
            if state.allGrid then
              arms_aligned mode maxDelta state.rows state.plainDoc
            else
              state.plainDoc
          return out ++ sectLead ++ body
    let mut state : arm_runs_state := {}
    for piece in pieces do
      if piece.plain && !state.run.isEmpty then state := { state with run := state.run.push piece }
      else
        state := {
          output := flush state.output state.sectionLead state.run
          run := #[piece]
          sectionLead := piece.sep
        }
    return flush state.output state.sectionLead state.run

/-- The `matchAlt` nodes of a `matchAlts` node (groups flattened). -/
def match_alts_of (altsNode : Lean.Syntax) : Array Lean.Syntax :=
  Id.run do
    let mut alts : Array Lean.Syntax := #[]
    for group in altsNode.getArgs do
      for child in group.getArgs do
        if child.getKind == ``Lean.Parser.Term.matchAlt then alts := alts.push child
    return alts

private
def flush_alt_pattern_group
    (joinFlat? : Lean.Syntax → Option String)
    (group : Array Lean.Syntax)
    : Option String := do
  if group.isEmpty then none
  let text ← joinFlat? (Lean.mkNullNode group)
  if text.isEmpty || text.any (· == '\n') then none
  else some text

private
def push_alt_pattern_separator
    (joinFlat? : Lean.Syntax → Option String)
    (separator : Lean.Syntax)
    (state : alt_pattern_state)
    : alt_pattern_state :=
  let trivia_empty :=
    ((Lean4Fmt.Syntax.leading? separator).getD "").trimAscii.toString.isEmpty
        && ((Lean4Fmt.Syntax.trailing? separator).getD "").trimAscii.toString.isEmpty
  match flush_alt_pattern_group joinFlat? state.current with
  | some text =>
    { state with
      groups := state.groups.push text
      current := #[]
      valid := state.valid && trivia_empty
    }
  | none => { state with current := #[], valid := false }

/-- The ALTERNATIVE-pattern stack rebuild (`| p₁\n| p₂\n| p₃ => body` — the
    Abel shape): split the arm's pattern null on its top-level `|` atoms,
    each alternative JOINS flat (parse-derived — `joinFlat?` refuses comments
    and newline-semantic interiors); whole set flat when the joined spelling
    fits (flatten-first), else one alternative per line at the arm's own `|`
    column (hardline = the arm's seam, mathlib's stack). Returns the pattern
    doc plus whether it broke (a broken set is grid-ineligible); `none` when
    the set is not this shape (the caller keeps its verbatim fallback). Pops
    the pattern's stale opt-out entry on success (the walk-interception
    rule). -/
def alt_pattern_stack?
    (patStx : Lean.Syntax)
    (joinFlat? : Lean.Syntax → Option String)
    : emit_m (Option (Doc × Bool)) := do
  let width := (← read).layout.lineWidth
  let mut state : alt_pattern_state := {}
  for child in patStx.getArgs do
    match child with
    | .atom _ "|" =>
      -- a comment riding the separator's trivia has no seam here
      state := push_alt_pattern_separator joinFlat? child state
    | _ => state := { state with current := state.current.push child }
  match flush_alt_pattern_group joinFlat? state.current with
  | some trailing => state := { state with groups := state.groups.push trailing }
  | none => state := { state with valid := false }
  if !state.valid || state.groups.size < 2 then
    return none
  if state.groups.any (fun group => group.length + 8 > width) then
    return none
  let result ← do
    let joined := " | ".intercalate state.groups.toList
    if joined.length + 8 ≤ width then
      pure ((Doc.text joined), false)
    else
      state := { state with doc := .text state.groups[0]! }
      for group in state.groups.toList.drop 1 do
        state := { state with doc := state.doc ++ .hardline ++ .text ("| " ++ group) }
      pure (state.doc, true)
  -- the initial walk logged the pattern null's opt-out, but the rebuilt
  -- set ships — pop the stale entry
  let pos := (patStx.getPos?.map (·.byteIdx)).getD 0
  modify fun documents =>
    if documents.size > 0 && documents[documents.size - 1]!.pos == pos
        && documents[documents.size - 1]!.rule == "verbatim" then
      documents.pop
    else
      documents
  return some result

private
def arm_body_part
    (body : Lean.Syntax)
    (bodyDoc : Doc)
    (sourceBroken preserveLineBreaks : Bool)
    : Doc :=
  let glueBody :=
    body.getKind == ``Lean.Parser.Term.do || body.getKind == ``Lean.Parser.Term.byTactic
  if glueBody then
    .text " " ++ bodyDoc
  else if preserveLineBreaks then
    if sourceBroken then Doc.nest 2 (Doc.hardline ++ bodyDoc) else Doc.text " " ++ bodyDoc
  else
    .group (.nest 2 (.line ++ bodyDoc))

private
def arm_grid_row
    (body : Lean.Syntax)
    (bodyDoc patternDoc : Doc)
    (hasTrail patternBroken : Bool)
    (arrowText : String)
    : Option (Doc × Option Doc) :=
  let inlineOk :=
    body.getKind != ``Lean.Parser.Term.do && !Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc
  if inlineOk && !hasTrail && arrowText == "=>" && !patternBroken then
    some (patternDoc, some bodyDoc)
  else
    none

/-- One `| pat => body` arm as its `arm_piece`: the leading places via
    `leadingSep?`; the arrow spelling comes from SOURCE (`=>` vs mathlib's `↦`
    — the gate's token check rightly refuses a silent rewrite); a `do` body
    glues to the arrow (its statements bring their own hardline), as does any
    `by` body (`=> by` + tactics below is the canonical arm shape); anything
    else is width-aware after the arrow. Preserve mode keeps single-line arms
    byte-exact (hand-padded arrow columns survive). Grid rows only for
    inline-capable `=>` arms without trailing comments — the aligned grid
    pads a hardcoded `=>` column, so a `↦` arm opts out. `none` when the arm
    is unportable (an unowned interior comment, an unownable leading, a
    mid-set multi-line trailing). -/
private
def one_arm_piece?
    (walk : Walk)
    (alt : Lean.Syntax)
    (last : Bool)
    (joinFlat? : Lean.Syntax → Option String)
    : emit_m (Option arm_piece) := do
  if Lean4Fmt.Syntax.has_unowned_interior_comment alt then
    return none
  let lead := (Lean4Fmt.Syntax.leading? alt).getD ""
  let some sep := leading_sep? lead | return none
  let plainSep := ((lead.splitOn "\n").drop 1).dropLast.isEmpty
  let trailT := ((Lean4Fmt.Syntax.trailing? alt).getD "").trimAscii.toString
  if !last && trailT.any (· == '\n') then
    return none
  let hasTrail := !last && !trailT.isEmpty
  let trailDoc : Doc := if hasTrail then .text (" " ++ trailT) else .nil
  let altArgs := alt.getArgs
  let patStx := altArgs[1]?.getD .missing
  let walked ← walk patStx

  -- ws-sensitivity (fixed-point class): a multi-line re-anchoring PATTERN
  -- glued after "| " re-indents by its placement column, which the previous
  -- pass just moved (gate-caught on mathlib Applicative + List/Basic,
  -- +2/pass). The ALTERNATIVE-pattern stack (the Abel shape) is portable
  -- though — see altPatternStack?. Anything else ships as this arm's
  -- verbatim piece, as before.
  let (patternDoc, patternBroken) ← if Lean4Fmt.Doc.hasMultilineReanchor walked then
    match ← alt_pattern_stack? patStx joinFlat? with
    | some stacked => pure stacked
    | none =>
      return some
        { sep     := sep,
          plain   := plainSep,
          doc     := (← verbatim alt "arm-multiline-pattern-piece") ++ trailDoc,
          gridRow := none }
  else pure (walked, false)
  let arrowT := (bare_src (altArgs[2]?.getD .missing)).trimAscii.toString
  let arrowT := if arrowT.isEmpty then "=>" else arrowT
  let body := altArgs[altArgs.size-1]?.getD .missing
  let bodyDoc ← walk body
  let srcBroken := ((Lean4Fmt.Syntax.leading? body).getD "").any (· == '\n')
  let preserveLB := (← read).breaking.preserveLineBreaks

  -- a `by` body glues to the arrow whether its members are active or
  -- verbatim (both sit at sequence-seam hardlines): `=> by` + tactics
  -- below is the canonical arm shape — the non-glued group put `by` on
  -- its own line whenever the proof was multi-line (surfaced when the
  -- alternative-pattern port activated eqns arms with by proofs)
  let bodyPart := arm_body_part body bodyDoc srcBroken preserveLB
  let armSrc := (bare_src alt).trimAscii.toString
  let armDoc :=
    if preserveLB && !armSrc.isEmpty && !armSrc.any (· == '\n') then
      Doc.text armSrc
    else
      .text "| " ++ patternDoc ++ .text (" " ++ arrowT) ++ bodyPart
  let row := arm_grid_row body bodyDoc patternDoc hasTrail patternBroken arrowT
  return some { sep := sep, plain := plainSep, doc := armDoc ++ trailDoc, gridRow := row }

/-- THE shared arm loop: the `arm_piece`s of a `| pat => body` arm set —
    `Term.match` arms and the Decl `declValEqns` value are the same shape, and
    this is their one implementation (they drifted as copies once: the
    arrow-spelling fix landed asymmetrically). `none` when any arm is
    unportable: the CALLER falls back to its own verbatim span
    (whole-match / whole-decl). -/
def arm_pieces?
    (walk : Walk)
    (alts : Array Lean.Syntax)
    (joinFlat? : Lean.Syntax → Option String := fun _ => none)
    : emit_m (Option (Array arm_piece)) := do
  let mut pieces : Array arm_piece := #[]
  for h : idx in [0:alts.size] do
    let some piece ← one_arm_piece? walk alts[idx] (idx + 1 == alts.size) joinFlat? | return none
    pieces := pieces.push piece
  return some pieces

/-- The leading trivia (comments + blank lines) before a form, as literal text. -/
def leading_raw (stx : Lean.Syntax) : Doc := .textRaw (Lean4Fmt.Syntax.leading? stx |>.getD "")

/-- The trailing trivia after a form, as literal text. `leadingRaw next` +
    `trailingRaw prev` partition the inter-form gap exactly. -/
def trailing_raw (stx : Lean.Syntax) : Doc := .textRaw (Lean4Fmt.Syntax.trailing? stx |>.getD "")

end Lean4Fmt.Emit
