/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // LEAN4FMT // EMIT // MONAD
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The walk monad: `EmitM = ReaderT Style (StateM Diagnostics)`, producing `Doc`.
    The walker expresses INTENT; the renderer decides realization.

    Note on structure (DESIGN_V2 §11): Lean can't have mutual recursion across
    modules, so the recursion lives in one place (`Emit.walk`) and the per-
    category emitters (`Emit/Module`, `Emit/Term`, …) are OPEN-RECURSION functions
    that take `walk` as a parameter. That is what lets the split live in separate
    files without a single 1.3k-line function.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import Lean4Fmt.Doc
import Lean4Fmt.Style
import Lean4Fmt.Rules.Diagnostic
import Lean4Fmt.Syntax.Trivia
import Lean4Fmt.Syntax.Kinds
import Lean4Fmt.Emit.WsSensitivity

namespace Lean4Fmt.Emit

open Lean Lean4Fmt.Doc Lean4Fmt.Style

abbrev EmitM := ReaderT Style (StateM (Array Rules.Diagnostic))

def style : EmitM Style := read
def emitDiag (d : Rules.Diagnostic) : EmitM Unit := modify (·.push d)

/-- The open-recursion walker type: category emitters receive `walk` so they can
    recurse into children without cross-module mutual recursion. -/
abbrev Walk := Lean.Syntax → EmitM Doc

/-- Bare source of a form (no leading/trailing trivia). -/
def bareSrc
    (stx : Lean.Syntax)
    : String :=
  (stx.getSubstring? false false).map (·.toString) |>.getD ""

/-- `canonVerbatimWs` applied PIECEWISE around embedded quotation TERMS: the
    quotation interiors ride byte-exact (the quasiquotation pin), everything
    around them still collapses — a sibling statement's gap must not escape
    canonicalization just because the block also holds a `` `(…) ``. The
    perturber mirrors this boundary (it guards quotation-bearing lines).
    `skipBytes` shifts the range base when `s` is a SUFFIX of the node's bare
    source (spanBodyBlank hands us the tail lines). Whole-node fallbacks: no
    substring/position info, or range geometry that doesn't land inside `s`. -/
def canonWsPiecewise
    (stx : Lean.Syntax)
    (s : String)
    (skipBytes : Nat := 0)
    : String :=
  Id.run
    do
      if Lean4Fmt.Syntax.hasQuotationCommand stx then
        return s
      let some ranges := Lean4Fmt.Syntax.quotTermRanges? stx | return s
      if ranges.isEmpty then return Lean4Fmt.Doc.canonVerbatimWs s
      let some sub := stx.getSubstring? false false | return s
      let base := sub.startPos.byteIdx + skipBytes
      let bytes := s.toUTF8
      let send := bytes.size
      -- range boundaries are token edges, so byte slices are valid UTF-8; any
      -- decode surprise bails to the whole text (content-safe)
      let piece? := fun (a b : Nat) => String.fromUTF8? (bytes.extract a b)
      let mut out := ""
      let mut cur : Nat := 0
      for (qs, qe) in ranges do
        if qe ≤ base then continue               -- range before our suffix window
        let a := qs - base                        -- Nat sub clamps: partial overlap → 0
        let b := qe - base
        if b ≤ a || a < cur || b > send then return s   -- geometry surprise: content-safe
        match piece? cur a, piece? a b with
        | some code, some quot =>
          out := out ++ Lean4Fmt.Doc.canonVerbatimWs code ++ quot
          cur := b
        | _, _ => return s
      match piece? cur send with
      | some tail => return out ++ Lean4Fmt.Doc.canonVerbatimWs tail
      | none => return s

/-- The opt-out trail entry (debug level): names the kind and position.
    `verbatim` emits it; PROBE constructions (docs built speculatively and
    possibly discarded) use `verbatimQuiet` and log at their decision site —
    the trail reports what is EMITTED, not what was considered. -/
def logOptOut
    (stx : Lean.Syntax)
    (why : String := "")
    : EmitM Unit :=
  let pos := (stx.getPos?.map (·.byteIdx)).getD 0
  let len := ((stx.getTailPos?.map (·.byteIdx)).getD pos) - pos
  emitDiag
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
def verbatimQuiet
    (stx : Lean.Syntax)
    : EmitM Doc := do
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
  let canon := fun (t : String) => if preserve then t else canonWsPiecewise stx t
  let s := bareSrc stx
  if s.isEmpty then
    match stx.reprint with
    | some r => pure (.verbatim (canon r) base)
    | none => pure .nil
  else pure (.verbatim (canon s) base)

/-- Opaque reproduction WITH the opt-out trail entry — the safe default. -/
def verbatim
    (stx : Lean.Syntax)
    (why : String := "")
    : EmitM Doc := do
  if !(bareSrc stx).isEmpty then   -- an empty node emits nothing: not an opt-out
    logOptOut stx why
  verbatimQuiet stx

/-- Byte-exact passthrough of a whole form INCLUDING its leading trivia. -/
def passthrough
    (stx : Lean.Syntax)
    : EmitM Doc := do
  emitDiag
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
def leadingSep? (lead : String) : Option Doc := Lean4Fmt.Doc.leadingSep? lead

/-- §7 matchArms: the aligned form `| pat => body` with the arrow column padded
    across a whole arm set — offered via `alignOr`, so the delta guardrail and
    the line width decide at render time; `fallback` is the ordinary per-arm
    layout. Only when EVERY arm has a flattenable pattern and an inline-capable
    body (a broken body opts the whole set out — mixed grids read worse than no
    grid). -/
def armsAligned
    (mode : Lean4Fmt.Style.AlignMode)
    (maxDelta : Nat)
    (arms : Array (Doc × Option Doc))
    (fallback : Doc)
    : Doc :=
  Id.run do
    if mode == Lean4Fmt.Style.AlignMode.never || arms.size < 2 then
      return fallback
    let mut rows : List (List Doc) := []
    for (p, b?) in arms do
      let some b := b? | return fallback
      if (Lean4Fmt.Doc.flatWidth p).isNone || (Lean4Fmt.Doc.flatWidth b).isNone then
        return fallback
      rows := rows ++ [[Doc.text "| " ++ p, Doc.text "=>", b]]
    let cap := if mode == Lean4Fmt.Style.AlignMode.always then 1000000 else maxDelta
    return Doc.alignOr { sep := " ", maxDelta := cap } rows fallback

/-- One arm of a comment-interleaved arm set, for the RUN-aligned layout. -/
structure ArmPiece where
  /-- Structural leading (comments/blank requests) — positions the arm. -/
  sep : Doc
  /-- The sep is a bare newline: this arm may JOIN the run in progress. -/
  plain : Bool
  /-- The arm's ordinary layout, trailing comment included. -/
  doc : Doc
  /-- `pat × body` when grid-eligible (flat pattern, inline body, no trailing
      comment) — `none` rides plain and terminates its run. -/
  gridRow : Option (Doc × Option Doc)

/-- §7 matchArms with clang-format run semantics: a VISIBLE seam (comment or
    blank line) splits the arm set into sections, and each section aligns
    independently (`armsAligned` — delta-guarded; single-arm sections degrade
    to the plain layout). Within a section the whole-set judgment still holds:
    one grid-ineligible arm (broken body, trailing comment) opts its whole
    section out — mixed grids read worse than no grid. This is what lets a
    sectioned table (`-- ── ints ──` between arm groups) keep its grids
    instead of falling to plain arms because the set as a whole is
    seam-bearing. -/
def armsAlignedRuns
    (mode : Lean4Fmt.Style.AlignMode)
    (maxDelta : Nat)
    (pieces : Array ArmPiece)
    : Doc :=
  Id.run do
    let flush :=
      fun (out sectLead : Doc) (sect : Array ArmPiece) =>
        Id.run do
          if sect.isEmpty then
            return out
          let mut plainJ : Doc := .nil
          let mut rows : Array (Doc × Option Doc) := #[]
          let mut allGrid := true
          for h : j in [0:sect.size] do
            let p := sect[j]
            plainJ := plainJ ++ (if j == 0 then Doc.nil else Doc.hardline) ++ p.doc
            match p.gridRow with
            | some r => rows := rows.push r
            | none => allGrid := false
          let body := if allGrid then armsAligned mode maxDelta rows plainJ else plainJ
          return out ++ sectLead ++ body
    let mut out : Doc := .nil
    let mut sect : Array ArmPiece := #[]
    let mut sectLead : Doc := .nil
    for p in pieces do
      if p.plain && !sect.isEmpty then sect := sect.push p
      else
        out := flush out sectLead sect
        sect := #[p]
        sectLead := p.sep
    return flush out sectLead sect

/-- The `matchAlt` nodes of a `matchAlts` node (groups flattened). -/
def matchAltsOf
    (altsNode : Lean.Syntax)
    : Array Lean.Syntax :=
  Id.run do
    let mut alts : Array Lean.Syntax := #[]
    for g in altsNode.getArgs do
      for c in g.getArgs do
        if c.getKind == ``Lean.Parser.Term.matchAlt then alts := alts.push c
    return alts

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
def altPatternStack?
    (patStx : Lean.Syntax)
    (joinFlat? : Lean.Syntax → Option String)
    : EmitM (Option (Doc × Bool)) := do
  let width := (← read).layout.lineWidth
  let flushG :=
    fun (g : Array Lean.Syntax) =>
      Id.run do
        if g.isEmpty then
          return none
        match joinFlat? (Lean.mkNullNode g) with
        | some t =>
          if t.isEmpty || t.any (· == '\n') then
            return none
          return some t
        | none => return (none : Option String)
  let mut groups : Array String := #[]
  let mut curG : Array Lean.Syntax := #[]
  let mut ok := true
  for c in patStx.getArgs do
    match c with
    | .atom _ "|" =>
      -- a comment riding the separator's trivia has no seam here
      if !(((Lean4Fmt.Syntax.leading? c).getD "").trimAscii.toString.isEmpty
          && ((Lean4Fmt.Syntax.trailing? c).getD "").trimAscii.toString.isEmpty) then
        ok := false
      match flushG curG with
      | some t => groups := groups.push t
      | none => ok := false
      curG := #[]
    | _ => curG := curG.push c
  match flushG curG with
  | some t => groups := groups.push t
  | none => ok := false
  if !ok || groups.size < 2 then
    return none
  if groups.any (fun g => g.length + 8 > width) then
    return none
  let result ← do
    let joined := " | ".intercalate groups.toList
    if joined.length + 8 ≤ width then
      pure ((Doc.text joined), false)
    else
      let mut pd : Doc := .text groups[0]!
      for g in groups.toList.drop 1 do
        pd := pd ++ .hardline ++ .text ("| " ++ g)
      pure (pd, true)
  -- the initial walk logged the pattern null's opt-out, but the rebuilt
  -- set ships — pop the stale entry
  let pos := (patStx.getPos?.map (·.byteIdx)).getD 0
  modify fun ds =>
    if ds.size > 0 && ds[ds.size - 1]!.pos == pos && ds[ds.size - 1]!.rule == "verbatim" then
      ds.pop
    else
      ds
  return some result

/-- THE shared arm loop: the `ArmPiece`s of a `| pat => body` arm set —
    `Term.match` arms and the Decl `declValEqns` value are the same shape, and
    this is their one implementation (they drifted as copies once: the
    arrow-spelling fix landed asymmetrically). Per arm: the leading places via
    `leadingSep?`; the arrow spelling comes from SOURCE (`=>` vs mathlib's `↦`
    — the gate's token check rightly refuses a silent rewrite); a `do` body
    glues to the arrow (its statements bring their own hardline), as does any
    `by` body (`=> by` + tactics below is the canonical arm shape); anything
    else is width-aware after the arrow. Preserve mode keeps single-line arms
    byte-exact (hand-padded arrow columns survive). Grid rows only for
    inline-capable `=>` arms without trailing comments — the aligned grid
    pads a hardcoded `=>` column, so a `↦` arm opts out. `none` when any arm
    is unportable (an unowned interior comment, an unownable leading, a
    mid-set multi-line trailing): the CALLER falls back to its own verbatim
    span (whole-match / whole-decl). -/
def armPieces?
    (walk : Walk)
    (alts : Array Lean.Syntax)
    (joinFlat? : Lean.Syntax → Option String := fun _ => none)
    : EmitM (Option (Array ArmPiece)) := do
  let mut pieces : Array ArmPiece := #[]
  for h : i in [0:alts.size] do
    let alt := alts[i]
    if Lean4Fmt.Syntax.hasUnownedInteriorComment alt then
      return none
    let lead := (Lean4Fmt.Syntax.leading? alt).getD ""
    let some sep := leadingSep? lead | return none
    let plainSep := ((lead.splitOn "\n").drop 1).dropLast.isEmpty
    let trailT := ((Lean4Fmt.Syntax.trailing? alt).getD "").trimAscii.toString
    let last := i + 1 == alts.size
    if !last && trailT.any (· == '\n') then return none
    let hasTrail := !last && !trailT.isEmpty
    let trailDoc : Doc := if hasTrail then .text (" " ++ trailT) else .nil
    let aa := alt.getArgs
    let patStx := aa[1]?.getD .missing
    let mut patDoc ← walk (aa[1]?.getD .missing)
    let mut patBroken := false
    -- ws-sensitivity (fixed-point class): a multi-line re-anchoring PATTERN
    -- glued after "| " re-indents by its placement column, which the previous
    -- pass just moved (gate-caught on mathlib Applicative + List/Basic,
    -- +2/pass). The ALTERNATIVE-pattern stack (the Abel shape) is portable
    -- though — see altPatternStack?. Anything else stays the caller's to
    -- verbatim, as before.
    if Lean4Fmt.Doc.hasMultilineReanchor patDoc then
      match ← altPatternStack? patStx joinFlat? with
      | some (pd, broken) =>
        patDoc := pd
        patBroken := broken
      | none => return none
    let arrowT := (bareSrc (aa[2]?.getD .missing)).trimAscii.toString
    let arrowT := if arrowT.isEmpty then "=>" else arrowT
    let body := aa[aa.size-1]?.getD .missing
    let bodyDoc ← walk body
    let srcBroken := ((Lean4Fmt.Syntax.leading? body).getD "").any (· == '\n')
    let preserveLB := (← read).breaking.preserveLineBreaks
    -- a `by` body glues to the arrow whether its members are active or
    -- verbatim (both sit at sequence-seam hardlines): `=> by` + tactics
    -- below is the canonical arm shape — the non-glued group put `by` on
    -- its own line whenever the proof was multi-line (surfaced when the
    -- alternative-pattern port activated eqns arms with by proofs)
    let glueBody := body.getKind == ``Lean.Parser.Term.do
      || body.getKind == ``Lean.Parser.Term.byTactic
    let bodyPart : Doc := if glueBody
      then .text " " ++ bodyDoc
      else if preserveLB then
        -- the author's arrow-line decision is load-bearing
        if srcBroken then Doc.nest 2 (Doc.hardline ++ bodyDoc)
        else Doc.text " " ++ bodyDoc
      else .group (.nest 2 (.line ++ bodyDoc))
    let armSrc := (bareSrc alt).trimAscii.toString
    let armDoc :=
      if preserveLB && !armSrc.isEmpty && !armSrc.any (· == '\n') then
        Doc.text armSrc
      else .text "| " ++ patDoc ++ .text (" " ++ arrowT) ++ bodyPart
    let inlineOk := body.getKind != ``Lean.Parser.Term.do
      && !Lean4Fmt.Doc.hasMultilineVerbatim bodyDoc
    let row := if inlineOk && !hasTrail && arrowT == "=>" && !patBroken
      then some (patDoc, some bodyDoc) else none
    pieces := pieces.push
      { sep := sep, plain := plainSep, doc := armDoc ++ trailDoc, gridRow := row }
  return some pieces

/-- The leading trivia (comments + blank lines) before a form, as literal text. -/
def leadingRaw (stx : Lean.Syntax) : Doc := .textRaw (Lean4Fmt.Syntax.leading? stx |>.getD "")

/-- The trailing trivia after a form, as literal text. `leadingRaw next` +
    `trailingRaw prev` partition the inter-form gap exactly. -/
def trailingRaw (stx : Lean.Syntax) : Doc := .textRaw (Lean4Fmt.Syntax.trailing? stx |>.getD "")

end Lean4Fmt.Emit
