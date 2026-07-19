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

/-- A multi-line structure instance WITHOUT comma separators relies on field
    COLUMN alignment (`{  f := v\n    g := w }` — the two spaces after `{` put
    the first field on the shared column): its interior spacing is
    load-bearing, so ws canon must not touch an enclosing verbatim
    (collapsing `{  ` → `{ ` shifted the first field off the column and the
    output FAILED TO REPARSE — gate-caught on Submonoid/Defs). -/
partial def hasColumnSensitiveStructInst (stx : Lean.Syntax) : Bool :=
  match stx with
  | .node _ k args => Id.run do
    if k == ``Lean.Parser.Term.structInst then
      let mut fields := 0
      let mut commas := 0
      for g in ((args[2]?.map (·.getArgs)).getD #[]) do
        for c in g.getArgs do
          if c.getKind == ``Lean.Parser.Term.structInstField then fields := fields + 1
          else if c.isAtom && (bareSrc c).trimAscii.toString == "," then commas := commas + 1
      let spanNl := (args[2]?.map (fun s => (bareSrc s).any (· == '\n'))).getD false
      if fields ≥ 2 && commas < fields - 1 && spanNl then return true
    return args.any hasColumnSensitiveStructInst
  | _ => false

/-- `canonVerbatimWs` applied PIECEWISE around embedded quotation TERMS: the
    quotation interiors ride byte-exact (the quasiquotation pin), everything
    around them still collapses — a sibling statement's gap must not escape
    canonicalization just because the block also holds a `` `(…) ``. The
    perturber mirrors this boundary (it guards quotation-bearing lines).
    `skipBytes` shifts the range base when `s` is a SUFFIX of the node's bare
    source (spanBodyBlank hands us the tail lines). Whole-node fallbacks: no
    substring/position info, or range geometry that doesn't land inside `s`. -/
def canonWsPiecewise (stx : Lean.Syntax) (s : String) (skipBytes : Nat := 0) : String := Id.run do
  if Lean4Fmt.Syntax.hasQuotationCommand stx then return s
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
def logOptOut (stx : Lean.Syntax) : EmitM Unit :=
  emitDiag { severity := .debug, pos := (stx.getPos?.map (·.byteIdx)).getD 0,
             rule := "verbatim", message := s!"opt-out: {stx.getKind}" }

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
  let base := if lead.any (· == '\n')
    then (((lead.splitOn "\n").getLastD "").toList.takeWhile (· == ' ')).length
    else 0
  -- zero-passthrough closure for the opaque tail: interior ws-run collapse
  -- (canonVerbatimWs) makes even UNPORTED content a canonical function of the
  -- tokens+comments — spacing preservation is exactly what preservation mode
  -- means, so it is the one (non-preset) opt-out
  let preserve := (← read).breaking.preserveLineBreaks
  -- ws-canon with the quasiquotation pin honored piecewise: quotation-command
  -- subtrees ride whole-node byte-exact, embedded quotation TERMS byte-exact
  -- by range, templates via canonVerbatimWs' own template mode — everything
  -- else collapses
  let canon := fun (t : String) =>
    if preserve || hasColumnSensitiveStructInst stx then t
    else canonWsPiecewise stx t
  let s := bareSrc stx
  if s.isEmpty then
    match stx.reprint with
    | some r => pure (.verbatim (canon r) base)
    | none => pure .nil
  else pure (.verbatim (canon s) base)

/-- Opaque reproduction WITH the opt-out trail entry — the safe default. -/
def verbatim
    (stx : Lean.Syntax)
    : EmitM Doc := do
  if !(bareSrc stx).isEmpty then   -- an empty node emits nothing: not an opt-out
    logOptOut stx
  verbatimQuiet stx

/-- Byte-exact passthrough of a whole form INCLUDING its leading trivia. -/
def passthrough
    (stx : Lean.Syntax)
    : EmitM Doc := do
  emitDiag { severity := .debug, pos := (stx.getPos?.map (·.byteIdx)).getD 0,
             rule := "passthrough", message := s!"opt-out: {stx.getKind}" }
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
def leadingSep?
    (lead : String)
    : Option Doc :=
  Lean4Fmt.Doc.leadingSep? lead

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
    : Doc := Id.run do
  if mode == Lean4Fmt.Style.AlignMode.never || arms.size < 2 then return fallback
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
    : Doc := Id.run do
  let flush := fun (out sectLead : Doc) (sect : Array ArmPiece) => Id.run do
    if sect.isEmpty then return out
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
    if p.plain && !sect.isEmpty then
      sect := sect.push p
    else
      out := flush out sectLead sect
      sect := #[p]
      sectLead := p.sep
  return flush out sectLead sect

/-- The leading trivia (comments + blank lines) before a form, as literal text. -/
def leadingRaw (stx : Lean.Syntax) : Doc := .textRaw (Lean4Fmt.Syntax.leading? stx |>.getD "")

/-- The trailing trivia after a form, as literal text. `leadingRaw next` +
    `trailingRaw prev` partition the inter-form gap exactly. -/
def trailingRaw (stx : Lean.Syntax) : Doc := .textRaw (Lean4Fmt.Syntax.trailing? stx |>.getD "")

end Lean4Fmt.Emit
