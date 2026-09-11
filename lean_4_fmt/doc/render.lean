/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // LEAN4FMT // DOC // RENDER
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Width-aware layout: `Style → Doc → String` (doc/design.md §5). A pragmatic
    Wadler/Leijen renderer: `group` picks flat-or-break by fit; `nest`/`align`
    set the break indent COMPOSITIONALLY (§0.2); `verbatim` re-anchors an opaque
    block to the current indent (§0.3, §4.1); `blank` is clamped by policy (§8).

    TOTAL: every function is total — the container constructors hold Lists, so
    the walkers use structural mutual recursion. The laws in `Lean4Fmt/Proofs`
    are stated about THESE functions, not a model.

    Pure. Depends on Doc.Core + Style.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.doc.core
import lean_4_fmt.doc.content
import lean_4_fmt.style

namespace Lean4Fmt.Doc

open Lean4Fmt.Style

mutual

  /-- Flat width of a doc, or `none` if it cannot be flattened. -/
  def flat_width : Doc → Option Nat
    | .nil => some 0
    | .text textValue => some textValue.length
    | .cat leftValue rightValue =>
      match flat_width leftValue, flat_width rightValue with
      | some xValue, some yValue => some (xValue + yValue)
      | _, _ => none
    | .line => some 1
    | .softline => some 0
    | .hardline => none
    | .group document => flat_width document
    | .nest _ document => flat_width document
    | .align document => flat_width document
    | .flatten document => flat_width document
    | .textRaw textValue => if textValue.toList.any (· == '\n') then none else some textValue.length
    -- must be EXACT for what wrBlock emits on a single line (Proofs T2): the
    -- line is trailing-trimmed, leading whitespace KEPT
    | .verbatim textValue _ =>
      if textValue.toList.any (· == '\n') then none else some (trim_end_ws textValue.toList).length
    | .blank _ => none
    -- pad renders NOTHING in flat mode — 0 keeps T2 (flat exactness); group
    -- fits count the phantom width separately via `padWidth`
    | .pad _ => some 0
    | .alignTable _ _ => none
    | .align_or _ _ flatBody => flat_width flatBody
    | .fillSep [] => some 0
    | .fillSep (indent :: indents) =>
      match flat_width indent, flatWidthSep indents with
      | some width, some widths => some (width + widths)
      | _, _ => none

  /-- Sum of flat widths of the tail items, each preceded by one space. -/
  def flatWidthSep : List Doc → Option Nat
    | [] => some 0
    | indent :: indents =>
      match flat_width indent, flatWidthSep indents with
      | some width, some widths => some (1 + width + widths)
      | _, _ => none

end

/-- First TEXT leaf on the doc's left spine (through cat/nest/flatten): the
    opening bytes when they are UNCONDITIONAL. `group` (and everything else
    width-decided) stops the walk — such a doc has no fixed left edge. Lets
    a caller glue a self-anchoring doc mid-line by its opener (the vertical
    structInst hangs its `{` on the `:=` line, house shape). -/
def left_edge_text? : Doc → Option String
  | .cat leftValue rightValue =>
    match leftValue with
    | .nil => left_edge_text? rightValue
    | _    => left_edge_text? leftValue
  | .nest _ document => left_edge_text? document
  | .flatten document => left_edge_text? document
  | .text textValue => some textValue
  | _ => none

/-- Total phantom `pad` width in a doc — a group fit adds this ON TOP of
    `flatWidth` (which stays render-exact, reporting pad as 0): the reserve
    for un-breakable text the caller appends after the group. -/
def pad_width : Doc → Nat
  | .pad count => count
  | .cat leftValue rightValue => pad_width leftValue + pad_width rightValue
  | .group document | .nest _ document | .align document | .flatten document => pad_width document
  | _ => 0

mutual

  /-- Whether a doc contains a multi-line opaque block (`verbatim`/`textRaw` with a
    newline). Such blocks re-anchor by column, which is only idempotent at their
    natural top-level position — so a subtree containing one must NOT be laid out
    actively (it stays on the safe whole-span path). Hardlines are fine. -/
  def hasMultilineVerbatim : Doc → Bool
    | .verbatim textValue _ => textValue.any (· == '\n')
    | .textRaw textValue => textValue.any (· == '\n')
    | .cat leftValue rightValue => hasMultilineVerbatim leftValue || hasMultilineVerbatim rightValue
    | .group document | .nest _ document | .align document | .flatten document =>
      hasMultilineVerbatim document
    | .alignTable _ rows => hasMLRows rows
    | .align_or _ _ flatBody => hasMultilineVerbatim flatBody
    | .fillSep items => hasMLList items
    | _ => false

  /-- Whether a doc contains a multi-line RE-ANCHORING block — `.verbatim` only.
    `.textRaw` (docstrings, comment blocks) emits its lines RAW at their source
    columns, indifferent to placement indent, so it is placement-stable; only
    `.verbatim` dedents/re-indents by column. The mutual member bail cares
    about exactly the re-anchoring class — counting textRaw kept every member
    with a MULTI-LINE DOCSTRING (and its whole mutual) verbatim. -/
  def hasMultilineReanchor : Doc → Bool
    | .verbatim textValue _ => textValue.any (· == '\n')
    | .cat leftValue rightValue => hasMultilineReanchor leftValue || hasMultilineReanchor rightValue
    | .group document | .nest _ document | .align document | .flatten document =>
      hasMultilineReanchor document
    | .alignTable _ rows => hasMRRows rows
    | .align_or _ _ flatBody => hasMultilineReanchor flatBody
    | .fillSep items => hasMRList items
    | _ => false

  def hasMRList : List Doc → Bool
    | [] => false
    | document :: documents => hasMultilineReanchor document || hasMRList documents

  def hasMRRows : List (List Doc) → Bool
    | []          => false
    | row :: rows => hasMRList row || hasMRRows rows

  def hasMLList : List Doc → Bool
    | [] => false
    | document :: documents => hasMultilineVerbatim document || hasMLList documents

  def hasMLRows : List (List Doc) → Bool
    | []          => false
    | row :: rows => hasMLList row || hasMLRows rows

end

/-- A multi-line `.verbatim` anchored MID-LINE — the fixed-point hazard (its
    re-anchor is additive with placement); one AT a line start is a stable
    seam. The traversal threads "are we at a line start": breaks set it (any
    group containing a multi-line verbatim cannot flatten, so its separators
    genuinely break — which is what makes `.line → true` sound here); visible
    text clears it. Returns (hazardFound, atLineStartAfter). -/
partial
def midline_reanchor_aux : Doc → Bool → Bool × Bool
  | .nil, atLS => (false, atLS)
  | .verbatim textValue _, atLS =>
    if textValue.any (· == '\n') then
      (!atLS, false)
    else
      (false, if textValue.isEmpty then atLS else false)
  | .text textValue, atLS => (false, if textValue.isEmpty then atLS else false)
  | .textRaw textValue, _ => (false, textValue.endsWith "\n")
  | .line, _ | .softline, _ | .hardline, _ | .blank _, _ => (false, true)
  | .pad _, atLS => (false, atLS)
  | .cat leftValue rightValue, atLS =>
    let (firstA, lastA) := midline_reanchor_aux leftValue atLS
    let (flatBody, lastB) := midline_reanchor_aux rightValue lastA
    (firstA || flatBody, lastB)
  | .group document, atLS | .nest _ document, atLS | .align document, atLS | .flatten document, atLS =>
    midline_reanchor_aux document atLS
  | .align_or _ _ flatBody, atLS => midline_reanchor_aux flatBody atLS
  | .fillSep items, _ => (items.any hasMultilineVerbatim, false)
  | .alignTable _ rows, _ => (rows.any (·.any hasMultilineVerbatim), false)

/-- Hazard check for a doc placed AT A LINE START (own-line seam): any
    multi-line verbatim it glues mid-line is a fixed-point drift. -/
def has_midline_reanchor (document : Doc) : Bool := (midline_reanchor_aux document true).1

mutual

  /-- Coverage accounting (doc/design.md §12): (active, verbatim, trivia) bytes. -/
  def stats : Doc → (Nat × Nat × Nat)
    | .text textValue => (textValue.utf8ByteSize, 0, 0)
    | .verbatim textValue _ => (0, textValue.utf8ByteSize, 0)
    | .textRaw textValue => (0, 0, textValue.utf8ByteSize)
    | .cat leftValue rightValue =>
      let (leftAlign, leftVerbatim, leftText) := stats leftValue
      let (rightAlign, rightVerbatim, rightText) := stats rightValue
      (leftAlign + rightAlign, leftVerbatim + rightVerbatim, leftText + rightText)
    | .group document | .nest _ document | .align document | .flatten document => stats document
    | .alignTable _ rows => statsRows rows
    | .align_or _ _ flatBody => stats flatBody
    | .fillSep items => statsList items
    | _ => (0, 0, 0)

  def statsList : List Doc → (Nat × Nat × Nat)
    | [] => (0, 0, 0)
    | document :: documents =>
      let (leftAlign, leftVerbatim, leftText) := stats document
      let (rightAlign, rightVerbatim, rightText) := statsList documents
      (leftAlign + rightAlign, leftVerbatim + rightVerbatim, leftText + rightText)

  def statsRows : List (List Doc) → (Nat × Nat × Nat)
    | [] => (0, 0, 0)
    | row :: rows =>
      let (leftAlign, leftVerbatim, leftText) := statsList row
      let (rightAlign, rightVerbatim, rightText) := statsRows rows
      (leftAlign + rightAlign, leftVerbatim + rightVerbatim, leftText + rightText)

end

/-- Width a doc contributes to the CURRENT line, up to its first possible break
    point, plus whether such a break was reached. A `flatten` never breaks, so
    it contributes its full flat width. -/
def first_line_width : Doc → Nat × Bool
  | .nil => (0, false)
  | .text textValue => (textValue.length, false)
  | .textRaw textValue =>
    let lines := textValue.splitOn "\n";
    ((lines.headD "").length, lines.length > 1)
  | .verbatim textValue _ =>
    let lines := textValue.splitOn "\n";
    ((lines.headD "").length, lines.length > 1)
  | .line | .softline | .hardline | .blank _ => (0, true)
  | .pad _ => (0, false)
  | .cat leftValue rightValue =>
    let (leftWidth, leftBreak) := first_line_width leftValue
    if leftBreak then
      (leftWidth, true)
    else
      let (rightWidth, rightBreak) := first_line_width rightValue;
      (leftWidth + rightWidth, rightBreak)
  | .group document | .nest _ document | .align document => first_line_width document
  | .flatten document =>
    match flat_width document with
    | some width => (width, false)
    | none       => first_line_width document
  | .alignTable _ _ => (0, true)
  | .align_or _ _ flatBody => first_line_width flatBody
  | .fillSep [] => (0, false)
  | .fillSep (indent :: indents) => ((flat_width indent).getD 0, !indents.isEmpty)

def spaces (count : Nat) : String := String.ofList (List.replicate count ' ')
def newlines (count : Nat) : String := String.ofList (List.replicate count '\n')

structure rst where
  out  : String := ""
  col  : Nat := 0
  pend : Nat := 0     -- pending newlines (for blank collapsing)
  deriving Inhabited

/-- Emit single-line visible text at break-indent `indent`, flushing pending
    newlines (with indentation) first. `writeResult` never writes the indent without
    content after it (the hygiene law in Proofs). -/
def writeResult (state : rst) (indent : Nat) (source : String) : rst :=
  let state :=
    if state.pend > 0 then
      { out := state.out ++ newlines state.pend ++ spaces indent, col := indent, pend := 0 }
    else
      state
  { state with out := state.out ++ source, col := state.col + source.length }

/-- Split a char list on '\n' (never returns `[]`; `[]` input → one empty line
    — the char-list twin of `splitOn "\n"`, owned so Proofs can induct). -/
def split_lines : List Char → List (List Char)
  | [] => [[]]
  | headChar :: tailChars =>
    match split_lines tailChars with
    | [] => [[headChar]] -- unreachable (never nil)
    | leading :: lsValue =>
      if headChar = '\n' then [] :: leading :: lsValue else (headChar :: leading) :: lsValue

/-- A line of nothing but spaces (the blank-line notion of `wrBlock`; NOT full
    whitespace — a tab-bearing line may be string-literal interior). -/
def is_blank_line (lineValue : List Char) : Bool := lineValue.all (· == ' ')

/-- One continuation line of a block: dedent, then emit behind one pending
    newline. Dedent drops ONLY spaces: if the first `base` chars aren't all
    spaces (a continuation less indented than its head), fall back to stripping
    just the leading spaces — dropping `base` chars unconditionally would eat
    CONTENT on such lines (latent until the content-preservation theorem in
    Proofs demanded it be impossible). Lines dedented to empty stay pending. -/
def dedent (base : Nat) (lineValue : List Char) : List Char :=
  if lineValue.length ≥ base && (lineValue.take base).all (· == ' ') then
    lineValue.drop base
  else
    lineValue.dropWhile (· == ' ')

def wr_line (state : rst) (indent base : Nat) (lineValue : List Char) : rst :=
  if (dedent base lineValue).isEmpty then
    { state with pend := state.pend + 1 }
  else
    writeResult { state with pend := state.pend + 1 } indent (String.ofList (dedent base lineValue))

def wr_lines (indent base : Nat) : List (List Char) → rst → rst
  | [], state                 => state
  | leading :: lsValue, state => wr_lines indent base lsValue (wr_line state indent base leading)

private
structure string_mask_context where
  chars : Array Char
  size  : Nat

private
structure string_mask_state where
  mode  : Nat := 0
  depth : Nat := 0
  prev  : Char := ' '
  mask  : Array Bool := #[false]
  idx   : Nat := 0

private
def is_identifier_char (char : Char) : Bool :=
  char.isAlphanum || char == '_' || char == '\'' || char == '!' || char == '?' || char.val > 127

private
def scan_raw_delimiter
    (context : string_mask_context)
    (state : string_mask_state)
    : string_mask_state :=
  Id.run do
    let mut delimiterIdx := state.idx + 1
    let mut hashes := 0
    while delimiterIdx < context.size && context.chars[delimiterIdx]! == '#' do
      hashes := hashes + 1
      delimiterIdx := delimiterIdx + 1
    if context.chars[delimiterIdx]? == some '"' then
      return { state with mode := 4, depth := hashes, idx := delimiterIdx }
    return state

private
def scan_code_char
    (context : string_mask_context)
    (state : string_mask_state)
    (char : Char)
    (nextChar : Option Char)
    : string_mask_state :=
  if char == '-' && nextChar == some '-' then
    { state with mode := 1, idx := state.idx + 1 }
  else if char == '/' && nextChar == some '-' then
    { state with mode := 2, depth := 1, idx := state.idx + 1 }
  else if char == '"' then
    { state with mode := 3 }
  else if char == 'r' && !is_identifier_char state.prev
      && (nextChar == some '"' || nextChar == some '#') then
    scan_raw_delimiter context state
  else if char == '\'' && !is_identifier_char state.prev then { state with mode := 5 } else state

private
def scan_block_comment_char
    (state : string_mask_state)
    (char : Char)
    (nextChar : Option Char)
    : string_mask_state :=
  if char == '/' && nextChar == some '-' then
    { state with depth := state.depth + 1, idx := state.idx + 1 }
  else if char == '-' && nextChar == some '/' then
    let depth := state.depth - 1
    { state with mode := if depth == 0 then 0 else state.mode, depth, idx := state.idx + 1 }
  else
    state

private
def scan_string_char
    (state : string_mask_state)
    (char : Char)
    (nextChar : Option Char)
    : string_mask_state :=
  if char == '\\' then
    { state with
      mask := if nextChar == some '\n' then state.mask.push true else state.mask
      idx := state.idx + 1
    }
  else if char == '"' then { state with mode := 0 } else state

private
def scan_raw_string_char
    (context : string_mask_context)
    (state : string_mask_state)
    (char : Char)
    : string_mask_state :=
  if char != '"' then
    state
  else
    Id.run do
      let mut delimiterIdx := state.idx + 1
      let mut hashes := 0
      while delimiterIdx < context.size && context.chars[delimiterIdx]! == '#'
          && hashes < state.depth do
        hashes := hashes + 1
        delimiterIdx := delimiterIdx + 1
      if hashes == state.depth then
        return { state with mode := 0, idx := delimiterIdx - 1 }
      return state

private
def scan_char_literal
    (state : string_mask_state)
    (char : Char)
    (nextChar : Option Char)
    : string_mask_state :=
  if char == '\\' then
    { state with
      mask := if nextChar == some '\n' then state.mask.push false else state.mask
      idx := state.idx + 1
    }
  else if char == '\'' then { state with mode := 0 } else state

private
def scan_mask_char
    (context : string_mask_context)
    (state : string_mask_state)
    : string_mask_state :=
  let char := context.chars[state.idx]!
  let nextChar := context.chars[state.idx + 1]?
  let state :=
    if char == '\n' then
      let mode := if state.mode == 1 || state.mode == 5 then 0 else state.mode
      { state with mode, mask := state.mask.push (mode == 3 || mode == 4) }
    else
      match state.mode with
      | 0 => scan_code_char context state char nextChar
      | 1 => state
      | 2 => scan_block_comment_char state char nextChar
      | 3 => scan_string_char state char nextChar
      | 4 => scan_raw_string_char context state char
      | _ => scan_char_literal state char nextChar
  { state with prev := char, idx := state.idx + 1 }

/-- Which lines of a block START inside a multi-line STRING token (string or
    raw string — a string-gap `\⏎` continuation keeps string mode across the
    newline). Such lines are TOKEN INTERIOR: their leading whitespace is part
    of the token's raw bytes (the gate's token equality compares them), so
    re-anchoring must emit them at their ORIGINAL absolute column. One Bool
    per `splitLines` line, first line `false` (a verbatim starts at a token
    boundary). Mirrors the `stripTrailingWs` mode machine. -/
def in_string_line_mask (chars : List Char) : List Bool :=
  Id.run do
    let context : string_mask_context := { chars := chars.toArray, size := chars.length }
    let mut state : string_mask_state := {}
    while state.idx < context.size do
      state := scan_mask_char context state
    return state.mask.toList

/-- `wrLines` with the in-string mask: a masked line is STRING-TOKEN INTERIOR
    and emits byte-exact at its original absolute column (indent 0, no
    dedent) — re-indenting it would rewrite the token's bytes (gate-caught on
    aleph FindBytesGate: a string-gap continuation, tokens class). -/
def wr_lines_m (indent base : Nat) : List (List Char) → List Bool → rst → rst
  | [], _, state => state
  | leading :: lsValue, candidate, state =>
    let state :=
      if candidate.headD false then
        writeResult { state with pend := state.pend + 1 } 0 (String.ofList leading)
      else
        wr_line state indent base leading
    wr_lines_m indent base lsValue (candidate.drop 1) state

/-- Emit a possibly-multi-line block (verbatim/comment), re-anchored to `indent`:
    dedent every continuation by the block's OWN base column `base`, re-indent to
    `indent` (§0.3) — EXCEPT lines inside a multi-line string token, which keep
    their absolute column byte-exact (`wrLinesM`). Trailing whitespace is trimmed
    (so trailing blank lines cannot exist); leading blank lines are dropped. -/
def wr_block (state : rst) (indent : Nat) (base : Nat) (raw : String) : rst :=
  let chars := trim_end_ws raw.toList
  let lines := split_lines chars
  let leadingCount := (lines.takeWhile is_blank_line).length
  match lines.drop leadingCount, (in_string_line_mask chars).drop leadingCount with
  | [], _ => state
  | leading :: rest, candidate =>
    wr_lines_m
      indent
      base
      rest
      (candidate.drop 1)
      (writeResult state indent (String.ofList leading))

/-- Pad-and-join one table row from rendered cell strings: every cell but the
    last is padded to its column width and followed by `sep`. Recursive (not a
    loop) so the Proofs module can reason by induction. -/
def render_row_str (sep : String) : List Nat → List String → String
  | _, [] => ""
  | _, [headChar] => headChar
  | widths, headChar :: tailChars =>
    headChar ++ spaces ((widths.headD 0) - headChar.length) ++ sep
        ++ render_row_str sep (widths.drop 1) tailChars

/-- Emit padded table rows: the first row at the current position, each
    subsequent row on its own line at `indent`. Named so the Proofs module can
    state its content law once for both alignTable and alignOr. -/
def emit_table
    (maxPend indent : Nat)
    (sep : String)
    (widths : List Nat)
    (strRows : List (List String))
    (state : rst)
    : rst :=
  (
    strRows.foldl
      (
        fun (progress : rst × Bool) row =>
          let state :=
            if progress.2 then
              progress.1
            else
              { progress.1 with pend := Nat.min (progress.1.pend + 1) maxPend }
          (writeResult state indent (render_row_str sep widths row), false)
      )
      (state, true)
  ).1

@[simp]
def go_basic? (maxPend indent : Nat) (doc : Doc) (flat : Bool) (state : rst) : Option rst :=
  match doc with
  | .nil => some state
  | .text text => some (writeResult state indent text)
  | .textRaw text =>
    let state :=
      if state.pend > 0 then
        { out := state.out ++ newlines state.pend ++ spaces indent, col := indent, pend := 0 }
      else
        state
    if text.toList.any (· == '\n') then
      some { state with out := state.out ++ text, col := ((text.splitOn "\n").getLast!).length }
    else
      some { state with out := state.out ++ text, col := state.col + text.length }
  | .verbatim text base => some (wr_block state indent base text)
  | .line =>
    some
      (
        if flat then
          writeResult state indent " "
        else
          { state with pend := Nat.min (state.pend + 1) maxPend }
      )
  | .softline =>
    some (if flat then state else { state with pend := Nat.min (state.pend + 1) maxPend })
  | .hardline => some { state with pend := Nat.min (state.pend + 1) maxPend }
  | .blank requested => some { state with pend := Nat.min (state.pend + 1 + requested) maxPend }
  | .pad _ => some state
  | _ => none

mutual

/-- The rendering step, named and total so the Proofs module can state laws
    about it. `width`/`maxPend` are style constants; `indent` is the
    compositional break indent; `flat` forces flat mode. -/
def renderLoop (width maxPend : Nat) : Doc → Nat → Bool → rst → rst
  | .cat left right, indent, flat, state =>
    renderLoop width maxPend right indent flat (renderLoop width maxPend left indent flat state)
  | .group doc, indent, flat, state =>
    -- flat context is sticky (the `flatten` contract); otherwise fit at the
    -- EFFECTIVE column (pending newlines land at `indent`)
    let effCol := if state.pend > 0 then indent else state.col
    let canFlat := flat
      || (match flat_width doc with
          | some flatWidth => decide (effCol + flatWidth + pad_width doc ≤ width)
          | none => false)
    renderLoop width maxPend doc indent canFlat state
  | .flatten doc, indent, _, state => renderLoop width maxPend doc indent true state
  | .nest amount doc, indent, flat, state =>
    renderLoop width maxPend doc (Int.toNat ((indent : Int) + amount)) flat state
  | .align doc, indent, flat, state =>
    -- anchor at the EFFECTIVE column: with newlines pending the next content
    -- lands at `indent`, and the stale `st.col` is the PREVIOUS line's end
    -- (the group fit-check learned this first; align re-learned it via the
    -- bullet outer-align, which anchored member bullets at the prior line's
    -- end column — gate-caught on mathlib PiSystem, tokens)
    renderLoop width maxPend doc (if state.pend > 0 then indent else state.col) flat state
  | .fillSep items, indent, flat, state =>
    -- pack items with single spaces, wrapping at the width; in FLAT mode
    -- everything stays on one line (the flatten contract — flatWidth is exact
    -- for fillSep; see Proofs)
    goFill width maxPend items indent flat true state
  | .alignTable spec rows, indent, _, state =>
    go_align_table width maxPend (.alignTable spec rows) indent state
  | .align_or spec rows fallback, indent, flat, state =>
    go_align_or width maxPend (.align_or spec rows fallback) indent flat state
  | doc, indent, flat, state => (go_basic? maxPend indent doc flat state).getD state

@[simp]
def go_align_table
    (width maxPend : Nat)
    (doc : Doc)
    (indent : Nat)
    (state : rst)
    : rst :=
  match doc with
  | .alignTable spec rows =>
    let strRows := goCellsRows width maxPend rows indent
    let columnCount := strRows.foldl (fun count row => Nat.max count row.length) 0
    let maximum (column : Nat) : Nat :=
      strRows.foldl (fun size row => Nat.max size ((row[column]?.getD "").length)) 0
    let deltaOk := (List.range columnCount).all fun column =>
      column + 1 == columnCount
        || decide (maximum column
            - strRows.foldl (fun size row => Nat.min size ((row[column]?.getD "").length)) 1000000
            ≤ spec.maxDelta)
    let widths := (List.range columnCount).map fun column => if deltaOk then maximum column else 0
    emit_table maxPend indent spec.sep widths strRows state
  | _ => state

@[simp]
def go_align_or
    (width maxPend : Nat)
    (doc : Doc)
    (indent : Nat)
    (flat : Bool)
    (state : rst)
    : rst :=
  match doc with
  | .align_or spec rows fallback =>
    -- in FLAT context the grid is out of the question (the flatten contract:
    -- flatWidth (alignOr) speaks about the fallback) — render the fallback flat
    if flat then renderLoop width maxPend fallback indent true state else
    -- flat fallback when it fits; the grid when the delta guardrail holds AND
    -- every padded row fits; the ordinary fallback otherwise
    let effCol := if state.pend > 0 then indent else state.col
    let flatFits : Bool := match flat_width fallback with
      | some widthBinding => decide (effCol + widthBinding ≤ width)
      | none => false
    if flatFits then renderLoop width maxPend fallback indent flat state else
    let strRows := goCellsRows width maxPend rows indent
    let ncol := strRows.foldl (fun maximum row => Nat.max maximum row.length) 0
    let maxOf (columnIndex : Nat) : Nat :=
      strRows.foldl
        (fun maximum row => Nat.max maximum ((row[columnIndex]?.getD "").length))
        0
    let minOf (columnIndex : Nat) : Nat :=
      strRows.foldl
        (fun minimum row =>
          if columnIndex < row.length then
            Nat.min minimum ((row[columnIndex]?.getD "").length)
          else
            minimum)
        1000000
    let deltaOk := (List.range ncol).all fun columnIndex =>
      columnIndex + 1 == ncol
          || decide (maxOf columnIndex - minOf columnIndex ≤ spec.maxDelta)
    let widths := (List.range ncol).map maxOf
    let rowsFit := strRows.all fun row =>
      decide (indent + (render_row_str spec.sep widths row).length ≤ width)
    -- coherence BY CONSTRUCTION: the grid is taken only when its content
    -- provably equals the fallback's — an incoherent emitter degrades to the
    -- fallback instead of corrupting (and render_content holds unconditionally)
    let gridContent :=
      (strRows.map fun row => non_ws (render_row_str spec.sep widths row)).flatten
    if deltaOk && rowsFit && decide (rows.length ≥ 2)
        && decide (gridContent = content fallback) then
      emit_table maxPend indent spec.sep widths strRows state
    else renderLoop width maxPend fallback indent flat state
  | _ => state

/-- Fill packing: each item rendered flat; wrap (in non-flat mode) when the
    next item would cross the width. -/
def goFill (width maxPend : Nat) : List Doc → Nat → Bool → Bool → rst → rst
  | [], _, _, _, state => state
  | indentBinding :: indents, indent, flat, first, state =>
    let text := (renderLoop width maxPend indentBinding indent true {}).out
    let state :=
      if first then writeResult state indent text
      else
        let effCol := if state.pend > 0 then indent else state.col
        if !flat && decide (effCol + 1 + text.length > width) then
          writeResult { state with pend := Nat.min (state.pend + 1) maxPend } indent text
        else writeResult state indent (" " ++ text)
    goFill width maxPend indents indent flat false state

/-- Render every cell of every row flat, to strings. -/
def goCellsRows (width maxPend : Nat) : List (List Doc) → Nat → List (List String)
  | [], _ => []
  | row :: rows, indent => goCells width maxPend row indent :: goCellsRows width maxPend rows indent

def goCells (width maxPend : Nat) : List Doc → Nat → List String
  | [], _ => []
  | headChar :: tailChars, indent => (renderLoop width maxPend headChar indent true {}).out :: goCells width maxPend tailChars indent

end

/-- Consume the character following a string/character escape, if present. -/
private
def consume_escape (out : Array Char) (idx : Nat) (next? : Option Char) : Array Char × Nat :=
  match next? with
  | some next => (out.push next, idx + 1)
  | none      => (out, idx)

private
structure trailing_context where
  chars : Array Char
  size  : Nat

private
structure trailing_state where
  mode       : Nat := 0
  depth      : Nat := 0
  docComment : Bool := false
  prev       : Char := ' '
  out        : Array Char := #[]
  idx        : Nat := 0

private partial
def strip_array_end (chars : Array Char) : Array Char :=
  if let some char := chars.back? then
    if char == ' ' || char == '\t' then strip_array_end chars.pop else chars
  else
    chars

private
def push_range (source : Array Char) (first past : Nat) (target : Array Char) : Array Char :=
  (List.range' first (past - first)).foldl (fun result idx => result.push source[idx]!) target

private
def trailing_code_step
    (context : trailing_context)
    (state : trailing_state)
    (char : Char)
    (nextChar : Option Char)
    : trailing_state :=
  if char == '\n' then
    { state with out := (strip_array_end state.out).push char }
  else if char == '-' && nextChar == some '-' then
    { state with mode := 1, out := (state.out.push char).push '-', idx := state.idx + 1 }
  else if char == '/' && nextChar == some '-' then
    { state with
      mode := 2
      depth := 1
      docComment := context.chars[state.idx + 2]? == some '-'
          || context.chars[state.idx + 2]? == some '!'
      out := (state.out.push char).push '-'
      idx := state.idx + 1
    }
  else if char == '"' then
    { state with mode := 3, out := state.out.push char }
  else if char == 'r' && !is_identifier_char state.prev
      && (nextChar == some '"' || nextChar == some '#') then
    let scanned :=
      scan_raw_delimiter
        { chars := context.chars, size := context.size }
        { mode := state.mode, depth := state.depth, prev := state.prev, idx := state.idx }
    if scanned.mode == 4 then
      { state with
        mode := 4
        depth := scanned.depth
        out := push_range context.chars state.idx (scanned.idx + 1) state.out
        idx := scanned.idx
      }
    else
      { state with out := state.out.push char }
  else if char == '\'' && !is_identifier_char state.prev then
    { state with mode := 5, out := state.out.push char }
  else
    { state with out := state.out.push char }

private
def trailing_block_step
    (state : trailing_state)
    (char : Char)
    (nextChar : Option Char)
    : trailing_state :=
  if char == '\n' then
    { state with
      out := (if state.docComment then state.out else strip_array_end state.out).push char }
  else if char == '/' && nextChar == some '-' then
    { state with
      depth := state.depth + 1
      out := (state.out.push char).push '-'
      idx := state.idx + 1
    }
  else if char == '-' && nextChar == some '/' then
    let depth := state.depth - 1
    { state with
      mode := if depth == 0 then 0 else state.mode
      depth
      out := (state.out.push char).push '/'
      idx := state.idx + 1
    }
  else
    { state with out := state.out.push char }

private
def trailing_string_step
    (state : trailing_state)
    (char : Char)
    (nextChar : Option Char)
    : trailing_state :=
  if char == '\\' then
    let escaped := consume_escape (state.out.push char) state.idx nextChar
    { state with out := escaped.1, idx := escaped.2 }
  else
    { state with mode := if char == '"' then 0 else state.mode, out := state.out.push char }

private
def trailing_raw_step
    (context : trailing_context)
    (state : trailing_state)
    (char : Char)
    : trailing_state :=
  if char != '"' then
    { state with out := state.out.push char }
  else
    let scanned :=
      scan_raw_string_char
        { chars := context.chars, size := context.size }
        { mode := state.mode, depth := state.depth, prev := state.prev, idx := state.idx }
        char
    if scanned.mode == 0 then
      { state with
        mode := 0
        out := push_range context.chars state.idx (scanned.idx + 1) state.out
        idx := scanned.idx
      }
    else
      { state with out := state.out.push char }

private
def trailing_char_step
    (state : trailing_state)
    (char : Char)
    (nextChar : Option Char)
    : trailing_state :=
  if char == '\\' then
    let escaped := consume_escape (state.out.push char) state.idx nextChar
    { state with out := escaped.1, idx := escaped.2 }
  else
    let mode := if char == '\'' || char == '\n' then 0 else state.mode
    let out := if char == '\n' then (strip_array_end state.out).push char else state.out.push char
    { state with mode, out }

private
def trailing_step (context : trailing_context) (state : trailing_state) : trailing_state :=
  let char := context.chars[state.idx]!
  let nextChar := context.chars[state.idx + 1]?
  let state :=
    match state.mode with
    | 0 => trailing_code_step context state char nextChar
    | 1 =>
      if char == '\n' then
        { state with mode := 0, out := (strip_array_end state.out).push char }
      else
        { state with out := state.out.push char }
    | 2 => trailing_block_step state char nextChar
    | 3 => trailing_string_step state char nextChar
    | 4 => trailing_raw_step context state char
    | _ => trailing_char_step state char nextChar
  { state with prev := state.out.back?.getD ' ', idx := state.idx + 1 }

private partial
def scan_trailing (context : trailing_context) (state : trailing_state) : trailing_state :=
  if state.idx < context.size then scan_trailing context (trailing_step context state) else state

/-- Erase whitespace from a string, retaining its semantic character stream. -/
def whitespace_erased (source : String) : List Char :=
  source.toList.filter fun character => !character.isWhitespace

/-- STRING-AWARE trailing-whitespace strip: drop spaces/tabs at every line end
    EXCEPT inside string literals (plain/interpolated/raw), where they are token
    content. Trailing whitespace anywhere else — code, line comments, block
    comments — is trivia the canonical form does not carry (the gate's
    `commentContent` check is whitespace-blind, so comment-tail stripping is
    provably meaning-safe). The scanner tracks the lexical mode at each newline:
    line comments end AT the newline (strippable); block comments nest; `'` opens
    a char literal only after a non-identifier char (else it is a prime); raw
    strings `r#…#"…"#…#` close on a quote followed by their hash count. Inside
    `s!"…{element}…"` the quote-toggle treats interpolation code as string — the
    conservative direction (never strips string content; at worst leaves a space
    inside interpolation code, which the gate would catch anyway). -/
def strip_trailing_ws (source : String) : String :=
  let chars := source.toList.toArray
  let state := scan_trailing { chars, size := chars.size } { out := Array.mkEmpty chars.size }
  let candidate := String.ofList (strip_array_end state.out).toList
  if whitespace_erased candidate == whitespace_erased source then candidate else source

/-- The guarded scanner cannot change the semantic character stream. -/
theorem whitespace_erased_strip_trailing_ws
        (source : String)
        : whitespace_erased (strip_trailing_ws source) = whitespace_erased source := by
  simp only [strip_trailing_ws]
  split
  · next candidateAccepted => exact beq_iff_eq.mp candidateAccepted
  · rfl

private
structure canonical_state where
  mode  : Nat := 0
  depth : Nat := 0
  prev  : Char := ' '
  out   : Array Char := #[]
  idx   : Nat := 0

private
structure newline_scan where
  idx   : Nat
  count : Nat := 0
  last  : Nat

private
def canonical_newline_run
    (context : trailing_context)
    (state : canonical_state)
    : canonical_state :=
  Id.run do
    let mut scan : newline_scan := { idx := state.idx, last := state.idx }
    while scan.idx < context.size
        && (context.chars[scan.idx]! == '\n'
          || context.chars[scan.idx]! == ' '
          || context.chars[scan.idx]! == '\t') do
      if context.chars[scan.idx]! == '\n' then
        scan := { idx := scan.idx, count := scan.count + 1, last := scan.idx }
      scan := { scan with idx := scan.idx + 1 }
    let out := if scan.count ≥ 2 then (state.out.push '\n').push '\n' else state.out.push '\n'
    return { state with out, idx := scan.last }

private
def canonical_space_run (context : trailing_context) (state : canonical_state) : canonical_state :=
  Id.run do
    let lineStart := state.out.isEmpty || state.out.back! == '\n'
    let mut scanIdx := state.idx
    while scanIdx < context.size && context.chars[scanIdx]! == ' ' do
      scanIdx := scanIdx + 1
    let commentNext :=
      (context.chars[scanIdx]? == some '-' && context.chars[scanIdx + 1]? == some '-')
          || (context.chars[scanIdx]? == some '/' && context.chars[scanIdx + 1]? == some '-')
    let afterBrace := !state.out.isEmpty && state.out.back! == '{'
    let out :=
      if lineStart || scanIdx - state.idx == 1 || commentNext || afterBrace then
        push_range context.chars state.idx scanIdx state.out
      else if context.chars[scanIdx]? != some '\n' && scanIdx < context.size then
        state.out.push ' '
      else
        state.out
    return { state with out, idx := scanIdx - 1 }

private
def canonical_dsl_step (context : trailing_context) (state : canonical_state) : canonical_state :=
  Id.run do
    let mut scanIdx := state.idx + 1
    while scanIdx < context.size
        && (context.chars[scanIdx]!.isAlphanum
          || context.chars[scanIdx]! == '_'
          || context.chars[scanIdx]! == '.') do
      scanIdx := scanIdx + 1
    if context.chars[scanIdx]? == some '|' && context.chars[scanIdx + 1]? != some ']' then
      let mut endIdx := scanIdx + 1
      while endIdx + 1 < context.size
          && !(context.chars[endIdx]! == '|' && context.chars[endIdx + 1]! == ']') do
        endIdx := endIdx + 1
      let last := if endIdx + 1 < context.size then endIdx + 1 else context.size - 1
      return { state with
        out := push_range context.chars state.idx (last + 1) state.out
        idx := last
      }
    return { state with out := state.out.push '[' }

private
def canonical_code_step
    (context : trailing_context)
    (state : canonical_state)
    (char : Char)
    (nextChar : Option Char)
    : canonical_state :=
  if char == '\n' then
    canonical_newline_run context state
  else if char == ' ' then
    canonical_space_run context state
  else if char == '[' && (nextChar.map (fun next => next.isAlpha || next == '_')).getD false then
    canonical_dsl_step context state
  else if char == '-' && nextChar == some '-' then
    { state with mode := 1, out := (state.out.push char).push '-', idx := state.idx + 1 }
  else if char == '/' && nextChar == some '-' then
    { state with
      mode := 2,
      depth := 1,
      out := (state.out.push char).push '-',
      idx := state.idx + 1 }
  else if char == '"' then
    { state with mode := 3, out := state.out.push char }
  else if char == 'r' && !is_identifier_char state.prev
      && (nextChar == some '"' || nextChar == some '#') then
    let scanned :=
      scan_raw_delimiter
        { chars := context.chars, size := context.size }
        { mode := state.mode, depth := state.depth, prev := state.prev, idx := state.idx }
    if scanned.mode == 4 then
      { state with
        mode := 4
        depth := scanned.depth
        out := push_range context.chars state.idx (scanned.idx + 1) state.out
        idx := scanned.idx
      }
    else
      { state with out := state.out.push char }
  else if char == '\'' && !is_identifier_char state.prev then
    { state with mode := 5, out := state.out.push char }
  else
    { state with out := state.out.push char }

private
def canonical_block_step
    (state : canonical_state)
    (char : Char)
    (nextChar : Option Char)
    : canonical_state :=
  if char == '/' && nextChar == some '-' then
    { state with
      depth := state.depth + 1
      out := (state.out.push char).push '-'
      idx := state.idx + 1
    }
  else if char == '-' && nextChar == some '/' then
    let depth := state.depth - 1
    { state with
      mode := if depth == 0 then 0 else state.mode
      depth
      out := (state.out.push char).push '/'
      idx := state.idx + 1
    }
  else
    { state with out := state.out.push char }

private
def canonical_string_step
    (state : canonical_state)
    (char : Char)
    (nextChar : Option Char)
    : canonical_state :=
  if char == '\\' then
    let escaped := consume_escape (state.out.push char) state.idx nextChar
    { state with out := escaped.1, idx := escaped.2 }
  else
    { state with mode := if char == '"' then 0 else state.mode, out := state.out.push char }

private
def canonical_raw_step
    (context : trailing_context)
    (state : canonical_state)
    (char : Char)
    : canonical_state :=
  if char != '"' then
    { state with out := state.out.push char }
  else
    let scanned :=
      scan_raw_string_char
        { chars := context.chars, size := context.size }
        { mode := state.mode, depth := state.depth, prev := state.prev, idx := state.idx }
        char
    if scanned.mode == 0 then
      { state with
        mode := 0
        out := push_range context.chars state.idx (scanned.idx + 1) state.out
        idx := scanned.idx
      }
    else
      { state with out := state.out.push char }

private
def canonical_char_step
    (state : canonical_state)
    (char : Char)
    (nextChar : Option Char)
    : canonical_state :=
  if char == '\\' then
    let escaped := consume_escape (state.out.push char) state.idx nextChar
    { state with out := escaped.1, idx := escaped.2 }
  else
    { state with
      mode := if char == '\'' || char == '\n' then 0 else state.mode
      out := state.out.push char
    }

private
def canonical_step (context : trailing_context) (state : canonical_state) : canonical_state :=
  let char := context.chars[state.idx]!
  let nextChar := context.chars[state.idx + 1]?
  let state :=
    match state.mode with
    | 0 => canonical_code_step context state char nextChar
    | 1 =>
      if char == '\n' then
        { state with mode := 0, idx := state.idx - 1 }
      else
        { state with out := state.out.push char }
    | 2 => canonical_block_step state char nextChar
    | 3 => canonical_string_step state char nextChar
    | 4 => canonical_raw_step context state char
    | _ => canonical_char_step state char nextChar
  { state with prev := state.out.back?.getD ' ', idx := state.idx + 1 }

private partial
def scan_canonical (context : trailing_context) (state : canonical_state) : canonical_state :=
  if state.idx < context.size then scan_canonical context (canonical_step context state) else state

/-- Canonical whitespace for OPAQUE (verbatim) block content — the zero-
    passthrough closure for constructs the walker has not ported. Two rules,
    both restricted to CODE (the same lexical modes as `stripTrailingWs`):

    * interior runs of 2+ spaces collapse to one — EXCEPT line-leading runs
      (indentation is layout, and Lean's column sensitivity binds at line
      starts) and runs directly before a comment opener (line or block),
      which carry trailing-comment alignment;
    * runs of newlines collapse to at most one blank line (the §8 clamp,
      textually) — 0-vs-1 blank adjacency survives, run LENGTH does not.

    String/char/raw-string interiors and comment interiors (line and block)
    are token/comment content — untouched. Both rules are idempotent, and
    token text is unchanged, so the gate's leafToks law is preserved by
    construction. -/
/- Retained during the state-machine transition for a line-by-line semantic audit.
def canon_verbatim_ws_legacy (s : String) : String :=
  Id.run
    do
      let a : Array Char := s.toList.toArray
      let n := a.size
      let isIdChar :=
        fun (c : Char) =>
          c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || c.val > 127
      -- modes: 0 code, 1 line comment, 2 block comment, 3 string, 4 raw string, 5 char
      let mut mode : Nat := 0
      let mut depth : Nat := 0
      let mut prev : Char := ' '
      let mut out : Array Char := Array.mkEmpty n
      let mut i := 0
      while _h : i < n do
        let c := a[i]!
        let c1 := a[i + 1]?
        match mode with
        | 0 =>
          if c == '\n' then
            -- newline RUN: consume spaces/newlines ahead; k newlines = k-1 blank
            -- lines; emit min(k,2) newlines and resume at the LAST one so the
            -- final line's indentation flows through untouched
            let mut j := i
            let mut k := 0
            let mut last := i
            while _hj : j < n && (a[j]! == '\n' || a[j]! == ' ' || a[j]! == '\t') do
              if a[j]! == '\n' then k := k + 1; last := j
              j := j + 1
            out := if k ≥ 2 then (out.push '\n').push '\n' else out.push '\n'
            i := last
          else if c == ' ' then
            let lineStart := out.isEmpty || out.back! == '\n'
            let mut j := i
            while _hj : j < n && a[j]! == ' ' do j := j + 1
            let commentNext := (a[j]? == some '-' && a[j+1]? == some '-')
              || (a[j]? == some '/' && a[j+1]? == some '-')
            -- ws-sensitivity CLASS 4 (Emit/WsSensitivity, mirrored in
            -- fuzz/perturb.py): the run after a `{` is exempt — a
            -- newline-separated structInst aligns its fields by COLUMN and
            -- `{  f := v` sets that column; collapsing it shifted the first
            -- field and the output failed to reparse. Exemptions here stay
            -- LEXICAL AND NARROW, never subtree-wide.
            let afterBrace := !out.isEmpty && out.back! == '{'
            if lineStart || j - i == 1 || commentNext || afterBrace then
              for k in [i:j] do out := out.push a[k]!
            else if a[j]? != some '\n' && j < n then
              out := out.push ' '
            -- (run before a newline or at end: trailing ws, dropped)
            i := j - 1
          else if c == '[' && (c1.map (fun x => x.isAlpha || x == '_')).getD false then
            -- DSL template candidate `[ident| … |]`: the interior is CONTENT
            -- (the quasiquotation pin) — copy verbatim through the closing `|]`
            let mut j := i + 1
            while _hj : j < n && (a[j]!.isAlphanum || a[j]! == '_' || a[j]! == '.') do
              j := j + 1
            if (a[j]? == some '|') && a[j+1]? != some ']' then
              let mut e := j + 1
              while _he : e + 1 < n && !(a[e]! == '|' && a[e+1]! == ']') do e := e + 1
              let last := if e + 1 < n then e + 1 else n - 1
              for m in [i:last+1] do out := out.push a[m]!
              i := last
            else
              out := out.push c
          else if c == '-' && c1 == some '-' then
            mode := 1; out := (out.push c).push '-'; i := i + 1
          else if c == '/' && c1 == some '-' then
            mode := 2; depth := 1
            out := (out.push c).push '-'; i := i + 1
          else if c == '"' then
            mode := 3; out := out.push c
          else if c == 'r' && !isIdChar prev && (c1 == some '"' || c1 == some '#') then
            let mut j := i + 1
            let mut hs := 0
            while _hj : j < n && a[j]! == '#' do hs := hs + 1; j := j + 1
            if a[j]? == some '"' then
              mode := 4; depth := hs
              for k in [i:j+1] do out := out.push a[k]!
              i := j
            else
              out := out.push c
          else if c == '\'' && !isIdChar prev then
            mode := 5; out := out.push c
          else
            out := out.push c
        | 1 =>  -- line comment: interior is content; the newline closes AND starts
                -- a code-mode run (step back onto it so the run rule applies)
          if c == '\n' then mode := 0; i := i - 1
          else out := out.push c
        | 2 =>  -- block comment (nested): interior is content, blank lines included
          if c == '/' && c1 == some '-' then
            depth := depth + 1; out := (out.push c).push '-'; i := i + 1
          else if c == '-' && c1 == some '/' then
            depth := depth - 1; out := (out.push c).push '/'; i := i + 1
            if depth == 0 then mode := 0
          else out := out.push c
        | 3 =>  -- string literal: content
          if c == '\\' then
            out := out.push c
            let escaped := consume_escape out i c1
            out := escaped.1
            i := escaped.2
          else
            if c == '"' then mode := 0
            out := out.push c
        | 4 =>  -- raw string: closes on `"` + depth hashes; interior is content
          if c == '"' then
            let mut j := i + 1
            let mut hs := 0
            while _hj : j < n && a[j]! == '#' && hs < depth do hs := hs + 1; j := j + 1
            if hs == depth then
              mode := 0
              for k in [i:j] do out := out.push a[k]!
              i := j - 1
            else
              out := out.push c
          else out := out.push c
        | _ =>  -- char literal (or prime-misparse recovery on newline)
          if c == '\\' then
            out := out.push c
            let escaped := consume_escape out i c1
            out := escaped.1
            i := escaped.2
          else
            if c == '\'' || c == '\n' then mode := 0
            out := out.push c
        prev := (out.back?).getD ' '
        i := i + 1
      return String.ofList out.toList
-/

def canon_verbatim_ws (text : String) : String :=
  let chars := text.toList.toArray
  let state := scan_canonical { chars, size := chars.size } { out := Array.mkEmpty chars.size }
  String.ofList state.out.toList

/-- Render a `Doc` to a string under `style`. -/
def render (style : Style) (doc : Doc) : String :=
  let state :=
    renderLoop style.layout.lineWidth (style.blankLines.maxConsecutive + 1) doc 0 false {}
  -- trailing whitespace is trivia everywhere outside string literals — the
  -- string-aware strip is what makes verbatim blocks canonical at line ends
  let out := strip_trailing_ws state.out
  if out.endsWith "\n" then out else out ++ "\n"

end Lean4Fmt.Doc
