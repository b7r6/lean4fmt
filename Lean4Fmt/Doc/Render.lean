/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // LEAN4FMT // DOC // RENDER
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Width-aware layout: `Style → Doc → String` (DESIGN_V2 §4). A pragmatic
    Wadler/Leijen renderer: `group` picks flat-or-break by fit; `nest`/`align`
    set the break indent COMPOSITIONALLY (§0.2); `verbatim` re-anchors an opaque
    block to the current indent (§0.3, §4.1); `blank` is clamped by policy (§8).

    TOTAL: every function is total — the container constructors hold Lists, so
    the walkers use structural mutual recursion. The laws in `Lean4Fmt/Proofs`
    are stated about THESE functions, not a model.

    Pure. Depends on Doc.Core + Style.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Doc.Core
import Lean4Fmt.Doc.Content
import Lean4Fmt.Style

namespace Lean4Fmt.Doc

open Lean4Fmt.Style

mutual

/-- Flat width of a doc, or `none` if it cannot be flattened. -/
def flatWidth : Doc → Option Nat
  | .nil => some 0
  | .text s => some s.length
  | .cat a b => match flatWidth a, flatWidth b with
    | some x, some y => some (x + y)
    | _, _ => none
  | .line => some 1
  | .softline => some 0
  | .hardline => none
  | .group d => flatWidth d
  | .nest _ d => flatWidth d
  | .align d => flatWidth d
  | .flatten d => flatWidth d
  | .textRaw s => if s.toList.any (· == '\n') then none else some s.length
  -- must be EXACT for what wrBlock emits on a single line (Proofs T2): the
  -- line is trailing-trimmed, leading whitespace KEPT
  | .verbatim s _ => if s.toList.any (· == '\n') then none else some (trimEndWs s.toList).length
  | .blank _ => none
  -- pad renders NOTHING in flat mode — 0 keeps T2 (flat exactness); group
  -- fits count the phantom width separately via `padWidth`
  | .pad _ => some 0
  | .alignTable _ _ => none
  | .alignOr _ _ fb => flatWidth fb
  | .fillSep [] => some 0
  | .fillSep (i :: is) =>
    match flatWidth i, flatWidthSep is with
    | some w, some ws => some (w + ws)
    | _, _ => none

/-- Sum of flat widths of the tail items, each preceded by one space. -/
def flatWidthSep : List Doc → Option Nat
  | [] => some 0
  | i :: is =>
    match flatWidth i, flatWidthSep is with
    | some w, some ws => some (1 + w + ws)
    | _, _ => none

end

/-- Total phantom `pad` width in a doc — a group fit adds this ON TOP of
    `flatWidth` (which stays render-exact, reporting pad as 0): the reserve
    for un-breakable text the caller appends after the group. -/
def padWidth : Doc → Nat
  | .pad n => n
  | .cat a b => padWidth a + padWidth b
  | .group d | .nest _ d | .align d | .flatten d => padWidth d
  | _ => 0

mutual

/-- Whether a doc contains a multi-line opaque block (`verbatim`/`textRaw` with a
    newline). Such blocks re-anchor by column, which is only idempotent at their
    natural top-level position — so a subtree containing one must NOT be laid out
    actively (it stays on the safe whole-span path). Hardlines are fine. -/
def hasMultilineVerbatim : Doc → Bool
  | .verbatim s _ => s.any (· == '\n')
  | .textRaw s => s.any (· == '\n')
  | .cat a b => hasMultilineVerbatim a || hasMultilineVerbatim b
  | .group d | .nest _ d | .align d | .flatten d => hasMultilineVerbatim d
  | .alignTable _ rows => hasMLRows rows
  | .alignOr _ _ fb => hasMultilineVerbatim fb
  | .fillSep items => hasMLList items
  | _ => false

/-- Whether a doc contains a multi-line RE-ANCHORING block — `.verbatim` only.
    `.textRaw` (docstrings, comment blocks) emits its lines RAW at their source
    columns, indifferent to placement indent, so it is placement-stable; only
    `.verbatim` dedents/re-indents by column. The mutual member bail cares
    about exactly the re-anchoring class — counting textRaw kept every member
    with a MULTI-LINE DOCSTRING (and its whole mutual) verbatim. -/
def hasMultilineReanchor : Doc → Bool
  | .verbatim s _ => s.any (· == '\n')
  | .cat a b => hasMultilineReanchor a || hasMultilineReanchor b
  | .group d | .nest _ d | .align d | .flatten d => hasMultilineReanchor d
  | .alignTable _ rows => hasMRRows rows
  | .alignOr _ _ fb => hasMultilineReanchor fb
  | .fillSep items => hasMRList items
  | _ => false

def hasMRList : List Doc → Bool
  | [] => false
  | d :: ds => hasMultilineReanchor d || hasMRList ds

def hasMRRows : List (List Doc) → Bool
  | [] => false
  | r :: rs => hasMRList r || hasMRRows rs

def hasMLList : List Doc → Bool
  | [] => false
  | d :: ds => hasMultilineVerbatim d || hasMLList ds

def hasMLRows : List (List Doc) → Bool
  | [] => false
  | r :: rs => hasMLList r || hasMLRows rs

end

mutual

/-- Coverage accounting (DESIGN_V2 §15): (active, verbatim, trivia) bytes. -/
def stats : Doc → (Nat × Nat × Nat)
  | .text s => (s.utf8ByteSize, 0, 0)
  | .verbatim s _ => (0, s.utf8ByteSize, 0)
  | .textRaw s => (0, 0, s.utf8ByteSize)
  | .cat a b =>
    let (a1, v1, t1) := stats a
    let (a2, v2, t2) := stats b
    (a1 + a2, v1 + v2, t1 + t2)
  | .group d | .nest _ d | .align d | .flatten d => stats d
  | .alignTable _ rows => statsRows rows
  | .alignOr _ _ fb => stats fb
  | .fillSep items => statsList items
  | _ => (0, 0, 0)

def statsList : List Doc → (Nat × Nat × Nat)
  | [] => (0, 0, 0)
  | d :: ds =>
    let (a1, v1, t1) := stats d
    let (a2, v2, t2) := statsList ds
    (a1 + a2, v1 + v2, t1 + t2)

def statsRows : List (List Doc) → (Nat × Nat × Nat)
  | [] => (0, 0, 0)
  | r :: rs =>
    let (a1, v1, t1) := statsList r
    let (a2, v2, t2) := statsRows rs
    (a1 + a2, v1 + v2, t1 + t2)

end

/-- Width a doc contributes to the CURRENT line, up to its first possible break
    point, plus whether such a break was reached. A `flatten` never breaks, so
    it contributes its full flat width. -/
def firstLineWidth : Doc → Nat × Bool
  | .nil => (0, false)
  | .text s => (s.length, false)
  | .textRaw s =>
    let ls := s.splitOn "\n"; ((ls.headD "").length, ls.length > 1)
  | .verbatim s _ =>
    let ls := s.splitOn "\n"; ((ls.headD "").length, ls.length > 1)
  | .line | .softline | .hardline | .blank _ => (0, true)
  | .pad _ => (0, false)
  | .cat a b =>
    let (wa, ba) := firstLineWidth a
    if ba then (wa, true) else let (wb, bb) := firstLineWidth b; (wa + wb, bb)
  | .group d | .nest _ d | .align d => firstLineWidth d
  | .flatten d => match flatWidth d with | some w => (w, false) | none => firstLineWidth d
  | .alignTable _ _ => (0, true)
  | .alignOr _ _ fb => firstLineWidth fb
  | .fillSep [] => (0, false)
  | .fillSep (i :: is) => ((flatWidth i).getD 0, !is.isEmpty)

def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')
def newlines (n : Nat) : String := String.ofList (List.replicate n '\n')

structure RSt where
  out  : String := ""
  col  : Nat := 0
  pend : Nat := 0        -- pending newlines (for blank collapsing)
  deriving Inhabited

/-- Emit single-line visible text at break-indent `indent`, flushing pending
    newlines (with indentation) first. `wr` never writes the indent without
    content after it (the hygiene law in Proofs). -/
def wr
    (st : RSt)
    (indent : Nat)
    (s : String)
    : RSt :=
  let st := if st.pend > 0
    then { out := st.out ++ newlines st.pend ++ spaces indent, col := indent, pend := 0 }
    else st
  { st with out := st.out ++ s, col := st.col + s.length }

/-- Split a char list on '\n' (never returns `[]`; `[]` input → one empty line
    — the char-list twin of `splitOn "\n"`, owned so Proofs can induct). -/
def splitLines : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    match splitLines cs with
    | [] => [[c]]                                   -- unreachable (never nil)
    | l :: ls => if c = '\n' then [] :: l :: ls else (c :: l) :: ls

/-- A line of nothing but spaces (the blank-line notion of `wrBlock`; NOT full
    whitespace — a tab-bearing line may be string-literal interior). -/
def isBlankLine (l : List Char) : Bool := l.all (· == ' ')

/-- One continuation line of a block: dedent, then emit behind one pending
    newline. Dedent drops ONLY spaces: if the first `base` chars aren't all
    spaces (a continuation less indented than its head), fall back to stripping
    just the leading spaces — dropping `base` chars unconditionally would eat
    CONTENT on such lines (latent until the content-preservation theorem in
    Proofs demanded it be impossible). Lines dedented to empty stay pending. -/
def dedent (base : Nat) (l : List Char) : List Char :=
  if l.length ≥ base && (l.take base).all (· == ' ')
    then l.drop base
    else l.dropWhile (· == ' ')

def wrLine (st : RSt) (indent base : Nat) (l : List Char) : RSt :=
  if (dedent base l).isEmpty then { st with pend := st.pend + 1 }
  else wr { st with pend := st.pend + 1 } indent (String.ofList (dedent base l))

def wrLines (indent base : Nat) : List (List Char) → RSt → RSt
  | [], st => st
  | l :: ls, st => wrLines indent base ls (wrLine st indent base l)

/-- Emit a possibly-multi-line block (verbatim/comment), re-anchored to `indent`:
    dedent every continuation by the block's OWN base column `base`, re-indent to
    `indent` (§0.3). Trailing whitespace is trimmed (so trailing blank lines
    cannot exist); leading blank lines are dropped. -/
def wrBlock
    (st : RSt)
    (indent : Nat)
    (base : Nat)
    (raw : String)
    : RSt :=
  match (splitLines (trimEndWs raw.toList)).dropWhile isBlankLine with
  | [] => st
  | l :: rest => wrLines indent base rest (wr st indent (String.ofList l))

/-- Pad-and-join one table row from rendered cell strings: every cell but the
    last is padded to its column width and followed by `sep`. Recursive (not a
    loop) so the Proofs module can reason by induction. -/
def renderRowStr
    (sep : String)
    : List Nat → List String → String
  | _, [] => ""
  | _, [c] => c
  | widths, c :: cs =>
    c ++ spaces ((widths.headD 0) - c.length) ++ sep
      ++ renderRowStr sep (widths.drop 1) cs

/-- Emit padded table rows: the first row at the current position, each
    subsequent row on its own line at `indent`. Named so the Proofs module can
    state its content law once for both alignTable and alignOr. -/
def emitTable (maxPend indent : Nat) (sep : String) (widths : List Nat)
    (strRows : List (List String)) (st : RSt) : RSt :=
  (strRows.foldl (fun (p : RSt × Bool) r =>
    let st := if p.2 then p.1 else { p.1 with pend := Nat.min (p.1.pend + 1) maxPend }
    (wr st indent (renderRowStr sep widths r), false)) (st, true)).1

mutual

/-- The rendering step, named and total so the Proofs module can state laws
    about it. `width`/`maxPend` are style constants; `indent` is the
    compositional break indent; `flat` forces flat mode. -/
def go (width maxPend : Nat) : Doc → Nat → Bool → RSt → RSt
  | .nil, _, _, st => st
  | .text s, indent, _, st => wr st indent s
  | .textRaw s, indent, _, st =>
    let st := if st.pend > 0
      then { out := st.out ++ newlines st.pend ++ spaces indent, col := indent, pend := 0 } else st
    -- single-line: col ADVANCES (it used to reset to s.length, silently
    -- misinforming every later fit decision on the line — found by T2)
    if s.toList.any (· == '\n') then
      { st with out := st.out ++ s, col := ((s.splitOn "\n").getLast!).length }
    else
      { st with out := st.out ++ s, col := st.col + s.length }
  | .verbatim s b, indent, _, st => wrBlock st indent b s
  | .cat a b, indent, flat, st => go width maxPend b indent flat (go width maxPend a indent flat st)
  | .line, indent, flat, st =>
    if flat then wr st indent " " else { st with pend := Nat.min (st.pend + 1) maxPend }
  | .softline, _, flat, st => if flat then st else { st with pend := Nat.min (st.pend + 1) maxPend }
  | .hardline, _, _, st => { st with pend := Nat.min (st.pend + 1) maxPend }
  | .blank req, _, _, st => { st with pend := Nat.min (st.pend + 1 + req) maxPend }
  | .group d, indent, flat, st =>
    -- flat context is sticky (the `flatten` contract); otherwise fit at the
    -- EFFECTIVE column (pending newlines land at `indent`)
    let effCol := if st.pend > 0 then indent else st.col
    let canFlat := flat
      || (match flatWidth d with
          | some w => decide (effCol + w + padWidth d ≤ width)
          | none => false)
    go width maxPend d indent canFlat st
  | .flatten d, indent, _, st => go width maxPend d indent true st
  | .pad _, _, _, st => st
  | .nest n d, indent, flat, st => go width maxPend d (Int.toNat ((indent : Int) + n)) flat st
  | .align d, _, flat, st => go width maxPend d st.col flat st
  | .fillSep items, indent, flat, st =>
    -- pack items with single spaces, wrapping at the width; in FLAT mode
    -- everything stays on one line (the flatten contract — flatWidth is exact
    -- for fillSep; see Proofs)
    goFill width maxPend items indent flat true st
  | .alignTable spec rows, indent, _, st =>
    let strRows := goCellsRows width maxPend rows indent
    let ncol := strRows.foldl (fun m r => Nat.max m r.length) 0
    let maxOf (j : Nat) : Nat := strRows.foldl (fun m r => Nat.max m ((r[j]?.getD "").length)) 0
    let deltaOk := (List.range ncol).all fun j =>
      j + 1 == ncol
        || decide (maxOf j - strRows.foldl (fun m r => Nat.min m ((r[j]?.getD "").length)) 1000000
             ≤ spec.maxDelta)
    let widths := (List.range ncol).map fun j => if deltaOk then maxOf j else 0
    emitTable maxPend indent spec.sep widths strRows st
  | .alignOr spec rows fallback, indent, flat, st =>
    -- in FLAT context the grid is out of the question (the flatten contract:
    -- flatWidth (alignOr) speaks about the fallback) — render the fallback flat
    if flat then go width maxPend fallback indent true st else
    -- flat fallback when it fits; the grid when the delta guardrail holds AND
    -- every padded row fits; the ordinary fallback otherwise
    let effCol := if st.pend > 0 then indent else st.col
    let flatFits : Bool := match flatWidth fallback with
      | some w => decide (effCol + w ≤ width)
      | none => false
    if flatFits then go width maxPend fallback indent flat st else
    let strRows := goCellsRows width maxPend rows indent
    let ncol := strRows.foldl (fun m r => Nat.max m r.length) 0
    let maxOf (j : Nat) : Nat := strRows.foldl (fun m r => Nat.max m ((r[j]?.getD "").length)) 0
    let minOf (j : Nat) : Nat :=
      strRows.foldl (fun m r => if j < r.length then Nat.min m ((r[j]?.getD "").length) else m) 1000000
    let deltaOk := (List.range ncol).all fun j =>
      j + 1 == ncol || decide (maxOf j - minOf j ≤ spec.maxDelta)
    let widths := (List.range ncol).map maxOf
    let rowsFit := strRows.all fun r =>
      decide (indent + (renderRowStr spec.sep widths r).length ≤ width)
    -- coherence BY CONSTRUCTION: the grid is taken only when its content
    -- provably equals the fallback's — an incoherent emitter degrades to the
    -- fallback instead of corrupting (and render_content holds unconditionally)
    let gridContent := (strRows.map fun r => nonWs (renderRowStr spec.sep widths r)).flatten
    if deltaOk && rowsFit && decide (rows.length ≥ 2)
        && decide (gridContent = content fallback) then
      emitTable maxPend indent spec.sep widths strRows st
    else go width maxPend fallback indent flat st

/-- Fill packing: each item rendered flat; wrap (in non-flat mode) when the
    next item would cross the width. -/
def goFill (width maxPend : Nat) : List Doc → Nat → Bool → Bool → RSt → RSt
  | [], _, _, _, st => st
  | i :: is, indent, flat, first, st =>
    let t := (go width maxPend i indent true {}).out
    let st :=
      if first then wr st indent t
      else
        let effCol := if st.pend > 0 then indent else st.col
        if !flat && decide (effCol + 1 + t.length > width) then
          wr { st with pend := Nat.min (st.pend + 1) maxPend } indent t
        else wr st indent (" " ++ t)
    goFill width maxPend is indent flat false st

/-- Render every cell of every row flat, to strings. -/
def goCellsRows (width maxPend : Nat) : List (List Doc) → Nat → List (List String)
  | [], _ => []
  | r :: rs, indent => goCells width maxPend r indent :: goCellsRows width maxPend rs indent

def goCells (width maxPend : Nat) : List Doc → Nat → List String
  | [], _ => []
  | c :: cs, indent => (go width maxPend c indent true {}).out :: goCells width maxPend cs indent

end

/-- STRING-AWARE trailing-whitespace strip: drop spaces/tabs at every line end
    EXCEPT inside string literals (plain/interpolated/raw), where they are token
    content. Trailing whitespace anywhere else — code, line comments, block
    comments — is trivia the canonical form does not carry (the gate's
    `commentContent` check is whitespace-blind, so comment-tail stripping is
    provably meaning-safe). The scanner tracks the lexical mode at each newline:
    line comments end AT the newline (strippable); block comments nest; `'` opens
    a char literal only after a non-identifier char (else it is a prime); raw
    strings `r#…#"…"#…#` close on a quote followed by their hash count. Inside
    `s!"…{e}…"` the quote-toggle treats interpolation code as string — the
    conservative direction (never strips string content; at worst leaves a space
    inside interpolation code, which the gate would catch anyway). -/
def stripTrailingWs (s : String) : String := Id.run do
  let a : Array Char := s.toList.toArray
  let n := a.size
  let isIdChar := fun (c : Char) =>
    c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || c.val > 127
  -- modes: 0 code, 1 line comment, 2 block comment, 3 string, 4 raw string, 5 char
  let mut mode : Nat := 0
  let mut depth : Nat := 0          -- block-comment nesting / raw-string hash count
  let mut docComment := false       -- `/--`/`/-!` are ATOMS (leafToks) — never strip inside
  let mut prev : Char := ' '
  let mut out : Array Char := Array.mkEmpty n
  let strip := fun (o : Array Char) => Id.run do
    let mut o := o
    while !o.isEmpty && (o.back! == ' ' || o.back! == '\t') do o := o.pop
    return o
  let mut i := 0
  while _h : i < n do
    let c := a[i]!
    let c1 := a[i + 1]?
    match mode with
    | 0 =>
      if c == '\n' then
        out := (strip out).push c
      else if c == '-' && c1 == some '-' then
        mode := 1; out := (out.push c).push '-'; i := i + 1
      else if c == '/' && c1 == some '-' then
        mode := 2; depth := 1
        docComment := a[i + 2]? == some '-' || a[i + 2]? == some '!'
        out := (out.push c).push '-'; i := i + 1
      else if c == '"' then
        mode := 3; out := out.push c
      else if c == 'r' && !isIdChar prev && (c1 == some '"' || c1 == some '#') then
        -- raw string candidate: r#*" — count hashes, confirm the quote
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
    | 1 =>  -- line comment: the newline both strips and closes
      if c == '\n' then mode := 0; out := (strip out).push c
      else out := out.push c
    | 2 =>  -- block comment (nested): line ends inside are strippable trivia,
            -- EXCEPT in doc comments, whose whole text is one leaf token
      if c == '\n' then out := (if docComment then out else strip out).push c
      else if c == '/' && c1 == some '-' then
        depth := depth + 1; out := (out.push c).push '-'; i := i + 1
      else if c == '-' && c1 == some '/' then
        depth := depth - 1; out := (out.push c).push '/'; i := i + 1
        if depth == 0 then mode := 0
      else out := out.push c
    | 3 =>  -- string literal: NOTHING is stripped (multi-line interiors are content)
      if c == '\\' then
        out := out.push c
        match c1 with | some e => out := out.push e; i := i + 1 | none => pure ()
      else
        if c == '"' then mode := 0
        out := out.push c
    | 4 =>  -- raw string: closes on `"` + depth hashes; interiors are content
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
        match c1 with | some e => out := out.push e; i := i + 1 | none => pure ()
      else
        if c == '\'' || c == '\n' then mode := 0
        if c == '\n' then out := (strip out).push c else out := out.push c
    prev := (out.back?).getD ' '
    i := i + 1
  return String.ofList (strip out).toList

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
def canonVerbatimWs (s : String) : String := Id.run do
  let a : Array Char := s.toList.toArray
  let n := a.size
  let isIdChar := fun (c : Char) =>
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
        if lineStart || j - i == 1 || commentNext then
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
        match c1 with | some e => out := out.push e; i := i + 1 | none => pure ()
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
        match c1 with | some e => out := out.push e; i := i + 1 | none => pure ()
      else
        if c == '\'' || c == '\n' then mode := 0
        out := out.push c
    prev := (out.back?).getD ' '
    i := i + 1
  return String.ofList out.toList

/-- Render a `Doc` to a string under `style`. -/
def render
    (style : Style)
    (doc : Doc)
    : String :=
  let st := go style.layout.lineWidth (style.blankLines.maxConsecutive + 1) doc 0 false {}
  -- trailing whitespace is trivia everywhere outside string literals — the
  -- string-aware strip is what makes verbatim blocks canonical at line ends
  let out := stripTrailingWs st.out
  if out.endsWith "\n" then out else out ++ "\n"

end Lean4Fmt.Doc
