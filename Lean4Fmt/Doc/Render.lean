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
  | .textRaw s => if s.any (· == '\n') then none else some s.length
  | .verbatim s _ => if s.any (· == '\n') then none else some s.trimAscii.toString.length
  | .blank _ => none
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

/-- Emit a possibly-multi-line block (verbatim/comment), re-anchored to `indent`:
    dedent every continuation by the block's OWN base column `base`, re-indent to
    `indent` (§0.3). Interior EMPTY lines stay pending newlines (hygiene; byte-
    empty only — whitespace-bearing lines may be string-literal interiors). -/
def wrBlock
    (st : RSt)
    (indent : Nat)
    (base : Nat)
    (raw : String)
    : RSt := Id.run do
  let nonblank (l : String) : Bool := l.any (· != ' ')
  let mut ls := raw.trimAsciiEnd.toString.splitOn "\n"
  ls := ls.dropWhile (fun l => !nonblank l)
  ls := (ls.reverse.dropWhile (fun l => !nonblank l)).reverse
  if ls.isEmpty then return st
  let mut st := st
  let mut first := true
  for l in ls do
    if first then
      st := wr st indent l; first := false
    else
      -- dedent drops ONLY spaces: if the first `base` chars aren't all spaces
      -- (a continuation less indented than its head), fall back to stripping
      -- just the leading spaces — dropping `base` chars unconditionally would
      -- eat CONTENT on such lines (latent until the content-preservation
      -- theorem in Proofs demanded it be impossible)
      let ded := if l.length ≥ base && (l.toList.take base).all (· == ' ')
        then String.ofList (l.toList.drop base)
        else String.ofList (l.toList.dropWhile (· == ' '))
      if ded.isEmpty then st := { st with pend := st.pend + 1 }
      else st := wr { st with pend := st.pend + 1 } indent ded
  return st

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
    { st with out := st.out ++ s, col := ((s.splitOn "\n").getLast!).length }
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
    let canFlat := flat || (match flatWidth d with | some w => decide (effCol + w ≤ width) | none => false)
    go width maxPend d indent canFlat st
  | .flatten d, indent, _, st => go width maxPend d indent true st
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
    if deltaOk && rowsFit && decide (rows.length ≥ 2) then
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

/-- Render a `Doc` to a string under `style`. -/
def render
    (style : Style)
    (doc : Doc)
    : String :=
  let st := go style.layout.lineWidth (style.blankLines.maxConsecutive + 1) doc 0 false {}
  -- NOTE: no blanket trailing-whitespace strip — active layout never emits
  -- trailing whitespace, and a strip would damage multi-line string literal
  -- interiors (their trailing spaces are token content).
  if st.out.endsWith "\n" then st.out else st.out ++ "\n"

end Lean4Fmt.Doc
