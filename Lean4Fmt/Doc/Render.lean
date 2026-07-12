/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // LEAN4FMT // DOC // RENDER
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Width-aware layout: `Style → Doc → String` (DESIGN_V2 §4). A pragmatic
    Wadler/Leijen renderer: `group` picks flat-or-break by fit; `nest`/`align`
    set the break indent COMPOSITIONALLY (this dissolves the v1
    context-guessed-indentation bug class, §0.2); `verbatim` re-anchors an opaque
    block to the current indent (§0.3, §4.1); `blank` is clamped by policy (§8).

    Pure. Depends on Doc.Core + Style.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Doc.Core
import Lean4Fmt.Style

namespace Lean4Fmt.Doc

open Lean4Fmt.Style

/-- Flat width of a doc, or `none` if it cannot be flattened. -/
partial def flatWidth : Doc → Option Nat
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

/-- Whether a doc contains a multi-line opaque block (`verbatim`/`textRaw` with a
    newline). Such blocks re-anchor by column, which is only idempotent at their
    natural top-level position — so a subtree containing one must NOT be laid out
    actively (it stays on the safe whole-span path). Hardlines are fine: they are
    clean structural breaks, not re-anchored, so a hardline-bearing doc (let / do /
    match) is still safe to render actively. -/
partial def hasMultilineVerbatim : Doc → Bool
  | .verbatim s _ => s.any (· == '\n')
  | .textRaw s => s.any (· == '\n')
  | .cat a b => hasMultilineVerbatim a || hasMultilineVerbatim b
  | .group d | .nest _ d | .align d | .flatten d => hasMultilineVerbatim d
  | .alignTable _ rows => rows.any (·.any hasMultilineVerbatim)
  | .alignOr _ _ fb => hasMultilineVerbatim fb
  | _ => false

/-- Coverage accounting (DESIGN_V2 §15): byte attribution over a produced doc.
    `.text` is actively formatted output; `.verbatim` is opaque reproduction —
    constructs not yet ported, plus content that is correctly byte-exact forever
    (string literals, DSL quotations); `.textRaw` is comments/trivia (inherently
    byte-exact, not a coverage failure). The ratio active/(active+verbatim) is
    the tool's construct-coverage number, tracked over time via `--stats`. -/
partial def stats : Doc → (Nat × Nat × Nat)
  | .text s => (s.utf8ByteSize, 0, 0)
  | .verbatim s _ => (0, s.utf8ByteSize, 0)
  | .textRaw s => (0, 0, s.utf8ByteSize)
  | .cat a b =>
    let (a1, v1, t1) := stats a
    let (a2, v2, t2) := stats b
    (a1 + a2, v1 + v2, t1 + t2)
  | .group d | .nest _ d | .align d | .flatten d => stats d
  | .alignTable _ rows =>
    rows.foldl
      (fun acc r => r.foldl
        (fun (acc : Nat × Nat × Nat) c =>
          let (a, v, t) := stats c
          (acc.1 + a, acc.2.1 + v, acc.2.2 + t)) acc)
      (0, 0, 0)
  | .alignOr _ _ fb => stats fb
  | _ => (0, 0, 0)

/-- Width a doc contributes to the CURRENT line, up to its first possible break
    point (line/softline/hardline/blank, or a newline inside a verbatim/textRaw),
    plus whether such a break was reached. Used to couple a signature's
    break-after-colon decision to what the value adds to the same line (e.g.
    `:= by` before a tactic block) without the circularity of asking the value to
    lay itself out first. A `flatten` never breaks, so it contributes its full
    flat width. -/
partial def firstLineWidth : Doc → Nat × Bool
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

private def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')private def newlines (n : Nat) : String := String.ofList (List.replicate n '\n')

private structure RSt where
  out  : String := ""
  col  : Nat := 0
  pend : Nat := 0        -- pending newlines (for blank collapsing)
  deriving Inhabited

/-- Emit single-line visible text at break-indent `indent`, flushing pending
    newlines (with indentation) first. -/
private def wr
            (st : RSt)
            (indent : Nat)
            (s : String)
            : RSt :=
  let st := if st.pend > 0
    then { out := st.out ++ newlines st.pend ++ spaces indent, col := indent, pend := 0 }
    else st
  { st with out := st.out ++ s, col := st.col + s.length }

/-- Emit a possibly-multi-line block (verbatim/comment), re-anchored to `indent`:
    dedent every continuation by the block's OWN base column `base` (the source
    column of its first token, computed at walk time), then re-indent to `indent`
    (§0.3). Using the explicit base — rather than a `min`-over-lines — is what lets
    the block re-anchor correctly regardless of the internal indentation of nested
    lines (e.g. a `do`-block deeper than its head). The first line is emitted as-is
    (it starts right after `indent` is already established). -/
private def wrBlock
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
      -- first line already sits at `indent`; emit its bare content verbatim
      st := wr st indent l; first := false
    else
      let ded := if l.length ≥ base then String.ofList (l.toList.drop base) else String.ofList (l.toList.dropWhile (· == ' '))
      -- an interior EMPTY line stays a pending newline — `wr` would write the
      -- indent with nothing after it (trailing whitespace, and non-idempotent
      -- once a verbatim block is re-anchored at a nonzero indent, e.g. inside
      -- `mutual`). Byte-empty ONLY: a whitespace-bearing line may be the
      -- interior of a multi-line string literal, where the spaces are token
      -- content and must survive byte-exact.
      if ded.isEmpty then st := { st with pend := st.pend + 1 }
      else st := wr { st with pend := st.pend + 1 } indent ded
  return st

/-- Render a `Doc` to a string under `style`. -/
partial def render
            (style : Style)
            (doc : Doc)
            : String :=
  let width := style.layout.lineWidth
  let maxPend := style.blankLines.maxConsecutive + 1
  let rec go (d : Doc) (indent : Nat) (flat : Bool) (st : RSt) : RSt :=
    match d with
    | .nil => st
    | .text s => wr st indent s
    | .textRaw s =>
      -- literal, byte-exact emission (used for passthrough of whole forms and
      -- inter-form trivia): flush pending, append verbatim, track last-line col.
      let st := if st.pend > 0
        then { out := st.out ++ newlines st.pend ++ spaces indent, col := indent, pend := 0 } else st
      { st with out := st.out ++ s, col := ((s.splitOn "\n").getLast!).length }
    | .verbatim s b => wrBlock st indent b s
    | .cat a b => go b indent flat (go a indent flat st)
    | .line => if flat then wr st indent " " else { st with pend := Nat.min (st.pend + 1) maxPend }
    | .softline => if flat then st else { st with pend := Nat.min (st.pend + 1) maxPend }
    | .hardline => { st with pend := Nat.min (st.pend + 1) maxPend }
    | .blank req => { st with pend := Nat.min (st.pend + 1 + req) maxPend }
    | .group d =>
      -- A group inside a flat context (e.g. under `.flatten`, or an enclosing
      -- group that chose flat) MUST stay flat — otherwise `flatten` fails to force
      -- its subtree flat and layout becomes column-dependent / non-idempotent.
      -- Otherwise decide by fit at the EFFECTIVE column: with newlines pending
      -- (unflushed) the next content lands at `indent`, not the stale `st.col`.
      let effCol := if st.pend > 0 then indent else st.col
      let canFlat := flat || (match flatWidth d with | some w => effCol + w ≤ width | none => false)
      go d indent canFlat st
    | .flatten d => go d indent true st
    | .nest n d => go d (Int.toNat ((indent : Int) + n)) flat st
    | .align d => go d st.col flat st
    | .alignTable spec rows =>
      let cellStr (c : Doc) : String := (go c indent true {}).out
      let strRows := rows.map (·.map cellStr)
      let ncol := strRows.foldl (fun m r => Nat.max m r.size) 0
      -- §7 guardrail: `maxDelta` caps the column DELTA (max−min), not the
      -- width — a run whose padding would exceed it opts out of alignment
      -- entirely (rows emit unpadded) rather than producing the ragged-
      -- whitespace anti-pattern.
      let maxOf (j : Nat) : Nat := strRows.foldl (fun m r => Nat.max m ((r[j]?.getD "").length)) 0
      let minOf (j : Nat) : Nat :=
        strRows.foldl (fun m r => Nat.min m ((r[j]?.getD "").length)) 1000000
      let deltaOk := (Array.range ncol).all fun j =>
        j + 1 == ncol || maxOf j - minOf j ≤ spec.maxDelta
      let widths := (Array.range ncol).map fun j => if deltaOk then maxOf j else 0
      let renderRow (r : Array String) : String :=
        (Array.range r.size).foldl (fun acc j =>
          let cell := r[j]?.getD ""
          let last := j + 1 == r.size
          let pad := if last then "" else spaces ((widths[j]?.getD 0) - cell.length)
          acc ++ cell ++ pad ++ (if last then "" else spec.sep)) ""
      (strRows.foldl (fun (p : RSt × Bool) r =>
        let st := if p.2 then p.1 else { p.1 with pend := Nat.min (p.1.pend + 1) maxPend }
        (wr st indent (renderRow r), false)) (st, true)).1
    | .alignOr spec rows fallback =>
      -- padded table when the delta guardrail holds AND every padded row fits
      -- the width at this indent; the ordinary fallback layout otherwise
      let cellStr (c : Doc) : String := (go c indent true {}).out
      let strRows := rows.map (·.map cellStr)
      let ncol := strRows.foldl (fun m r => Nat.max m r.size) 0
      let maxOf (j : Nat) : Nat := strRows.foldl (fun m r => Nat.max m ((r[j]?.getD "").length)) 0
      let minOf (j : Nat) : Nat :=
        strRows.foldl (fun m r =>
          if j < r.size then Nat.min m ((r[j]?.getD "").length) else m) 1000000
      let deltaOk := (Array.range ncol).all fun j =>
        j + 1 == ncol || maxOf j - minOf j ≤ spec.maxDelta
      let widths := (Array.range ncol).map maxOf
      let renderRow (r : Array String) : String :=
        (Array.range r.size).foldl (fun acc j =>
          let cell := r[j]?.getD ""
          let last := j + 1 == r.size
          let pad := if last then "" else spaces ((widths[j]?.getD 0) - cell.length)
          acc ++ cell ++ pad ++ (if last then "" else spec.sep)) ""
      let rowsFit := strRows.all fun r => indent + (renderRow r).length ≤ width
      if deltaOk && rowsFit && rows.size ≥ 2 then
        (strRows.foldl (fun (p : RSt × Bool) r =>
          let st := if p.2 then p.1 else { p.1 with pend := Nat.min (p.1.pend + 1) maxPend }
          (wr st indent (renderRow r), false)) (st, true)).1
      else go fallback indent flat st
  let st := go doc 0 false {}
  -- NOTE: no blanket trailing-whitespace strip — active layout never emits trailing
  -- whitespace, and a final-pass strip would damage the interior lines of multi-line
  -- string literals (their trailing spaces are part of the token). A comment/string-
  -- aware hygiene pass is deferred (same class as blank-line normalization, §8).
  if st.out.endsWith "\n" then st.out else st.out ++ "\n"

end Lean4Fmt.Doc
