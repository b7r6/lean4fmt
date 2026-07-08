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

private def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')
private def newlines (n : Nat) : String := String.ofList (List.replicate n '\n')

private structure RSt where
  out  : String := ""
  col  : Nat := 0
  pend : Nat := 0        -- pending newlines (for blank collapsing)
  deriving Inhabited

/-- Emit single-line visible text at break-indent `indent`, flushing pending
    newlines (with indentation) first. -/
private def wr (st : RSt) (indent : Nat) (s : String) : RSt :=
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
private def wrBlock (st : RSt) (indent : Nat) (base : Nat) (raw : String) : RSt := Id.run do
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
      st := wr { st with pend := st.pend + 1 } indent ded
  return st

/-- Render a `Doc` to a string under `style`. -/
partial def render (style : Style) (doc : Doc) : String :=
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
      -- Fit-check at the EFFECTIVE column: if newlines are pending (unflushed),
      -- the next content will land at `indent`, not at the stale `st.col` left
      -- over from before the break. Using `st.col` here would make an inner group
      -- break spuriously after its enclosing group broke.
      let effCol := if st.pend > 0 then indent else st.col
      let canFlat := match flatWidth d with | some w => effCol + w ≤ width | none => false
      go d indent canFlat st
    | .flatten d => go d indent true st
    | .nest n d => go d (Int.toNat ((indent : Int) + n)) flat st
    | .align d => go d st.col flat st
    | .alignTable spec rows =>
      let cellStr (c : Doc) : String := (go c indent true {}).out
      let strRows := rows.map (·.map cellStr)
      let ncol := strRows.foldl (fun m r => Nat.max m r.size) 0
      let widths := (Array.range ncol).map fun j =>
        Nat.min spec.maxDelta (strRows.foldl (fun m r => Nat.max m ((r[j]?.getD "").length)) 0)
      let renderRow (r : Array String) : String :=
        (Array.range r.size).foldl (fun acc j =>
          let cell := r[j]?.getD ""
          let last := j + 1 == r.size
          let pad := if last then "" else spaces ((widths[j]?.getD 0) - cell.length)
          acc ++ cell ++ pad ++ (if last then "" else spec.sep)) ""
      (strRows.foldl (fun (p : RSt × Bool) r =>
        let st := if p.2 then p.1 else { p.1 with pend := Nat.min (p.1.pend + 1) maxPend }
        (wr st indent (renderRow r), false)) (st, true)).1
  let st := go doc 0 false {}
  if st.out.endsWith "\n" then st.out else st.out ++ "\n"

end Lean4Fmt.Doc
