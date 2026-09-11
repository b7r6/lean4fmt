/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // LEAN4FMT // DOC // SEAM
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The seam kit's pure core: turning a form's leading trivia into the
    separator doc a vertical-sequence loop emits before the form. Built from
    the owned primitives (`splitLines`, `trimEndWs`, `dedent`) so
    `Lean4Fmt/Proofs` can prove T3: `leadingSep? lead = some d` implies
    `content d = nonWs lead` — every comment character in the trivia survives
    the seam exactly, in order; when any segment can't be owned, the answer is
    `none` (the caller goes verbatim), never a drop.

    Pure. Depends on Doc.Core + Content + Render.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.doc.core
import lean_4_fmt.doc.content
import lean_4_fmt.doc.render

namespace Lean4Fmt.Doc

/-- A whitespace-only trivia line (spaces/tabs — a blank line or pure indent). -/
def ws_line (line : List Char) : Bool := line.all (fun char => char == ' ' || char == '\t')

/-- The separator for a run of `blanks` blank lines (none → plain newline). -/
def seam_sep (blanks : Nat) : Doc := if blanks > 0 then .blank blanks else .hardline

/-- Emit the interior full lines of a leading trivia: blank lines accumulate
    into `.blank` requests; each comment line rides `.textRaw`, dedented by
    `base` (spaces only — `dedent`'s guard) and trailing-trimmed. -/
def seam_lines (base : Nat) : Nat → List (List Char) → Doc
  | blanks, [] => seam_sep blanks
  | blanks, leading :: lsValue =>
    if ws_line leading then
      seam_lines base (blanks + 1) lsValue
    else
      seam_sep blanks ++ .textRaw (String.ofList (trim_end_ws (dedent base leading)))
          ++ seam_lines base 0 lsValue

/-- The dedent column of a seam run: the minimum space-indent over its comment
    lines (relative offsets between comments survive the re-anchoring). -/
def seam_base (full : List (List Char)) : Nat :=
  (full.filter (fun line => !ws_line line)).foldl
    (fun minimum line => Nat.min minimum (line.takeWhile (· == ' ')).length)
    1000000

/-- Structural placement of a form's leading trivia, as the separator doc that
    goes BEFORE the form in a vertical sequence (a do-statement, an inductive
    constructor): each full line is either a blank line (a `.blank` request,
    §8-clamped) or comment content (dedented by the run's minimum indent so
    relative offsets survive, re-anchored at the sequence indent). Two partial
    lines are dropped AS WHITESPACE ONLY: the HEAD segment (remainder of the
    previous token's line — its newline IS the separator) and the TAIL segment
    (the form's own indentation — the renderer re-indents); if EITHER carries
    content (e.g. a block comment on the form's line), there is no seam that
    owns it and the answer is `none` — the caller goes verbatim. Pure
    single-newline trivia degenerates to the plain `.hardline` separator. -/
def leading_sep? (lead : String) : Option Doc :=
  if !ws_line ((split_lines lead.toList).headD []) then
    none
  else if !ws_line ((split_lines lead.toList).getLastD []) then
    none
  else
    some
      (
        seam_lines
          (seam_base (((split_lines lead.toList).drop 1).dropLast))
          0
          (((split_lines lead.toList).drop 1).dropLast)
      )

end Lean4Fmt.Doc
