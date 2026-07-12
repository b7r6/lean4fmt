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

import Lean4Fmt.Doc.Core
import Lean4Fmt.Doc.Content
import Lean4Fmt.Doc.Render

namespace Lean4Fmt.Doc

/-- A whitespace-only trivia line (spaces/tabs — a blank line or pure indent). -/
def wsLine (l : List Char) : Bool := l.all (fun c => c == ' ' || c == '\t')

/-- The separator for a run of `blanks` blank lines (none → plain newline). -/
def seamSep (blanks : Nat) : Doc := if blanks > 0 then .blank blanks else .hardline

/-- Emit the interior full lines of a leading trivia: blank lines accumulate
    into `.blank` requests; each comment line rides `.textRaw`, dedented by
    `base` (spaces only — `dedent`'s guard) and trailing-trimmed. -/
def seamLines (base : Nat) : Nat → List (List Char) → Doc
  | blanks, [] => seamSep blanks
  | blanks, l :: ls =>
    if wsLine l then seamLines base (blanks + 1) ls
    else
      seamSep blanks ++ .textRaw (String.ofList (trimEndWs (dedent base l)))
        ++ seamLines base 0 ls

/-- The dedent column of a seam run: the minimum space-indent over its comment
    lines (relative offsets between comments survive the re-anchoring). -/
def seamBase (full : List (List Char)) : Nat :=
  (full.filter (fun l => !wsLine l)).foldl
    (fun m l => Nat.min m (l.takeWhile (· == ' ')).length) 1000000

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
def leadingSep? (lead : String) : Option Doc :=
  if !wsLine ((splitLines lead.toList).headD []) then none
  else if !wsLine ((splitLines lead.toList).getLastD []) then none
  else
    some (seamLines (seamBase (((splitLines lead.toList).drop 1).dropLast)) 0
      (((splitLines lead.toList).drop 1).dropLast))

end Lean4Fmt.Doc
