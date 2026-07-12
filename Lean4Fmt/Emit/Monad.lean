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

/-- Opaque reproduction (§4.1): the safe default for any construct not yet
    actively formatted. Reproduces the BARE source as a re-anchorable `verbatim`
    doc whose `baseIndent` is the first token's source column (from leading
    trivia) — the renderer dedents continuations by that, so the block re-anchors
    correctly at whatever column it is placed (the composition seam, §0.3). -/
def verbatim
    (stx : Lean.Syntax)
    : EmitM Doc := do
  let lead := (Lean4Fmt.Syntax.leading? stx).getD ""
  let base := if lead.any (· == '\n')
    then (((lead.splitOn "\n").getLastD "").toList.takeWhile (· == ' ')).length
    else 0
  let s := bareSrc stx
  if s.isEmpty then
    match stx.reprint with | some r => pure (.verbatim r base) | none => pure .nil
  else pure (.verbatim s base)

/-- Byte-exact passthrough of a whole form INCLUDING its leading trivia. -/
def passthrough
    (stx : Lean.Syntax)
    : EmitM Doc :=

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
    : Option Doc := Id.run do
  let ls := lead.splitOn "\n"
  let isWs (l : String) : Bool := l.all (fun c => c == ' ' || c == '\t')
  if !isWs (ls.headD "") then return none
  let full := (ls.drop 1).dropLast
  let content := full.filter (fun l => !isWs l)
  let indentOf (l : String) : Nat := (l.toList.takeWhile (· == ' ')).length
  let base := content.foldl (fun m l => Nat.min m (indentOf l)) 1000000
  let mut d : Doc := .nil
  let mut blanks := 0
  for l in full do
    if isWs l then blanks := blanks + 1
    else
      let ded := if l.length ≥ base then String.ofList (l.toList.drop base) else l
      d := d ++ (if blanks > 0 then .blank blanks else .hardline)
        ++ .textRaw ded.trimAsciiEnd.toString
      blanks := 0
  return some (d ++ (if blanks > 0 then .blank blanks else .hardline))

/-- The leading trivia (comments + blank lines) before a form, as literal text. -/
def leadingRaw (stx : Lean.Syntax) : Doc := .textRaw (Lean4Fmt.Syntax.leading? stx |>.getD "")

/-- The trailing trivia after a form, as literal text. `leadingRaw next` +
    `trailingRaw prev` partition the inter-form gap exactly. -/
def trailingRaw (stx : Lean.Syntax) : Doc := .textRaw (Lean4Fmt.Syntax.trailing? stx |>.getD "")

end Lean4Fmt.Emit
