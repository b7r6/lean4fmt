/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // LEAN4FMT // SYNTAX // TRIVIA
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Leading/trailing trivia extraction, comment detection, verbatim source
    slices. QUARANTINED HERE so a toolchain bump (Substring.Raw, trimAscii,
    getSubstring?, dependent String.Pos — §0.6) touches one module, not the walker.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean

namespace Lean4Fmt.Syntax

open Lean

/-- Leading trivia string of a syntax's head token, if original. -/
def leading? (stx : Lean.Syntax) : Option String :=
  match stx.getHeadInfo with
  | .original leading .. => some (Substring.Raw.toString leading)
  | _ => none

/-- Does a trivia string contain a line comment `-- …`? (block comments `/- -/`
    are safe; only line comments eat the rest of the line — §0.4). -/
def hasLineComment (s : String) : Bool := (s.splitOn "--").length > 1

/-- True if any token in the subtree carries a line comment in its trivia. Such
    a subtree must never be inlined/flattened (§0.4). -/
partial def subtreeHasLineComment (stx : Lean.Syntax) : Bool :=
  let inTrivia (info : SourceInfo) : Bool :=
    match info with
    | .original l _ t _ =>
      hasLineComment (Substring.Raw.toString l) || hasLineComment (Substring.Raw.toString t)
    | _ => false
  match stx with
  | .atom info _ => inTrivia info
  | .ident info _ _ _ => inTrivia info
  | .node info _ args => inTrivia info || args.any subtreeHasLineComment
  | .missing => false

/-- Exact original source text for a node (leading trivia in, trailing out):
    reprint, falling back to the source slice when reprint is unavailable
    (§0.3 — reprint can be `none` for some nodes after `updateLeading`). -/
def verbatimSrc? (stx : Lean.Syntax) : Option String :=
  match stx.reprint with
  | some s => some s
  | none => (stx.getSubstring? true false).map (·.toString)

end Lean4Fmt.Syntax
