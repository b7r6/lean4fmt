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
def leading?
    (stx : Lean.Syntax)
    : Option String :=

  match stx.getHeadInfo with
  | .original leading .. => some (Substring.Raw.toString leading)
  | _ => none

/-- Trailing trivia string of a syntax's tail token, if original. Together with
    the next form's leading this partitions the inter-form gap exactly. -/
def trailing?
    (stx : Lean.Syntax)
    : Option String :=

  match stx.getTailInfo with
  | .original _ _ trailing _ => some (Substring.Raw.toString trailing)
  | _ => none

/-- The trailing trivia of the LAST token in the subtree (robust against
    trailing empty null slots, which defeat `getTailInfo`). -/
partial def lastTokenTrailing?
            (stx : Lean.Syntax)
            : Option String :=

  match trailing? stx with
  | some t => some t
  | none   => stx.getArgs.reverse.findSome? lastTokenTrailing?

/-- Does a trivia string contain a line comment `-- …`? (block comments `/- -/`
    are safe; only line comments eat the rest of the line — §0.4). -/
def hasLineComment (s : String) : Bool := (s.splitOn "--").length > 1

/-- True if any token in the subtree carries a line comment in its trivia. Such
    a subtree must never be inlined/flattened (§0.4). -/
partial def subtreeHasLineComment
            (stx : Lean.Syntax)
            : Bool :=

  let inTrivia (info : SourceInfo) : Bool :=
    match info with
    | .original l _ t _ =>
      hasLineComment (Substring.Raw.toString l) || hasLineComment (Substring.Raw.toString t)
    | _ => false
  match stx with
  | .atom info _      => inTrivia info
  | .ident info _ _ _ => inTrivia info
  | .node info _ args => inTrivia info || args.any subtreeHasLineComment
  | .missing          => false

/-- Number of line comments in a trivia string (the counting form of
    `hasLineComment`). -/
def countLineComments (s : String) : Nat := (s.splitOn "--").length - 1

/-- Total line comments in ALL trivia of a subtree (leading and trailing of every
    token) — the counting form of `subtreeHasLineComment`. Callers exempt a
    specific zone (e.g. the tail token's trailing, which the enclosing seam
    places byte-exact) by subtracting its count; a boolean can't express that,
    since a comment in an exempt zone would mask one in the interior. -/
partial def countSubtreeLineComments
            (stx : Lean.Syntax)
            : Nat :=

  let inInfo (info : SourceInfo) : Nat :=
    match info with
    | .original l _ t _ =>
      countLineComments (Substring.Raw.toString l) + countLineComments (Substring.Raw.toString t)
    | _ => 0
  match stx with
  | .atom info _      => inInfo info
  | .ident info _ _ _ => inInfo info
  | .node info _ args => inInfo info + args.foldl (fun n c => n + countSubtreeLineComments c) 0
  | .missing          => 0

/-- Line comment in the trivia this form OWNS: anywhere in the subtree except the
    tail token's trailing — that zone belongs to the enclosing seam (whoever
    places the form also places its trailing: `Module` for commands, the do-block
    statement loop for statements). The counting arithmetic is what makes the
    exemption sound — a boolean check would let a trailing comment mask an
    interior one. -/
def hasOwnedLineComment
    (stx : Lean.Syntax)
    : Bool :=

  countSubtreeLineComments stx > countLineComments ((trailing? stx).getD "")

/-- Line comment strictly INTERIOR to a form: between its first and last token.
    Both the head token's leading and the tail token's trailing are exempt — for
    a do-statement the loop places both zones itself. -/
def interiorHasLineComment
    (stx : Lean.Syntax)
    : Bool :=

  -- the trailing exemption must reach the LAST TOKEN's trailing: getTailInfo
  -- is defeated by trailing empty null slots (a match arm ends in one), which
  -- would count an arm's own trailing comment as interior
  countSubtreeLineComments stx
      > countLineComments ((leading? stx).getD "")
          + countLineComments ((lastTokenTrailing? stx).getD "")

/-- Exact original source text for a node (leading trivia in, trailing out):
    reprint, falling back to the source slice when reprint is unavailable
    (§0.3 — reprint can be `none` for some nodes after `updateLeading`). -/
def verbatimSrc?
    (stx : Lean.Syntax)
    : Option String :=

  match stx.reprint with
  | some s => some s
  | none   => (stx.getSubstring? true false).map (·.toString)

end Lean4Fmt.Syntax
