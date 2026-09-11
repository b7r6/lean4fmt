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

/-- Trailing trivia string of a syntax's tail token, if original. Together with
    the next form's leading this partitions the inter-form gap exactly. -/
def trailing? (stx : Lean.Syntax) : Option String :=
  match stx.getTailInfo with
  | .original _ _ trailing _ => some (Substring.Raw.toString trailing)
  | _ => none

/-- The trailing trivia of the LAST token in the subtree (robust against
    trailing empty null slots, which defeat `getTailInfo`). -/
partial
def last_token_trailing? (stx : Lean.Syntax) : Option String :=
  match trailing? stx with
  | some trailing => some trailing
  | none          => stx.getArgs.reverse.findSome? last_token_trailing?

/-- Does a trivia string contain a line comment `-- …`? (block comments `/- -/`
    are safe; only line comments eat the rest of the line — §0.4). -/
def has_line_comment (source : String) : Bool := (source.splitOn "--").length > 1

/-- Does a trivia string contain a block comment? Unlike line comments these
    do not consume the line, but an active emitter must still own their seam or
    it can silently discard the token. -/
def has_block_comment (source : String) : Bool := (source.splitOn "/-").length > 1

/-- True if any token in the subtree carries a line comment in its trivia. Such
    a subtree must never be inlined/flattened (§0.4). -/
partial
def subtree_has_line_comment (stx : Lean.Syntax) : Bool :=
  let inTrivia (info : SourceInfo) : Bool :=
    match info with
    | .original leading _ trailing _ =>
      has_line_comment (Substring.Raw.toString leading)
          || has_line_comment (Substring.Raw.toString trailing)
    | _ => false
  match stx with
  | .atom info _      => inTrivia info
  | .ident info _ _ _ => inTrivia info
  | .node info _ args => inTrivia info || args.any subtree_has_line_comment
  | .missing          => false

/-- True if any token in the subtree carries a block comment in its trivia. -/
partial
def subtree_has_block_comment (stx : Lean.Syntax) : Bool :=
  let inTrivia (info : SourceInfo) : Bool :=
    match info with
    | .original leading _ trailing _ =>
      has_block_comment (Substring.Raw.toString leading)
          || has_block_comment (Substring.Raw.toString trailing)
    | _ => false
  match stx with
  | .atom info _      => inTrivia info
  | .ident info _ _ _ => inTrivia info
  | .node info _ args => inTrivia info || args.any subtree_has_block_comment
  | .missing          => false

/-- Number of line comments in a trivia string (the counting form of
    `hasLineComment`). -/
def count_line_comments (source : String) : Nat := (source.splitOn "--").length - 1

/-- Total line comments in ALL trivia of a subtree (leading and trailing of every
    token) — the counting form of `subtreeHasLineComment`. Callers exempt a
    specific zone (e.g. the tail token's trailing, which the enclosing seam
    places byte-exact) by subtracting its count; a boolean can't express that,
    since a comment in an exempt zone would mask one in the interior. -/
partial
def count_subtree_line_comments (stx : Lean.Syntax) : Nat :=
  let inInfo (info : SourceInfo) : Nat :=
    match info with
    | .original leading _ trailing _ =>
      count_line_comments (Substring.Raw.toString leading)
          + count_line_comments (Substring.Raw.toString trailing)
    | _ => 0
  match stx with
  | .atom info _ => inInfo info
  | .ident info _ _ _ => inInfo info
  | .node info _ args =>
    inInfo info + args.foldl (fun count child => count + count_subtree_line_comments child) 0
  | .missing => 0

/-- Line comment in the trivia this form OWNS: anywhere in the subtree except the
    tail token's trailing — that zone belongs to the enclosing seam (whoever
    places the form also places its trailing: `Module` for commands, the do-block
    statement loop for statements). The counting arithmetic is what makes the
    exemption sound — a boolean check would let a trailing comment mask an
    interior one. -/
def has_owned_line_comment (stx : Lean.Syntax) : Bool :=
  count_subtree_line_comments stx > count_line_comments ((trailing? stx).getD "")

/-- Line comment strictly INTERIOR to a form: between its first and last token.
    Both the head token's leading and the tail token's trailing are exempt — for
    a do-statement the loop places both zones itself. -/
def interior_has_line_comment (stx : Lean.Syntax) : Bool :=

  -- the trailing exemption must reach the LAST TOKEN's trailing: getTailInfo
  -- is defeated by trailing empty null slots (a match arm ends in one), which
  -- would count an arm's own trailing comment as interior
  count_subtree_line_comments stx
      > count_line_comments ((leading? stx).getD "")
          + count_line_comments ((last_token_trailing? stx).getD "")

/-- Exact original source text for a node (leading trivia in, trailing out):
    reprint, falling back to the source slice when reprint is unavailable
    (§0.3 — reprint can be `none` for some nodes after `updateLeading`). -/
def verbatim_src? (stx : Lean.Syntax) : Option String :=
  match stx.reprint with
  | some textValue => some textValue
  | none           => (stx.getSubstring? true false).map (·.toString)

end Lean4Fmt.Syntax
