/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // EMIT // TOKENS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Token-level respacing (zero-passthrough §6): render a single-line construct
    from its LEAF TOKENS with canonical inter-token gaps, instead of
    reproducing source bytes. v1 rule: a whitespace gap collapses to ONE space;
    a zero gap stays glued (token adjacency is parse-adjacent content pending
    the v2 pair-class table). Comments in an interior gap bail (`none`) — the
    caller reproduces byte-exact.

    Origin-agnosticism: any parse-preserving ADDITION of intra-line whitespace
    converges to the same bytes. Pure. Depends on Emit.Monad.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Emit.Monad

namespace Lean4Fmt.Emit

/-- The leaf tokens of a subtree, in order (atoms + idents with source bytes). -/
partial def leafTokens (stx : Lean.Syntax) (acc : Array Lean.Syntax := #[]) :
    Array Lean.Syntax :=
  match stx with
  | .atom .. => acc.push stx
  | .ident .. => acc.push stx
  | .node _ _ args => args.foldl (fun a c => leafTokens c a) acc
  | .missing => acc

/-- Any `choice` node in the subtree (ambiguous parse: children are ALL the
    alternatives — flattening would duplicate tokens). -/
partial def hasChoice (stx : Lean.Syntax) : Bool :=
  match stx with
  | .node _ k args => k == Lean.choiceKind || args.any hasChoice
  | _ => false

/-- Canonical single-line respacing of a construct: leaf tokens joined with
    canonical gaps (ws-gap → one space, zero gap → glued). `none` when a token
    is multi-line, a gap carries non-whitespace (an inline block comment), or
    there are no tokens. -/
def tokenJoin? (stx : Lean.Syntax) : Option String := Id.run do
  if hasChoice stx then return none
  let ls := leafTokens stx
  if ls.isEmpty then return none
  let mut out := ""
  let mut prev : Option Lean.Syntax := none
  for l in ls do
    let t := bareSrc l
    if t.isEmpty then continue
    if t.any (· == '\n') then return none
    match prev with
    | none => out := t
    | some p =>
      -- the inter-token gap = prev token's trailing ++ this token's leading.
      -- A zero gap is only trusted with POSITIVE evidence (both trivia
      -- lookups present): a token with synthetic info would otherwise be
      -- GLUED to its neighbor and relex differently (caught as MANGLED).
      let tr? := Lean4Fmt.Syntax.trailing? p
      let ld? := Lean4Fmt.Syntax.leading? l
      if tr?.isNone || ld?.isNone then return none
      let gap := tr?.getD "" ++ ld?.getD ""
      if !gap.toList.all (·.isWhitespace) then return none   -- inline comment
      if gap.any (· == '\n') then return none               -- not single-line
      out := out ++ (if gap.isEmpty then "" else " ") ++ t
    prev := some l
  if out.isEmpty then return none
  return some out

end Lean4Fmt.Emit
