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
import Lean4Fmt.Syntax.Kinds

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

/-- v2 pair rule: `some true` = one space, `some false` = glued, `none` =
    source-derived (v1). Whitespace-SENSITIVE tokens (`[` for getElem, postfix
    `!`/`?`, field indices) stay source-derived: Lean's parse depends on their
    adjacency, so forcing either spelling could change the tree (the gate
    would catch it as a per-file fallback — correctness holds, coverage pays).
    clang-format is the shape of the eventual full table. -/
private def gapRule (prev next : String) : Option Bool :=
  let identLike (t : String) := t.toList.all fun c =>
    c.isAlphanum || c == '_' || c == '\'' || c == '.' || c.toNat > 127
  if prev == "(" || prev == "⟨" || prev == "‹" || prev == "⦃" then some false
  else if next == ")" || next == "⟩" || next == "›" || next == "⦄"
      || next == "," || next == ";" then some false
  else if prev == "," || prev == ";" then some true
  else if prev == ":=" || next == ":=" || prev == "=>" || next == "=>" then some true
  else if next == "(" && (identLike prev || prev == ")" ) then some true
  else none

/-- Canonical single-line respacing of a construct: leaf tokens joined with
    canonical gaps (pair-rule table, else ws-gap → one space / zero gap →
    glued). `none` when a token is multi-line, a gap carries non-whitespace
    (an inline block comment), or there are no tokens. -/
def tokenJoin? (stx : Lean.Syntax) : Option String := Id.run do
  if hasChoice stx then return none
  -- quotation/template content (pin): inter-token spacing may be semantic
  -- to the quoted DSL — never respace
  if Lean4Fmt.Syntax.hasQuotationKind stx then return none
  if Lean4Fmt.Syntax.hasTemplateOpener (bareSrc stx) then return none
  let ls := leafTokens stx
  if ls.isEmpty then return none
  let mut out := ""
  let mut prev : Option Lean.Syntax := none
  -- trivia carried by SKIPPED empty leaves (e.g. the synthetic `[anonymous]`
  -- idents of a cdot expansion, whose trailing holds the real inter-token
  -- space) — folded into the next real gap, else `(· + ·)` would relex-glue
  let mut skipGap := ""
  for l in ls do
    let t := bareSrc l
    if t.isEmpty then
      skipGap := skipGap
        ++ (Lean4Fmt.Syntax.leading? l).getD "" ++ (Lean4Fmt.Syntax.trailing? l).getD ""
      continue
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
      let gap := tr?.getD "" ++ skipGap ++ ld?.getD ""
      if !gap.toList.all (·.isWhitespace) then return none   -- inline comment
      if gap.any (· == '\n') then return none               -- not single-line
      let sep := match gapRule (bareSrc p) t with
        | some true => " "
        | some false => ""
        | none => if gap.isEmpty then "" else " "
      out := out ++ sep ++ t
    prev := some l
    skipGap := ""
  if out.isEmpty then return none
  return some out

/-- Canonical FLATTENED token text: like `tokenJoin?` but newline gaps become
    single spaces — the canonical one-line spelling of a multi-line construct.
    `none` when a gap carries a comment (flattening would eat it or comment
    out the tail). -/
def tokenJoinFlat? (stx : Lean.Syntax) : Option String := Id.run do
  if hasChoice stx then return none
  if Lean4Fmt.Syntax.hasQuotationKind stx then return none
  if Lean4Fmt.Syntax.hasTemplateOpener (bareSrc stx) then return none
  let ls := leafTokens stx
  if ls.isEmpty then return none
  let mut out := ""
  let mut prev : Option Lean.Syntax := none
  let mut skipGap := ""   -- trivia from skipped empty leaves (see tokenJoin?)
  for l in ls do
    let t := bareSrc l
    if t.isEmpty then
      skipGap := skipGap
        ++ (Lean4Fmt.Syntax.leading? l).getD "" ++ (Lean4Fmt.Syntax.trailing? l).getD ""
      continue
    if t.any (· == '\n') then return none    -- multi-line TOKEN: content
    match prev with
    | none => out := t
    | some p =>
      let tr? := Lean4Fmt.Syntax.trailing? p
      let ld? := Lean4Fmt.Syntax.leading? l
      if tr?.isNone || ld?.isNone then return none
      let gap := tr?.getD "" ++ skipGap ++ ld?.getD ""
      if !gap.toList.all (·.isWhitespace) then return none
      let sep := match gapRule (bareSrc p) t with
        | some true => " "
        | some false => ""
        | none => if gap.isEmpty then "" else " "
      out := out ++ sep ++ t
    prev := some l
    skipGap := ""
  if out.isEmpty then return none
  return some out

/-- Canonical single-line token text: tokenJoin? with a bareSrc fallback —
    the standard spelling for EMITTED head pieces. The fallback (choice nodes,
    synthetic-info gaps) still ws-canonicalizes LEXICALLY (canonVerbatimWs):
    token bytes survive, interior space runs do not — so even the fallback is
    not an origin carrier. -/
def canonTok (stx : Lean.Syntax) : String :=
  match tokenJoin? stx with
  | some t => t
  | none =>
    let raw := (bareSrc stx).trimAscii.toString
    -- quotation KINDS ride byte-exact; templates are guarded inside
    -- canonVerbatimWs (template mode), so the lexical collapse is safe
    if Lean4Fmt.Syntax.hasQuotationKind stx then raw
    else Lean4Fmt.Doc.canonVerbatimWs raw

end Lean4Fmt.Emit
