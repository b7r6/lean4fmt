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
partial
def leaf_tokens (stx : Lean.Syntax) (acc : Array Lean.Syntax := #[]) : Array Lean.Syntax :=
  match stx with
  | .atom ..       => acc.push stx
  | .ident ..      => acc.push stx
  | .node _ _ args => args.foldl (fun a c => leaf_tokens c a) acc
  | .missing       => acc

/-- Any `choice` node in the subtree (ambiguous parse: children are ALL the
    alternatives — flattening would duplicate tokens). -/
partial
def has_choice (stx : Lean.Syntax) : Bool :=
  match stx with
  | .node _ k args => k == Lean.choiceKind || args.any has_choice
  | _              => false

/-- v2 pair rule: `some true` = one space, `some false` = glued, `none` =
    source-derived (v1). Whitespace-SENSITIVE tokens (`[` for getElem, postfix
    `!`/`?`, field indices) stay source-derived: Lean's parse depends on their
    adjacency, so forcing either spelling could change the tree (the gate
    would catch it as a per-file fallback — correctness holds, coverage pays).
    clang-format is the shape of the eventual full table. -/
private
def gap_rule (prev next : String) : Option Bool :=
  let identLike (t : String) :=
    t.toList.all fun c => c.isAlphanum || c == '_' || c == '\'' || c == '.' || c.toNat > 127
  if prev == "(" || prev == "⟨" || prev == "‹" || prev == "⦃" || prev == "¬" then
    some false
  else if next == ")" || next == "⟩" || next == "›" || next == "⦄" || next == "," || next == ";" then
    some false
  else if prev == "," || prev == ";" then
    some true
  else if prev == ":=" || next == ":=" || prev == "=>" || next == "=>" || prev == "↦" || next == "↦" then
    some true
  else if next == "(" && (identLike prev || prev == ")") then some true else none

/-- Canonical single-line respacing of a construct: leaf tokens joined with
    canonical gaps (pair-rule table, else ws-gap → one space / zero gap →
    glued). `none` when a token is multi-line, a gap carries non-whitespace
    (an inline block comment), or there are no tokens. -/
def token_join? (stx : Lean.Syntax) : Option String :=
  Id.run
    do
      if has_choice stx then
        return none
      -- quotation/template content (pin): inter-token spacing may be semantic
      -- to the quoted DSL — never respace
      if Lean4Fmt.Syntax.has_quotation_kind stx then
        return none
      if Lean4Fmt.Syntax.has_template_opener (bare_src stx) then
        return none
      let ls := leaf_tokens stx
      if ls.isEmpty then
        return none
      let mut out := ""
      let mut prev : Option Lean.Syntax := none
      -- trivia carried by SKIPPED empty leaves (e.g. the synthetic `[anonymous]`
      -- idents of a cdot expansion, whose trailing holds the real inter-token
      -- space) — folded into the next real gap, else `(· + ·)` would relex-glue
      let mut skipGap := ""
      for l in ls do
        let t := bare_src l
        if t.isEmpty then
          skipGap :=
            skipGap ++ (Lean4Fmt.Syntax.leading? l).getD "" ++ (Lean4Fmt.Syntax.trailing? l).getD ""
          continue
        if t.any (· == '\n') then
          return none
        match prev with
        | none => out := t
        | some p =>
          -- the inter-token gap = prev token's trailing ++ this token's leading.
          -- A zero gap is only trusted with POSITIVE evidence (both trivia
          -- lookups present): a token with synthetic info would otherwise be
          -- GLUED to its neighbor and relex differently (caught as MANGLED).
          let tr? := Lean4Fmt.Syntax.trailing? p
          let ld? := Lean4Fmt.Syntax.leading? l
          if tr?.isNone || ld?.isNone then
            return none
          let gap := tr?.getD "" ++ skipGap ++ ld?.getD ""
          if !gap.toList.all (·.isWhitespace) then
            return none -- inline comment
          if gap.any (· == '\n') then
            return none -- not single-line
          let sep :=
            match gap_rule (bare_src p) t with
            | some true  => " "
            | some false => ""
            | none       => if gap.isEmpty then "" else " "
          out := out ++ sep ++ t
        prev := some l
        skipGap := ""
      if out.isEmpty then
        return none
      return some out

/-- A MULTI-LINE newline-SEMANTIC descendant: by/do (the newline separates
    tactics/statements), let (the newline is the `in`), structInst (comma-less
    fields separate by line). Flattening across one joins constructs the
    parser separates by line — a DIFFERENT parse from identical tokens (tree
    class, gate-caught on mathlib Divisors: a calc step's `:= by` + two
    tactics joined into an application). Single-line ones are safe: their
    interior is already one line and the join preserves it. -/
partial
def has_newline_semantic (s : Lean.Syntax) : Bool :=
  ((s.getKind == ``Lean.Parser.Term.do || s.getKind == ``Lean.Parser.Term.byTactic
      || s.getKind == `Lean.Parser.Term.byTactic'
      || s.getKind == ``Lean.Parser.Term.let
      || s.getKind == ``Lean.Parser.Term.letrec
      || s.getKind == ``Lean.Parser.Term.structInst)
      && (bare_src s).any (· == '\n'))
      || s.getArgs.any has_newline_semantic

/-- Canonical FLATTENED token text: like `tokenJoin?` but newline gaps become
    single spaces — the canonical one-line spelling of a multi-line construct.
    `none` when a gap carries a comment (flattening would eat it or comment
    out the tail), or when the subtree contains a multi-line
    newline-semantic construct (no one-line spelling EXISTS — see
    `hasNewlineSemantic`; the flatten-side head-ws law, enforced at the one
    owner instead of per call site). -/
def token_join_flat? (stx : Lean.Syntax) : Option String :=
  Id.run
    do
      if has_choice stx then
        return none
      if has_newline_semantic stx then
        return none
      if Lean4Fmt.Syntax.has_quotation_kind stx then
        return none
      if Lean4Fmt.Syntax.has_template_opener (bare_src stx) then
        return none
      let ls := leaf_tokens stx
      if ls.isEmpty then
        return none
      let mut out := ""
      let mut prev : Option Lean.Syntax := none
      let mut skipGap := "" -- trivia from skipped empty leaves (see tokenJoin?)
      for l in ls do
        let t := bare_src l
        if t.isEmpty then
          skipGap :=
            skipGap ++ (Lean4Fmt.Syntax.leading? l).getD "" ++ (Lean4Fmt.Syntax.trailing? l).getD ""
          continue
        if t.any (· == '\n') then
          return none -- multi-line TOKEN: content
        match prev with
        | none => out := t
        | some p =>
          let tr? := Lean4Fmt.Syntax.trailing? p
          let ld? := Lean4Fmt.Syntax.leading? l
          if tr?.isNone || ld?.isNone then
            return none
          let gap := tr?.getD "" ++ skipGap ++ ld?.getD ""
          if !gap.toList.all (·.isWhitespace) then
            return none
          let sep :=
            match gap_rule (bare_src p) t with
            | some true  => " "
            | some false => ""
            | none       => if gap.isEmpty then "" else " "
          out := out ++ sep ++ t
        prev := some l
        skipGap := ""
      if out.isEmpty then
        return none
      return some out

/-- Canonical single-line token text: tokenJoin? with a bareSrc fallback —
    the standard spelling for EMITTED head pieces. The fallback (choice nodes,
    synthetic-info gaps) still ws-canonicalizes LEXICALLY (canonVerbatimWs):
    token bytes survive, interior space runs do not — so even the fallback is
    not an origin carrier. -/
def canon_tok (stx : Lean.Syntax) : String :=
  match token_join? stx with
  | some t => t
  | none =>
    -- piecewise ws-canon: quotation terms/commands byte-exact (pin),
    -- templates via canonVerbatimWs' own template mode, the rest collapses.
    -- NOTE the trim: bareSrc has no leading trivia, so start trim is a no-op
    -- and end trim only drops trailing ws — the piecewise offsets stay valid.
    canon_ws_piecewise stx ((bare_src stx).trimAscii.toString)

end Lean4Fmt.Emit
