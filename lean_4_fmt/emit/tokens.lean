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

import lean_4_fmt.emit.monad
import lean_4_fmt.syntax.kinds

namespace Lean4Fmt.Emit

/-- The leaf tokens of a subtree, in order (atoms + idents with source bytes). -/
partial
def leaf_tokens (stx : Lean.Syntax) (found : Array Lean.Syntax := #[]) : Array Lean.Syntax :=
  match stx with
  | .atom ..       => found.push stx
  | .ident ..      => found.push stx
  | .node _ _ args => args.foldl (fun result child => leaf_tokens child result) found
  | .missing       => found

/-- Any `choice` node in the subtree (ambiguous parse: children are ALL the
    alternatives — flattening would duplicate tokens). -/
partial
def has_choice (stx : Lean.Syntax) : Bool :=
  match stx with
  | .node _ kind args => kind == Lean.choiceKind || args.any has_choice
  | _                 => false

/-- v2 pair rule: `some true` = one space, `some false` = glued, `none` =
    source-derived (v1). Whitespace-SENSITIVE tokens (`[` for getElem, postfix
    `!`/`?`, field indices) stay source-derived: Lean's parse depends on their
    adjacency, so forcing either spelling could change the tree (the gate
    would catch it as a per-file fallback — correctness holds, coverage pays).
    clang-format is the shape of the eventual full table. -/
private
def gap_rule (prev next : String) : Option Bool :=
  let identLike (textValue : String) :=
    textValue.toList.all fun char =>
      char.isAlphanum || char == '_' || char == '\'' || char == '.' || char.toNat > 127
  if prev == "(" || prev == "⟨" || prev == "‹" || prev == "⦃" || prev == "¬" then
    some false
  else if next == ")" || next == "⟩" || next == "›" || next == "⦄" || next == "," || next == ";" then
    some false
  else if prev == "," || prev == ";" then
    some true
  else if prev == ":=" || next == ":=" || prev == "=>" || next == "=>" || prev == "↦" || next == "↦" then
    some true
  else if next == "(" && (identLike prev || prev == ")") then some true else none

private
structure token_join_state where
  output     : String := ""
  previous   : Option Lean.Syntax := none
  skippedGap : String := ""

private
def append_token_after_previous?
    (flatten : Bool)
    (state : token_join_state)
    (leaf : Lean.Syntax)
    (token : String)
    (previous : Lean.Syntax)
    : Option token_join_state :=
  Id.run do
    let trailing? := Lean4Fmt.Syntax.trailing? previous
    let leading? := Lean4Fmt.Syntax.leading? leaf
    if trailing?.isNone || leading?.isNone then
      return none
    let gap := trailing?.getD "" ++ state.skippedGap ++ leading?.getD ""
    if !gap.toList.all (·.isWhitespace) || (!flatten && gap.any (· == '\n')) then
      return none
    let separator :=
      match gap_rule (bare_src previous) token with
      | some true  => " "
      | some false => ""
      | none       => if gap.isEmpty then "" else " "
    return some
      {
        output := state.output ++ separator ++ token
        previous := some leaf
        skippedGap := ""
      }

private
def advance_token_join?
    (flatten : Bool)
    (state : token_join_state)
    (leaf : Lean.Syntax)
    : Option token_join_state :=
  let token := bare_src leaf
  if token.isEmpty then
    some
      { state with
        skippedGap := state.skippedGap ++ (Lean4Fmt.Syntax.leading? leaf).getD ""
            ++ (Lean4Fmt.Syntax.trailing? leaf).getD "" }
  else if token.any (· == '\n') then
    none
  else
    match state.previous with
    | none          => some { output := token, previous := some leaf, skippedGap := "" }
    | some previous => append_token_after_previous? flatten state leaf token previous

/-- Canonical single-line respacing of a construct: leaf tokens joined with
    canonical gaps (pair-rule table, else ws-gap → one space / zero gap →
    glued). `none` when a token is multi-line, a gap carries non-whitespace
    (an inline block comment), or there are no tokens. -/
private
def token_join_impl? (stx : Lean.Syntax) (flatten : Bool) : Option String :=
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
      let leaves := leaf_tokens stx
      if leaves.isEmpty then
        return none
      let mut state : token_join_state := {}
      -- trivia carried by SKIPPED empty leaves (e.g. the synthetic `[anonymous]`
      -- idents of a cdot expansion, whose trailing holds the real inter-token
      -- space) — folded into the next real gap, else `(· + ·)` would relex-glue
      for leaf in leaves do
        let some nextState := advance_token_join? flatten state leaf | return none
        state := nextState
      if state.output.isEmpty then
        return none
      return some state.output

def token_join? (stx : Lean.Syntax) : Option String := token_join_impl? stx false

/-- A MULTI-LINE newline-SEMANTIC descendant: by/do (the newline separates
    tactics/statements), let (the newline is the `in`), structInst (comma-less
    fields separate by line). Flattening across one joins constructs the
    parser separates by line — a DIFFERENT parse from identical tokens (tree
    class, gate-caught on mathlib Divisors: a calc step's `:= by` + two
    tactics joined into an application). Single-line ones are safe: their
    interior is already one line and the join preserves it. -/
partial
def has_newline_semantic (source : Lean.Syntax) : Bool :=
  (
    (
      source.getKind == ``Lean.Parser.Term.do || source.getKind == ``Lean.Parser.Term.byTactic
          || source.getKind == `Lean.Parser.Term.byTactic'
          || source.getKind == ``Lean.Parser.Term.let
          || source.getKind == ``Lean.Parser.Term.letrec
          || source.getKind == ``Lean.Parser.Term.structInst
    )
        && (bare_src source).any (· == '\n')
  )
      || source.getArgs.any has_newline_semantic

/-- Canonical FLATTENED token text: like `tokenJoin?` but newline gaps become
    single spaces — the canonical one-line spelling of a multi-line construct.
    `none` when a gap carries a comment (flattening would eat it or comment
    out the tail), or when the subtree contains a multi-line
    newline-semantic construct (no one-line spelling EXISTS — see
    `hasNewlineSemantic`; the flatten-side head-ws law, enforced at the one
    owner instead of per call site). -/
def token_join_flat? (stx : Lean.Syntax) : Option String :=
  if has_newline_semantic stx then none else token_join_impl? stx true

/-- Canonical single-line token text: tokenJoin? with a bareSrc fallback —
    the standard spelling for EMITTED head pieces. The fallback (choice nodes,
    synthetic-info gaps) still ws-canonicalizes LEXICALLY (canonVerbatimWs):
    token bytes survive, interior space runs do not — so even the fallback is
    not an origin carrier. -/
def canon_tok (stx : Lean.Syntax) : String :=
  match token_join? stx with
  | some trailing => trailing
  | none =>
    -- piecewise ws-canon: quotation terms/commands byte-exact (pin),
    -- templates via canonVerbatimWs' own template mode, the rest collapses.
    -- NOTE the trim: bareSrc has no leading trivia, so start trim is a no-op
    -- and end trim only drops trailing ws — the piecewise offsets stay valid.
    canon_ws_piecewise stx ((bare_src stx).trimAscii.toString)

end Lean4Fmt.Emit
