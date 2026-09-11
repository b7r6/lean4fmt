/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // SYNTAX // KINDS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    SyntaxNodeKind constants and classifiers. One place for kind names so the
    walker reads declaratively and a kind rename touches one file.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import lean_4_fmt.syntax.trivia

namespace Lean4Fmt.Syntax

open Lean

-- Parser-generated kinds (notation-derived — no Lean-core constant to
-- ``-reference), named ONCE here; every comparison goes through these. The
-- `#guard`s pin each Name literal to the exact string the comparisons
-- previously spelled out — drift between the two spellings is a compile
-- error, not a silent formatter regression.

/-- `[a, b]` list literals. -/
def list_lit_kind : SyntaxNodeKind := `«term[_]»

/-- `#[a, b]` array literals. -/
def array_lit_kind : SyntaxNodeKind := `«term#[_,]»

/-- `{leftValue}` brace literals. -/
def brace_lit_kind : SyntaxNodeKind := `«term{_}»

/-- `if c then a else b`. -/
def ite_kind : SyntaxNodeKind := `termIfThenElse

/-- `if h : c then a else b`. -/
def dite_kind : SyntaxNodeKind := `termDepIfThenElse

#guard list_lit_kind.toString == "«term[_]»"
#guard array_lit_kind.toString == "«term#[_,]»"
#guard brace_lit_kind.toString == "«term{_}»"
#guard ite_kind.toString == "termIfThenElse"
#guard dite_kind.toString == "termDepIfThenElse"

/-- A binary-operator notation kind (`«term_+_»`, `«term_<_»`, …), including
    NAMESPACED scoped notations (`CategoryTheory.«term_≫_»`,
    `Quiver.«term_⟶_»` — the mathlib operator families): the pattern applies
    to the LAST name component. -/
def is_bin_op (kind : SyntaxNodeKind) : Bool :=
  let spelling := ((kind.components.getLast?.map toString).getD "")
  spelling.startsWith "«term_" && (spelling.toList.filter (· == '_')).length >= 2

#guard is_bin_op `«term_=_»
#guard is_bin_op `CategoryTheory.«term_≫_»
#guard !is_bin_op `Lean.Parser.Term.app

/-- A BINDER-COMMA notation (`∑ x ∈ s, body` / `⨆ i, f i` / `∀ᵐ x ∂μ, p` —
    the big-operator and measure families, namespaced or not): a prefix-op
    head, binders, then the BODY after the final comma. Recognized by name
    shape on the last component; binops are excluded (they start `«term_`).
    These all share the binder-predicate layout: head tokens canonical, body
    width-aware at the continuation. -/
def is_binder_comma (kind : SyntaxNodeKind) : Bool :=
  let spelling := ((kind.components.getLast?.map toString).getD "")
  (spelling.startsWith "«term" && spelling.endsWith "_,_»" && !is_bin_op kind)
    -- the NAMED big-operator binders (`∑ x ∈ s, body` parses as
    -- `BigOperators.bigsum`, not a «term…» spelling): same
    -- head-comma-body shape, same extended source-exact-head route
    || kind == `BigOperators.bigsum || kind == `BigOperators.bigprod

#guard is_binder_comma `BigOperators.bigsum
#guard is_binder_comma `Finset.«term∑_∈_,_»
#guard is_binder_comma `«term⨆_,_»
#guard is_binder_comma `MeasureTheory.«term∀ᵐ_∂_,_»
#guard !is_binder_comma `«term_=_»
#guard !is_binder_comma `Lean.Parser.Term.app

/-- Term kinds with an ACTIVE MULTI-LINE layout: their `walk` produces a
    width-aware breaking group, so a decl value of one of these may lay out
    actively even when it spans lines. `Decl.isActiveMultiline` consumes
    exactly this set; the walk router consumes `walkTermKinds`, a superset BY
    CONSTRUCTION — so "the emitter handles it but the walker never routes it"
    (the structInst/forall registration-drift class) cannot recur for a
    multi-line kind. -/
def active_multiline_term_kinds : Array SyntaxNodeKind :=
  #[
    ite_kind,
    dite_kind,
    list_lit_kind,
    array_lit_kind,
    ``Lean.Parser.Term.app,
    ``Lean.Parser.Term.anonymousCtor,
    ``Lean.Parser.Term.fun,
    ``Lean.Parser.Term.tuple,
    ``Lean.Parser.Term.structInst,
    ``Lean.Parser.Term.forall,
    ``Lean.Parser.Term.arrow,
    ``Lean.Parser.Term.paren,
    ``Lean.Parser.Term.let,
    ``Lean.Parser.Term.have,
    ``Lean.Parser.Term.letI,
    ``Lean.Parser.Term.haveI,
    ``Lean.Parser.Term.letrec,
    ``Lean.Parser.Term.match,
    ``Lean.Parser.Term.show,
    `Mathlib.Meta.setBuilder
  ]

/-- Every term kind the walker routes to `Term.emit` (binOps ride the
    `isBinOp` predicate beside this array).

    PORTING CHECKLIST — a new term construct registers in: (1) this array —
    or `activeMultilineTermKinds` above when its layout can break (Decl's
    value gate derives from that); (2) its `Term.emit` branch; (3)
    `Tokens.gapRule` when it introduces token-adjacency rules; (4) the
    ws-canon/perturber mirrors when its layout is column-sensitive
    (`Emit/WsSensitivity`). -/
def walk_term_kinds : Array SyntaxNodeKind :=
  active_multiline_term_kinds
      ++ #[
        `Lean.«term∀__,_»,
        `Lean.«term∃__,_»,
        `«term∃_,_»,
        `«term∀_,_»,
        `«term¬_»,
        ``Lean.Parser.Term.proj,
        ``Lean.Parser.Term.dotIdent,
        ``Lean.Parser.Term.hole,
        ``Lean.Parser.Term.letDecl,
        ``Lean.Parser.Term.letIdDecl,
        ``Lean.Parser.Term.letPatDecl,
        ``Lean.Parser.Term.letIdDeclNoBinders
      ]

/-- Kinds that are inline-prone containers: flattening one that carries a line
    comment would let the comment swallow following tokens (§0.4). -/
def is_inline_prone_container (kind : SyntaxNodeKind) : Bool :=
  kind == ``Lean.Parser.Term.app || kind == ``Lean.Parser.Term.anonymousCtor
      || kind == ``Lean.Parser.Term.match
      || kind == ``Lean.Parser.Term.structInst
      || kind == list_lit_kind
      || kind == brace_lit_kind

/-- Kinds whose emitters OWN their interior comment seams (the seam model
    pushed into expression space): the entry comment-guard and the value
    span-guard exempt these — their arms place inter-item comments
    structurally, and anything they can't hold falls back internally. -/
def owns_seams (kind : SyntaxNodeKind) : Bool :=
  kind == ``Lean.Parser.Term.let || kind == ``Lean.Parser.Term.have
    || kind == ``Lean.Parser.Term.letI || kind == ``Lean.Parser.Term.haveI
    || kind == ``Lean.Parser.Term.match
      || kind == ``Lean.Parser.Term.anonymousCtor
      || kind == ``Lean.Parser.Term.structInst
      || kind == ``Lean.Parser.Term.app
      -- the do statement loop owns inter-statement trivia (comments/blanks
      -- place structurally; a statement-interior comment keeps just that
      -- statement verbatim — bytes never drop). Counting do-body comments
      -- at an eqns/match ARM forced whole-decl (and enclosing-mutual)
      -- verbatim for every commented proof-shaped arm.
      || kind == ``Lean.Parser.Term.do
      -- by is do's proof twin: the tactic sequence loop owns inter-tactic
      -- trivia the same way (per-tactic verbatim fallback; bytes never
      -- drop). Its absence made any TERM wrapping a comment-bearing by
      -- (`fun x ↦ by …` values, the mathlib structInst-field idiom) bail
      -- wholesale at the entry guard before its handler ran.
      || kind == ``Lean.Parser.Term.byTactic
      || kind == `Lean.Parser.Term.byTactic'
      || kind == list_lit_kind
      || kind == array_lit_kind

/-- A `fun` whose body is a `by`/`do` block: the wrapper adds only flat head
    text before the block, so a binding seam's block-glue argument passes
    through it (`x := fun a ↦ by` + body below). The match-alternative form
    (`fun | pat => …`) is not this shape. -/
def is_fun_block_value (value : Lean.Syntax) : Bool :=
  value.getKind == ``Lean.Parser.Term.fun
      && (
        match value.getArgs[1]? with
        | some bodyForm =>
          bodyForm.getKind == ``Lean.Parser.Term.basicFun
              && (
                match bodyForm.getArgs.back? with
                | some rightValue =>
                  rightValue.getKind == ``Lean.Parser.Term.do
                      || rightValue.getKind == ``Lean.Parser.Term.byTactic
                | none => false
              )
        | none => false
      )

/-- Layout-sensitive / proof kinds that must never be inlined (§0.7 #10). -/
def is_never_inline (kind : SyntaxNodeKind) : Bool :=
  kind == ``Lean.Parser.Term.byTactic || kind == ``Lean.Parser.Term.have
      || kind == ``Lean.Parser.Term.show
      || kind == ``Lean.Parser.Term.suffices
      || kind == ``Lean.Parser.Term.letrec

/-- Comment hazard EXCLUDING seam-owning descendants: a `match`/`let`/… child
    places its own interior comments structurally (and falls back to a
    multi-line verbatim itself when it cannot — which the parent's
    hasMultilineVerbatim check catches). Counting their subtrees at the parent
    made e.g. `fun c => match … -- comment` verbatim for no reason. The tail
    token's trailing stays exempt (the enclosing seam owns it). -/
partial
def has_unowned_line_comment (stx : Lean.Syntax) : Bool :=
  countUnownedComments stx > count_line_comments ((last_token_trailing? stx).getD "")
  where
    countUnownedComments (source : Lean.Syntax) : Nat :=
      match source with
      | .node _ kind args =>
        if owns_seams kind then 0
    else args.foldl (fun count child => count + countUnownedComments child) 0
      | _ =>
        count_line_comments ((leading? source).getD "")
          + count_line_comments ((trailing? source).getD "")

/-- The ARM-SITE variant of the unowned-comment count: (a) the node's OWN
    leading is exempt — the arm loop places it via `leadingSep?`; (b) a
    seam-owning DESCENDANT's HEAD-leading still counts — its emitter owns
    comments BETWEEN its items, not the one before its own first token
    (a comment between `=>` and a `match` body was silently DROPPED when
    the plain ownsSeams cutoff swallowed it — found by the comment diff
    check, the gate is blind to it). -/
partial
def has_unowned_interior_comment (stx : Lean.Syntax) : Bool :=
  goI stx
      > count_line_comments ((leading? stx).getD "")
          + count_line_comments ((last_token_trailing? stx).getD "")
  where
    goI (source : Lean.Syntax) : Nat :=
      match source with
      | .node _ kind args =>
        if owns_seams kind then count_line_comments ((leading? source).getD "")
    else args.foldl (fun count child => count + goI child) 0
      | _ =>
        count_line_comments ((leading? source).getD "")
          + count_line_comments ((trailing? source).getD "")

/-- A quotation TERM kind (`Term.quot`, `dynamicQuot`, category quots) —
    `.quot`/`…Quot` names the quotation PARSERS; name-literal kinds
    (`quotedName`) are single tokens — nothing inside them to respace — and
    must NOT poison their whole decl. -/
def is_quot_term_kind (keyValue : Lean.SyntaxNodeKind) : Bool :=
  let spelling := keyValue.toString
  spelling.endsWith ".quot" || spelling.endsWith "Quot"

/-- A metaprogram COMMAND whose whole body is quotation content byte-exact
    (arm padding included — the perturber's META guard mirrors this). -/
def is_quotation_command (keyValue : Lean.SyntaxNodeKind) : Bool :=
  keyValue == `Lean.Parser.Command.macro_rules || keyValue == `Lean.Parser.Command.elab_rules
      || keyValue == `Lean.Parser.Command.syntax
      || keyValue == `Lean.Parser.Command.syntaxAbbrev
      || keyValue == `Lean.Parser.Command.notation
      || keyValue == `Lean.Parser.Command.macro
      || keyValue == `Lean.Parser.Command.elab
      || keyValue == `Lean.Parser.Command.mixfix

partial
def has_quotation_kind (stx : Lean.Syntax) : Bool :=
  match stx with
  | .node _ kind args =>
    is_quot_term_kind kind || is_quotation_command kind || args.any has_quotation_kind
  | _ => false

/-- Whether the subtree carries one of the byte-exact metaprogram COMMANDS. -/
partial
def has_quotation_command (stx : Lean.Syntax) : Bool :=
  match stx with
  | .node _ kind args => is_quotation_command kind || args.any has_quotation_command
  | _                 => false

/-- Bytes of CONTENT-BY-POLICY nodes (module docstrings, the header, quotation
    commands): permanently verbatim by design, NOT portable residue — the
    honest porting tail is `verbatim - policy`, and `--stats` reports the
    coverage ceiling from it. Bare-source sizes match what `verbatim` emits
    (modulo ws-canon: an accounting approximation, not an invariant). -/
partial
def policy_content_bytes (stx : Lean.Syntax) : Nat :=
  match stx with
  | .node _ kind args =>
    if kind == ``Lean.Parser.Module.header || kind == `Lean.Parser.Command.moduleDoc
        || is_quotation_command kind then
      ((stx.getSubstring? false false).map (·.toString.utf8ByteSize)).getD 0
    else
      args.foldl (fun count child => count + policy_content_bytes child) 0
  | _ => 0

/-- The byte ranges of embedded quotation TERMS (outermost only — interiors
    belong to their quotation). `none` when a quotation has no position info
    (the caller must then treat the WHOLE text as content). -/
partial
def quot_term_ranges? (stx : Lean.Syntax) : Option (Array (Nat × Nat)) :=
  collectQuotTermRanges stx (some #[])
  where
    collectQuotTermRanges
        (source : Lean.Syntax)
        (ranges : Option (Array (Nat × Nat)))
        : Option (Array (Nat × Nat)) :=
      match ranges with
      | none => none
      | some leftValue =>
        match source with
        | .node _ kind args =>
          if is_quot_term_kind kind then
            match source.getPos?, source.getTailPos? with
            | some pathValue, some rightPos => some (leftValue.push (pathValue.byteIdx, rightPos.byteIdx))
            | _, _ => none
          else args.foldl (fun found child => collectQuotTermRanges child found) (some leftValue)
        | _ => some leftValue

/-- A DSL template opener (`[ident|`) anywhere in the text — the lexical
    counterpart of the perturber's TPL_OPEN guard, for source that parses
    under custom template kinds we cannot enumerate. -/
def has_template_opener (source : String) : Bool :=
  Id.run do
    let chars : Array Char := source.toList.toArray
    let size := chars.size
    for idx in [0:size] do
      if chars[idx]! == '[' && idx + 1 < size
          && (chars[idx+1]!.isAlpha || chars[idx+1]! == '_') then
        let mut cursor := idx + 1
        while _hj : cursor < size
            && (chars[cursor]!.isAlphanum || chars[cursor]! == '_' || chars[cursor]! == '.') do
          cursor := cursor + 1
        if _hj : cursor < size then
          if chars[cursor]! == '|' then
            return true
    return false

end Lean4Fmt.Syntax
