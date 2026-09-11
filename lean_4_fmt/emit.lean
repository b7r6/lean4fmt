/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                             // LEAN4FMT // EMIT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The walker: `Syntax → Doc` (doc/design.md §3/§6). `walk` is the single recursive
    function; it dispatches on syntax kind to the per-category open-recursion
    emitters (`Emit/Module`, `Emit/Term`, …), passing itself so they can recurse.

    The safe default routes an unsupported kind to verbatim reproduction (§5.2) — a
    safe, meaning-preserving no-op. Active formatting is filled in category by
    category; the safety gate (Frontend) guarantees correctness throughout.

    Pure. Depends on Doc, Style, Syntax, Rules.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.emit.monad
import lean_4_fmt.emit.tokens
import lean_4_fmt.emit.module
import lean_4_fmt.emit.decl
import lean_4_fmt.emit.command
import lean_4_fmt.emit.term
import lean_4_fmt.emit.do_notation
import lean_4_fmt.emit.tactic
import lean_4_fmt.syntax.kinds

namespace Lean4Fmt.Emit

open Lean Lean4Fmt.Doc Lean4Fmt.Style

private
def command_kinds : Array Name :=
  #[
    ``Lean.Parser.Command.structure,
    ``Lean.Parser.Command.inductive,
    ``Lean.Parser.Command.mutual,
    ``Lean.Parser.Command.open,
    ``Lean.Parser.Command.namespace,
    ``Lean.Parser.Command.end,
    ``Lean.Parser.Command.section,
    ``Lean.Parser.Command.universe,
    ``Lean.Parser.Command.variable,
    ``Lean.Parser.Command.elab,
    `Batteries.Tactic.Alias.alias,
    ``Lean.Parser.Command.eval,
    ``Lean.Parser.Command.in
  ]

private
def do_kinds : Array Name :=
  #[
    ``Lean.Parser.Term.do,
    ``Lean.Parser.Term.doNested,
    ``Lean.Parser.Term.doFor,
    `Lean.Parser.Term.doWhile,
    `Lean.Parser.Term.doUnless,
    ``Lean.Parser.Term.doLet,
    ``Lean.Parser.Term.doLetRec,
    ``Lean.Parser.Term.doLetElse,
    ``Lean.Parser.Term.doLetArrow,
    ``Lean.Parser.Term.doReassign,
    ``Lean.Parser.Term.doReassignArrow,
    ``Lean.Parser.Term.doExpr,
    ``Lean.Parser.Term.doReturn,
    ``Lean.Parser.Term.doIf,
    ``Lean.Parser.Term.doMatch
  ]

private
def tactic_kinds_primary : Array Name :=
  #[
    ``Lean.Parser.Term.byTactic,
    ``Lean.Parser.Tactic.exact,
    ``Lean.Parser.Tactic.apply,
    ``Lean.Parser.Tactic.refine,
    ``Lean.Parser.Tactic.rwSeq,
    ``Lean.Parser.Tactic.unfold,
    ``Lean.Parser.Tactic.induction,
    ``Lean.Parser.Tactic.cases,
    ``Lean.Parser.Tactic.tacticHave__,
    `Lean.Parser.Tactic.tacticHaveI__,
    `Lean.Parser.Tactic.tacticLetI__,
    ``Lean.Parser.Tactic.replace,
    `Lean.cdot,
    ``Lean.Parser.Tactic.tacticRfl,
    ``Lean.Parser.Tactic.omega,
    ``Lean.Parser.Tactic.decide,
    ``Lean.Parser.Tactic.nativeDecide,
    ``Lean.Parser.Tactic.constructor,
    ``Lean.Parser.Tactic.tacticTrivial,
    ``Lean.Parser.Tactic.contradiction,
    ``Lean.Parser.Tactic.assumption,
    ``Lean.Parser.Tactic.tacticAnd_intros,
    ``Lean.Parser.Tactic.simpAll,
    ``Lean.Parser.Tactic.intro,
    ``Lean.Parser.Tactic.intros,
    ``Lean.Parser.Tactic.simp,
    `Mathlib.Tactic.tacticSimp_rw___,
    `Lean.Parser.Tactic.«tacticNext_=>_»,
    ``Lean.Parser.Tactic.case,
    ``Lean.Parser.Tactic.allGoals,
    `Lean.Parser.Tactic.tacticRepeat_,
    `Lean.Parser.Tactic.Conv.conv,
    `Lean.calcTactic,
    `Lean.calc
  ]

private
def tactic_kinds_secondary : Array Name :=
  #[
    ``Lean.Parser.Tactic.split,
    `Lean.Parser.Tactic.obtain,
    `Lean.Parser.Tactic.rcases,
    ``Lean.Parser.Tactic.show,
    `Lean.Parser.Tactic.subst,
    `Lean.Parser.Tactic.«tacticExists_,,»,
    ``Lean.Parser.Tactic.change,
    `«tacticBy_cases_:_»,
    `Lean.Parser.Tactic.tacticSuffices_,
    `Lean.Parser.Tactic.«tactic_<;>_»,
    ``Lean.Parser.Tactic.simpAll,
    `Lean.Parser.Tactic.dsimp,
    `Lean.Parser.Tactic.simpa,
    `Lean.Parser.Tactic.simpaUsingBang,
    `Lean.Parser.Tactic.tacticRwa__,
    `Lean.Parser.Tactic.first,
    `Lean.Parser.Tactic.match,
    `Lean.Parser.Tactic.tacticLet__,
    `Lean.Parser.Tactic.congr,
    `Lean.Parser.Tactic.renameI,
    `Lean.Parser.Tactic.bvDecide,
    `Lean.Parser.Tactic.left,
    `Lean.Parser.Tactic.right,
    `Lean.Parser.Tactic.revert,
    `Lean.Parser.Tactic.injection,
    `Lean.Parser.Tactic.tacticInfer_instance,
    `Lean.Parser.Tactic.tacticExfalso,
    `Lean.Parser.Tactic.«tacticNomatch_,,»,
    `Lean.Parser.Tactic.paren,
    `Lean.Parser.Tactic.generalize,
    `Lean.Parser.Tactic.classical,
    `Lean.Parser.Term.byTactic'
  ]

private
def is_tactic_kind (kind : Name) : Bool :=
  tactic_kinds_primary.contains kind || tactic_kinds_secondary.contains kind

private
def ident_doc (stx : Lean.Syntax) (identifier : Name) : Doc :=

  -- preserve guillemets on keyword-named identifiers.
  let text := Lean4Fmt.Emit.bare_src stx
  -- suppress synthetic anonymous identifiers introduced by cdot expansion.
  .text
    (if text.isEmpty then (if identifier == .anonymous then "" else identifier.toString) else text)

mutual

/-- The single recursive walker. Dispatches to category emitters; falls back to
    verbatim reproduction for anything not yet actively formatted. Term routing
    is DATA (`Syntax.Kinds.walkTermKinds` — the porting checklist lives on it);
    the do/tactic/command lists below are single-consumer and stay inline. -/
partial def walkCore
            (stx : Lean.Syntax)
            : emit_m Doc := do
  match stx with
  | .missing => pure .nil
  | .atom _ value => pure (.text value)
  | .ident _ _ identifier _ => pure (ident_doc stx identifier)
  | .node _ kind _ => walk_node stx kind

/-- Route a syntax node to its category emitter or canonical fallback. -/
partial def walk_node
    (stx : Lean.Syntax)
    (kind : Name)
    : emit_m Doc := do
  if kind == ``Lean.Parser.Module.module then
    Module.emit walk stx
  else if kind == ``Lean.Parser.Command.declaration || kind == `lemma then
    Decl.emit walk stx
  else if command_kinds.contains kind then
    Command.emit walk stx
  else if (← read).breaking.preserveLineBreaks && kind == ``Lean.Parser.Term.do
      && !(Lean4Fmt.Emit.bare_src stx).any (· == '\n')
      && !(Lean4Fmt.Emit.bare_src stx).isEmpty then
    pure (.text (Lean4Fmt.Emit.bare_src stx))
  else if do_kinds.contains kind then
    DoNotation.emit walk stx
  else if is_tactic_kind kind then
    Tactic.emit walk stx
  else if (← read).breaking.preserveLineBreaks
      && (kind == ``Lean.Parser.Term.match || Lean4Fmt.Syntax.is_bin_op kind
          || kind.toString.startsWith "Lean.Parser.Term"
          || kind.toString.startsWith "term"
          || kind.toString.startsWith "«term") then
    let text := Lean4Fmt.Emit.bare_src stx
    if !text.isEmpty && !text.any (· == '\n') then pure (.text text) else verbatim stx
  else if Lean4Fmt.Syntax.is_bin_op kind
      || Lean4Fmt.Syntax.is_binder_comma kind
      || Lean4Fmt.Syntax.walk_term_kinds.contains kind then
    Term.emit walk stx
  else
    let text := Lean4Fmt.Emit.bare_src stx
    if !text.isEmpty && !text.any (· == '\n') then
      match Lean4Fmt.Emit.token_join? stx with
      | some joined => pure (.text joined)
      | none => pure (.text (Lean4Fmt.Emit.canon_ws_piecewise stx text))
    else
      verbatim stx

/-- Commit a token join and discard the stale diagnostic from the bailed node. -/
private partial def commit_token_join
    (stx : Lean.Syntax)
    (text : String)
    : emit_m Doc := do
  let pos := (stx.getPos?.map (·.byteIdx)).getD 0
  modify fun diagnostics =>
    if diagnostics.size > 0 && diagnostics[diagnostics.size - 1]!.pos == pos
        && diagnostics[diagnostics.size - 1]!.rule == "verbatim" then
      diagnostics.pop
    else
      diagnostics
  pure (.text text)

private partial def finish_verbatim
    (stx : Lean.Syntax)
    (doc : Doc)
    (text : String)
    : emit_m Doc := do
  if text.any (· == '\n') || (← read).breaking.preserveLineBreaks then return doc
  let some joined := Lean4Fmt.Emit.token_join? stx | return doc
  commit_token_join stx joined

/-- `walkCore` + the single-line bail interception: a DISPATCHED emitter that
    bails whole-node (`.verbatim`, one line) still gets the canonical token
    respacing the walk-default gives undispatched kinds — one seam closes the
    entire "dispatched but bailed" origin-carrier class (semicolon `do`s,
    pattern let-arrows, tuple bails, …). Multi-line verbatims and comment-gap
    joins stay byte-exact; preserveLineBreaks styles keep source bytes. -/
partial def walk
            (stx : Lean.Syntax)
            : emit_m Doc := do
  let document ← walkCore stx
  match document with
  -- discard the stale opt-out when a single-line bail ships as respaced text.
  | .verbatim text _ => finish_verbatim stx document text
  | _ => return document

end

/-- Format a whole module to a `Doc` plus collected diagnostics, under `style`. -/
def run (style : Style) (stx : Lean.Syntax) : Doc × Array Rules.Diagnostic :=
  (walk stx |>.run style).run #[]

/-- Convenience: format a module directly to a string. -/
def format (style : Style) (stx : Lean.Syntax) : String × Array Rules.Diagnostic :=
  let (doc, diags) := run style stx
  (Lean4Fmt.Doc.render style doc, diags)

end Lean4Fmt.Emit
