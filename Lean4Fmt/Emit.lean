/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                             // LEAN4FMT // EMIT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The walker: `Syntax → Doc` (DESIGN_V2 §2/§11). `walk` is the single recursive
    function; it dispatches on syntax kind to the per-category open-recursion
    emitters (`Emit/Module`, `Emit/Term`, …), passing itself so they can recurse.

    SCAFFOLD: every kind currently routes to verbatim reproduction (§4.1) — a
    safe, meaning-preserving no-op. Active formatting is filled in category by
    category; the safety gate (Frontend) guarantees correctness throughout.

    Pure. Depends on Doc, Style, Syntax, Rules.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Emit.Monad
import Lean4Fmt.Emit.Module
import Lean4Fmt.Emit.Decl
import Lean4Fmt.Emit.Command
import Lean4Fmt.Emit.Term
import Lean4Fmt.Emit.DoNotation
import Lean4Fmt.Emit.Tactic
import Lean4Fmt.Syntax.Kinds

namespace Lean4Fmt.Emit

open Lean Lean4Fmt.Doc Lean4Fmt.Style

/-- The single recursive walker. Dispatches to category emitters; falls back to
    verbatim reproduction for anything not yet actively formatted. -/
partial def walk
            (stx : Lean.Syntax)
            : EmitM Doc := do
  match stx with
  | .missing => pure .nil
  | .atom _ v => pure (.text v)
  | .ident _ _ n _ => pure (.text n.toString)
  | .node _ kind _ =>
    if kind == ``Lean.Parser.Module.module then Module.emit walk stx
    else if kind == ``Lean.Parser.Command.declaration then Decl.emit walk stx
    else if kind == ``Lean.Parser.Command.structure || kind == ``Lean.Parser.Command.inductive
         || kind == ``Lean.Parser.Command.mutual
         || kind == ``Lean.Parser.Command.open
         || kind == ``Lean.Parser.Command.namespace
         || kind == ``Lean.Parser.Command.end
         || kind == ``Lean.Parser.Command.section
         || kind == ``Lean.Parser.Command.universe
         || kind == ``Lean.Parser.Command.eval
         || kind == ``Lean.Parser.Command.in then
      Command.emit walk stx
    else if kind == ``Lean.Parser.Term.do
         || kind == ``Lean.Parser.Term.doLet
         || kind == ``Lean.Parser.Term.doLetArrow
         || kind == ``Lean.Parser.Term.doReassign
         || kind == ``Lean.Parser.Term.doReassignArrow
         || kind == ``Lean.Parser.Term.doExpr
         || kind == ``Lean.Parser.Term.doReturn
         || kind == ``Lean.Parser.Term.doIf
         || kind == ``Lean.Parser.Term.doMatch then
      DoNotation.emit walk stx
    else if kind == ``Lean.Parser.Term.byTactic
         || kind == ``Lean.Parser.Tactic.exact
         || kind == ``Lean.Parser.Tactic.apply
         || kind == ``Lean.Parser.Tactic.refine
         || kind == ``Lean.Parser.Tactic.rwSeq
         || kind == ``Lean.Parser.Tactic.unfold
         || kind == ``Lean.Parser.Tactic.induction
         || kind == ``Lean.Parser.Tactic.cases
         || kind == ``Lean.Parser.Tactic.tacticHave__
         || kind == `Lean.cdot
         || kind == ``Lean.Parser.Tactic.tacticRfl
         || kind == ``Lean.Parser.Tactic.omega
         || kind == ``Lean.Parser.Tactic.decide
         || kind == ``Lean.Parser.Tactic.nativeDecide
         || kind == ``Lean.Parser.Tactic.constructor
         || kind == ``Lean.Parser.Tactic.tacticTrivial
         || kind == ``Lean.Parser.Tactic.contradiction
         || kind == ``Lean.Parser.Tactic.assumption
         || kind == ``Lean.Parser.Tactic.tacticAnd_intros
         || kind == ``Lean.Parser.Tactic.simpAll
         || kind == ``Lean.Parser.Tactic.intro
         || kind == ``Lean.Parser.Tactic.intros
         || kind == ``Lean.Parser.Tactic.simp
         || kind == `Lean.Parser.Tactic.«tacticNext_=>_»
         || kind == ``Lean.Parser.Tactic.case
         || kind == ``Lean.Parser.Tactic.allGoals
         || kind == `Lean.Parser.Tactic.tacticRepeat_
         || kind == `Lean.Parser.Tactic.Conv.conv
         || kind == `Lean.calcTactic
         || kind == ``Lean.Parser.Tactic.split
         || kind == `Lean.Parser.Tactic.obtain
         || kind == `Lean.Parser.Tactic.rcases
         || kind == ``Lean.Parser.Tactic.show
         || kind == `Lean.Parser.Tactic.subst
         || kind == `Lean.Parser.Tactic.«tacticExists_,,»
         || kind == ``Lean.Parser.Tactic.change
         || kind == `«tacticBy_cases_:_»
         || kind == `Lean.Parser.Tactic.tacticSuffices_
         || kind == `Lean.Parser.Tactic.«tactic_<;>_»
         || kind == ``Lean.Parser.Tactic.simpAll
         || kind == `Lean.Parser.Tactic.dsimp
         || kind == `Lean.Parser.Tactic.simpa
         || kind == `Lean.Parser.Tactic.tacticRwa__
         || kind == `Lean.Parser.Tactic.first
         || kind == `Lean.Parser.Tactic.match
         || kind == `Lean.Parser.Tactic.tacticLet__
         || kind == `Lean.Parser.Tactic.congr
         || kind == `Lean.Parser.Tactic.renameI
         || kind == `Lean.Parser.Tactic.bvDecide
         || kind == `Lean.Parser.Tactic.left
         || kind == `Lean.Parser.Tactic.right
         || kind == `Lean.Parser.Tactic.revert
         || kind == `Lean.Parser.Tactic.injection
         || kind == `Lean.Parser.Tactic.tacticInfer_instance
         || kind == `Lean.Parser.Tactic.tacticExfalso
         || kind == `Lean.Parser.Tactic.«tacticNomatch_,,»
         || kind == `Lean.Parser.Tactic.paren
         || kind == `Lean.Parser.Tactic.generalize
         || kind == `Lean.Parser.Term.byTactic' then
      Tactic.emit walk stx
    -- expression constructs → Term (flat, comment-guarded; else verbatim)
    else if Lean4Fmt.Syntax.isBinOp kind
         || kind == ``Lean.Parser.Term.arrow
         || kind == ``Lean.Parser.Term.app
         || kind == ``Lean.Parser.Term.paren
         || kind == ``Lean.Parser.Term.proj
         || kind == ``Lean.Parser.Term.dotIdent
         || kind == ``Lean.Parser.Term.anonymousCtor
         || kind == ``Lean.Parser.Term.fun
         || kind == ``Lean.Parser.Term.tuple
         || kind == ``Lean.Parser.Term.structInst
         || kind == ``Lean.Parser.Term.hole
         || kind.toString == "«term[_]»"
         || kind.toString == "«term#[_,]»"
         || kind.toString == "termIfThenElse"
         || kind.toString == "termDepIfThenElse"
         || kind == ``Lean.Parser.Term.let
         || kind == ``Lean.Parser.Term.letrec
         || kind == ``Lean.Parser.Term.letDecl
         || kind == ``Lean.Parser.Term.letIdDecl
         || kind == ``Lean.Parser.Term.letPatDecl
         || kind == ``Lean.Parser.Term.letIdDeclNoBinders
         || kind == ``Lean.Parser.Term.match then
      Term.emit walk stx
    -- default: reproduce verbatim (safe; §4.1)
    else verbatim stx

/-- Format a whole module to a `Doc` plus collected diagnostics, under `style`. -/
def run
    (style : Style)
    (stx : Lean.Syntax)
    : Doc × Array Rules.Diagnostic :=

  (walk stx |>.run style).run #[]

/-- Convenience: format a module directly to a string. -/
def format
    (style : Style)
    (stx : Lean.Syntax)
    : String × Array Rules.Diagnostic :=

  let (doc, diags) := run style stx
  (Lean4Fmt.Doc.render style doc, diags)

end Lean4Fmt.Emit
