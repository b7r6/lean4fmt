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
import Lean4Fmt.Emit.Tokens
import Lean4Fmt.Emit.Module
import Lean4Fmt.Emit.Decl
import Lean4Fmt.Emit.Command
import Lean4Fmt.Emit.Term
import Lean4Fmt.Emit.DoNotation
import Lean4Fmt.Emit.Tactic
import Lean4Fmt.Syntax.Kinds

namespace Lean4Fmt.Emit

open Lean Lean4Fmt.Doc Lean4Fmt.Style

mutual

/-- The single recursive walker. Dispatches to category emitters; falls back to
    verbatim reproduction for anything not yet actively formatted. Term routing
    is DATA (`Syntax.Kinds.walkTermKinds` — the porting checklist lives on it);
    the do/tactic/command lists below are single-consumer and stay inline. -/
partial def walkCore
            (stx : Lean.Syntax)
            : EmitM Doc := do
  match stx with
  | .missing => pure .nil
  | .atom _ v => pure (.text v)
  | .ident _ _ n _ =>
    -- SOURCE bytes, not `n.toString`: a keyword-named ident (`«have»`,
    -- `«let»`) round-trips through toString WITHOUT its guillemets and
    -- reparses as the keyword (found on Pantograph — MANGLED)
    let t := Lean4Fmt.Emit.bareSrc stx
    -- an EMPTY-SOURCE anonymous ident is SYNTHETIC (cdot expansion): its
    -- toString would INJECT the literal text "[anonymous]" into the output
    -- (gate-caught on mathlib Determinant, tokens +1) — emit nothing
    pure (.text (if t.isEmpty then (if n == Lean.Name.anonymous then "" else n.toString) else t))
  | .node _ kind _ =>
    if kind == ``Lean.Parser.Module.module then Module.emit walk stx
    else if kind == ``Lean.Parser.Command.declaration
         || kind == `lemma then   -- mathlib's `lemma` command: theorem-shaped
      Decl.emit walk stx
    else if kind == ``Lean.Parser.Command.structure || kind == ``Lean.Parser.Command.inductive
         || kind == ``Lean.Parser.Command.mutual
         || kind == ``Lean.Parser.Command.open
         || kind == ``Lean.Parser.Command.namespace
         || kind == ``Lean.Parser.Command.end
         || kind == ``Lean.Parser.Command.section
         || kind == ``Lean.Parser.Command.universe
         || kind == ``Lean.Parser.Command.variable
         || kind == ``Lean.Parser.Command.eval
         || kind == ``Lean.Parser.Command.in then
      Command.emit walk stx
    else if (← read).breaking.preserveLineBreaks && kind == ``Lean.Parser.Term.do
        && !(Lean4Fmt.Emit.bareSrc stx).any (· == '\n')
        && !(Lean4Fmt.Emit.bareSrc stx).isEmpty then
      pure (.text (Lean4Fmt.Emit.bareSrc stx))
    else if kind == ``Lean.Parser.Term.do
         || kind == ``Lean.Parser.Term.doNested
         || kind == ``Lean.Parser.Term.doFor
         || kind == `Lean.Parser.Term.doWhile
         || kind == `Lean.Parser.Term.doUnless
         || kind == ``Lean.Parser.Term.doLet
         || kind == ``Lean.Parser.Term.doLetRec
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
         || kind == `Mathlib.Tactic.tacticSimp_rw___
         || kind == `Lean.Parser.Tactic.«tacticNext_=>_»
         || kind == ``Lean.Parser.Tactic.case
         || kind == ``Lean.Parser.Tactic.allGoals
         || kind == `Lean.Parser.Tactic.tacticRepeat_
         || kind == `Lean.Parser.Tactic.Conv.conv
         || kind == `Lean.calcTactic
         || kind == `Lean.calc
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
         || kind == `Lean.Parser.Tactic.classical
         || kind == `Lean.Parser.Term.byTactic' then
      Tactic.emit walk stx
    -- expression constructs → Term (flat, comment-guarded; else verbatim).
    -- preserveLineBreaks: TERMS ride byte-exact wholesale — single-line via
    -- the active-text default, multi-line via verbatim. The author's break
    -- decisions inside expressions are load-bearing; structure (decls, do,
    -- tactics, seams) stays active.
    else if (← read).breaking.preserveLineBreaks
        && (kind == ``Lean.Parser.Term.match || Lean4Fmt.Syntax.isBinOp kind
            || kind.toString.startsWith "Lean.Parser.Term"
            || kind.toString.startsWith "term"
            || kind.toString.startsWith "«term") then
      let t := Lean4Fmt.Emit.bareSrc stx
      if !t.isEmpty && !t.any (· == '\n') then pure (.text t)
      else verbatim stx
    else if Lean4Fmt.Syntax.isBinOp kind
         || Lean4Fmt.Syntax.isBinderComma kind
         || Lean4Fmt.Syntax.walkTermKinds.contains kind then
      Term.emit walk stx
    -- default: a SINGLE-LINE construct rides as active text — byte-exact
    -- (bareSrc is the source bytes, inter-token trivia included) and
    -- content-safe either way (T1 covers text and verbatim alike); only
    -- multi-line constructs need opaque re-anchoring (§4.1). This is what
    -- makes literals, types, and custom notations ACTIVE without per-kind
    -- ports — the opt-out log shows only the multi-line residue.
    else
      let t := Lean4Fmt.Emit.bareSrc stx
      if !t.isEmpty && !t.any (· == '\n') then
        -- canonical respacing (zero-passthrough): ws gaps collapse to one
        -- space; when tokenJoin? can't (choice nodes, synthetic-info gaps,
        -- interior comments), the LEXICAL ws-collapse still applies — token
        -- and comment bytes survive, interior space runs do not. Quotation
        -- kinds are content byte-exact (pin); templates are guarded inside
        -- canonVerbatimWs itself.
        match Lean4Fmt.Emit.tokenJoin? stx with
        | some t' => pure (.text t')
        | none => pure (.text (Lean4Fmt.Emit.canonWsPiecewise stx t))
      else verbatim stx

/-- `walkCore` + the single-line bail interception: a DISPATCHED emitter that
    bails whole-node (`.verbatim`, one line) still gets the canonical token
    respacing the walk-default gives undispatched kinds — one seam closes the
    entire "dispatched but bailed" origin-carrier class (semicolon `do`s,
    pattern let-arrows, tuple bails, …). Multi-line verbatims and comment-gap
    joins stay byte-exact; preserveLineBreaks styles keep source bytes. -/
partial def walk
            (stx : Lean.Syntax)
            : EmitM Doc := do
  let d ← walkCore stx
  match d with
  | .verbatim s _ =>
    if s.any (· == '\n') || (← read).breaking.preserveLineBreaks then return d
    match Lean4Fmt.Emit.tokenJoin? stx with
    | some t =>
      -- walkCore's bail logged an opt-out for THIS node, but the respaced
      -- text ships — pop the stale entry so the trail reports emissions
      -- (it was the misreport the census had to caveat)
      let pos := (stx.getPos?.map (·.byteIdx)).getD 0
      modify fun ds =>
        if ds.size > 0 && ds[ds.size - 1]!.pos == pos
            && ds[ds.size - 1]!.rule == "verbatim" then ds.pop else ds
      return .text t
    | none => return d
  | _ => return d

end

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
