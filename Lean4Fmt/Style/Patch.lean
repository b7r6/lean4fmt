/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // LEAN4FMT // STYLE // PATCH
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `StylePatch` — overrides/config deltas (DESIGN_V2 §5). Every field Optional;
    `Append` merges with the right operand winning on `some`. CLI flags, project
    config, and per-dir config are all patches merged in precedence order.

    Scaffold: patches are modeled at sub-record granularity (whole-group
    override). Field-level Optional patches are a depth refinement.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Style.Options

namespace Lean4Fmt.Style

/-- A style override. Absent (`none`) groups leave the base untouched. -/
structure style_patch where
  layout     : Option Layout := none
  breaking   : Option breaking := none
  alignment  : Option alignment := none
  blankLines : Option blank_lines := none
  spacing    : Option spacing := none
  imports    : Option imports := none
  comments   : Option comments := none
  naming     : Option Naming := none
  linting    : Option Linting := none
  deriving Inhabited

/-- Right-biased merge: the later patch wins per group. Named so the
    composition laws can unfold the operation directly. -/
def style_patch.append (a b : style_patch) : style_patch := {
  layout := b.layout <|> a.layout
  breaking := b.breaking <|> a.breaking
  alignment := b.alignment <|> a.alignment
  blankLines := b.blankLines <|> a.blankLines
  spacing := b.spacing <|> a.spacing
  imports := b.imports <|> a.imports
  comments := b.comments <|> a.comments
  naming := b.naming <|> a.naming
  linting := b.linting <|> a.linting
}

instance : Append style_patch := ⟨style_patch.append⟩

/-- Apply a patch to a base style (patch wins where present). -/
def Style.apply (base : Style) (p : style_patch) : Style := {
  layout := p.layout.getD base.layout
  breaking := p.breaking.getD base.breaking
  alignment := p.alignment.getD base.alignment
  blankLines := p.blankLines.getD base.blankLines
  spacing := p.spacing.getD base.spacing
  imports := p.imports.getD base.imports
  comments := p.comments.getD base.comments
  naming := p.naming.getD base.naming
  linting := p.linting.getD base.linting
}

/-- A path-local override. `root` is a component path relative to the policy
    tree's root; an empty root applies to the whole tree. -/
structure tree_override where
  root  : List String
  patch : style_patch
  deriving Inhabited

/-- A root-to-leaf policy program. List order is precedence order: later
    matching entries win through `style_patch.append`. -/
abbrev override_tree := List tree_override

/-- Does this override's root contain `path`? Matching is component-wise, so
    `["Core"]` matches `["Core", "Codec"]` but not `["CoreCodec"]`. -/
def tree_override.matches (override : tree_override) (path : List String) : Bool :=
  override.root.isPrefixOf path

/-- Resolve all overrides matching `path`, in list order. Non-matching entries
    are identity steps; later matching entries have deterministic precedence. -/
def override_tree.resolve (base : Style) (path : List String) : override_tree → Style
  | [] => base
  | override :: rest =>
    let next := if override.matches path then base.apply override.patch else base
    override_tree.resolve next path rest

/-- Compose policy trees in precedence order. All entries in `later` run after
    all entries in `earlier`. -/
def override_tree.overlay (earlier later : override_tree) : override_tree := earlier ++ later

/-- A policy relation expressing that the right style is at least as tight as
    the left. Concrete lint axes supply the relation; the override algebra only
    needs its preservation law. -/
abbrev Tightening := Style → Style → Prop

/-- A patch is monotone for a tightening relation when applying it to both
    sides preserves that relation. -/
def style_patch.preserves_tightening (tightens : Tightening) (patch : style_patch) : Prop :=
  ∀ lowerStyle upperStyle,
      tightens lowerStyle upperStyle → tightens (lowerStyle.apply patch) (upperStyle.apply patch)

/-- Every patch in the tree preserves the selected tightening relation. -/
def override_tree.preserves_tightening (tightens : Tightening) (tree : override_tree) : Prop :=
  ∀ override, override ∈ tree → override.patch.preserves_tightening tightens

end Lean4Fmt.Style
