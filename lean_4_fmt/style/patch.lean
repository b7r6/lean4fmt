/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // LEAN4FMT // STYLE // PATCH
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `StylePatch` — overrides/config deltas (doc/design.md §7.1). Every field Optional;
    `Append` merges with the right operand winning on `some`. CLI flags, project
    config, and per-dir config are all patches merged in precedence order.

    Scaffold: patches are modeled at sub-record granularity (whole-group
    override). Field-level Optional patches are a depth refinement.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.style.options

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
def style_patch.append (leftValue rightValue : style_patch) : style_patch := {
  layout := rightValue.layout <|> leftValue.layout
  breaking := rightValue.breaking <|> leftValue.breaking
  alignment := rightValue.alignment <|> leftValue.alignment
  blankLines := rightValue.blankLines <|> leftValue.blankLines
  spacing := rightValue.spacing <|> leftValue.spacing
  imports := rightValue.imports <|> leftValue.imports
  comments := rightValue.comments <|> leftValue.comments
  naming := rightValue.naming <|> leftValue.naming
  linting := rightValue.linting <|> leftValue.linting
}

instance : Append style_patch := ⟨style_patch.append⟩

/-- Apply a patch to a base style (patch wins where present). -/
def Style.apply (base : Style) (predicate : style_patch) : Style := {
  layout := predicate.layout.getD base.layout
  breaking := predicate.breaking.getD base.breaking
  alignment := predicate.alignment.getD base.alignment
  blankLines := predicate.blankLines.getD base.blankLines
  spacing := predicate.spacing.getD base.spacing
  imports := predicate.imports.getD base.imports
  comments := predicate.comments.getD base.comments
  naming := predicate.naming.getD base.naming
  linting := predicate.linting.getD base.linting
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
