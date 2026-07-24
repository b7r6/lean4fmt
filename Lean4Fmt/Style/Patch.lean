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
  deriving Inhabited

/-- Right-biased merge: the later patch wins per group. -/
instance : Append style_patch :=
  ⟨
    fun a b => {
      layout := b.layout <|> a.layout
      breaking := b.breaking <|> a.breaking
      alignment := b.alignment <|> a.alignment
      blankLines := b.blankLines <|> a.blankLines
      spacing := b.spacing <|> a.spacing
      imports := b.imports <|> a.imports
      comments := b.comments <|> a.comments
    }
  ⟩

/-- Apply a patch to a base style (patch wins where present). -/
def Style.apply (base : Style) (p : style_patch) : Style := {
  layout := p.layout.getD base.layout
  breaking := p.breaking.getD base.breaking
  alignment := p.alignment.getD base.alignment
  blankLines := p.blankLines.getD base.blankLines
  spacing := p.spacing.getD base.spacing
  imports := p.imports.getD base.imports
  comments := p.comments.getD base.comments
}

end Lean4Fmt.Style
