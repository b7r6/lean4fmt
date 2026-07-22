/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // STYLE // PRESET
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Named presets (DESIGN_V2 §6). A preset is just a `Style` value. Their
    coexistence under one knob set is the ontology's acceptance test (goal #2).

    Straylight is the house style (seeded from DESIGN.md — dense, break-after
    colon, align short runs). Mathlib and Aniva are placeholders (= Straylight)
    until their rules are pinned down (§14.1–2); they exist so the surface is
    real and the flexibility test is wired.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Style.Options

namespace Lean4Fmt.Style

/-- Straylight house style (§6). -/
def straylight
    : Style := {
  layout := { lineWidth := 100, indent := 2, continuationIndent := 4 }
  breaking := { colon := .breakBefore, binders := .onePerLine, attributesOwnLine := true, bodyOwnLine := true, compactDo := true }
  alignment := { structFields := .whenShort, matchArms := .whenShort,
                  trailingComments := .whenShort, maxDelta := 16 }
  blankLines := { policy := .normalize, betweenTopLevelDecls := 1, maxConsecutive := 1 }
}

/-- Placeholder — tuned to minimize mathlib4 churn (§9). Currently = Straylight
    with the mathlib-ish binder fill (pack + wrap) and blank preservation. -/
def mathlib
    : Style := { straylight with
  layout := { straylight.layout with bodyFitWidth := 70 }
  breaking := { straylight.breaking with binders := .fill, colon := .breakAfter, attributesOwnLine := true, bodyOwnLine := false, glueFun := true, opBreak := .trailing, listFill := true }
  alignment := { structFields := .never, matchArms := .never, recordFields := .never, trailingComments := .never }
  blankLines := { straylight.blankLines with policy := .preserve }
}

/-- The `aniva` style (Pantograph-derived), PRESCRIPTIVE: one canonical fixed
    point per parse, origin-agnostic. Inline signatures, break-after colon,
    normalized binder spacing (the repo's own 70/30 majority), no body blank,
    no alignment grids. -/
def aniva
    : Style := {
  layout := { lineWidth := 120, indent := 2, continuationIndent := 4 }
  breaking := { colon := .breakAfter, binders := .oneLine, attributesOwnLine := true,
                  bodyOwnLine := false, compactDo := true }
  alignment := { structFields := .never, matchArms := .never, recordFields := .never,
                  trailingComments := .never }
  blankLines := { policy := .normalize, betweenTopLevelDecls := 1, maxConsecutive := 1 }
}

/-- The `purtell` style (lithe-derived), PRESCRIPTIVE: inline signatures,
    attributes on the declaration line, inline-when-fits bodies, no grids. -/
def purtell
    : Style := {
  layout := { lineWidth := 120, indent := 2, continuationIndent := 4 }
  breaking := { colon := .breakAfter, binders := .oneLine, attributesOwnLine := true,
                  bodyOwnLine := false, compactDo := true, inlineBranches := true,
                  ctorsOneLine := true }
  alignment := { structFields := .never, matchArms := .never, recordFields := .never,
                  trailingComments := .never }
  blankLines := { policy := .normalize, betweenTopLevelDecls := 1, maxConsecutive := 1 }
}

/-- Look up a preset by name. -/
def byName? : String → Option Style
  | "straylight" => some straylight
  | "mathlib"    => some mathlib
  | "aniva"      => some aniva
  | "purtell"    => some purtell
  | _            => none

/-- The default preset. -/
def default : Style := straylight

end Lean4Fmt.Style
