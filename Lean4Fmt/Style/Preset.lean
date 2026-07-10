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
def straylight : Style := {
  layout     := { lineWidth := 100, indent := 2, continuationIndent := 4 }
  breaking   := { colon := .breakBefore, binders := .onePerLine, compactDo := true }
  alignment  := { structFields := .whenShort, matchArms := .whenShort, maxDelta := 8 }
  blankLines := { policy := .normalize, betweenTopLevelDecls := 1, maxConsecutive := 1 }
}

/-- Placeholder — tuned to minimize mathlib4 churn (§9). Currently = Straylight
    with the mathlib-ish binder fill (pack + wrap) and blank preservation. -/
def mathlib : Style := { straylight with
  breaking   := { straylight.breaking with binders := .fill, colon := .breakAfter }
  blankLines := { straylight.blankLines with policy := .preserve }
}

/-- Placeholder — the `aniva` community style (§14.2). Currently = Straylight. -/
def aniva : Style := straylight

/-- Look up a preset by name. -/
def byName? : String → Option Style
  | "straylight" => some straylight
  | "mathlib"    => some mathlib
  | "aniva"      => some aniva
  | _            => none

/-- The default preset. -/
def default : Style := straylight

end Lean4Fmt.Style
