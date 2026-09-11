/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // STYLE // PRESET
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Named presets (doc/design.md §6). A preset is just a `Style` value. Their
    coexistence under one knob set is the ontology's acceptance test (goal #2).

    Straylight is the house style (seeded from doc/style.md — dense, break-after
    colon, align short runs). Mathlib and Aniva are placeholders (= Straylight)
    until their rules are pinned down (§14.1–2); they exist so the surface is
    real and the flexibility test is wired.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.style.options

namespace Lean4Fmt.Style

/-- Straylight house style (§6). -/
def straylight : Style :=
  {
    layout := { lineWidth := 100, indent := 2, continuationIndent := 4 }
    -- the exemplar pins (G-L4/G-L5): visibility on its own line, adaptive
    -- signatures through the solver, no imposed body blank.
    breaking := { colon := .breakBefore, binders := .adaptive, attributesOwnLine := true,
                    visibilityOwnLine := true, bodyOwnLine := false, solveDefs := true,
                    compactDo := true, guardIfOwnLine := true,
                    glueFun := true, listFill := true }
    alignment := { structFields := .whenShort, matchArms := .whenShort,
                    trailingComments := .whenShort, maxDelta := 16 }
    blankLines := { policy := .normalize, betweenTopLevelDecls := 1, maxConsecutive := 1 }
    -- systems house convention: every naming axis canonicalizes to snake.
    naming := { namespaces := .snake, types := .snake, theorems := .snake, terms := .snake }
    -- systems terms of art survive the three-character floor; lazy one-letter
    -- locals do not acquire a blanket exemption.
    linting := {
      symbolMinChars := 3
      branchDensityMax := 12
      handlerParameterMax := 6
      requireStanzaComments := true
      requireTraditionalInstances := true
      requirePositionalLoopNames := true
      requireSemanticPatternBinders := true
      requireSemanticCollectionLoopNames := true
      requireSemanticFieldNames := true
      requireSemanticDeclarationNames := true
      requireSemanticRecursiveHelperNames := true
      requireSemanticLambdaNames := true
      requireSemanticLetNames := true
      symbolAllow := [(2, ["fd", "ud"])]
      symbolDeny := ["acc", "tmp", "foo", "bar", "baz"]
      fieldAllow := [(2, ["st"])]
    }
  }

/-- Placeholder — tuned to minimize mathlib4 churn (§9). Currently = Straylight
    with the mathlib-ish binder fill (pack + wrap) and blank preservation. -/
def mathlib : Style :=
  { straylight with
    layout := { straylight.layout with bodyFitWidth := 70 }
    -- pinned to the census-measured behavior: no straylight exemplar inherits.
    breaking := { straylight.breaking with binders := .fill, colon := .breakAfter, attributesOwnLine := true, visibilityOwnLine := false, bodyOwnLine := false, solveDefs := false, glueFun := true, opBreak := .trailing, listFill := true }
    alignment := { structFields := .never, matchArms := .never, recordFields := .never, trailingComments := .never }
    blankLines := { straylight.blankLines with policy := .preserve }
    linting := {}
  }

/-- The `aniva` style (Pantograph-derived), PRESCRIPTIVE: one canonical fixed
    point per parse, origin-agnostic. Inline signatures, break-after colon,
    normalized binder spacing (the repo's own 70/30 majority), no body blank,
    no alignment grids. -/
def aniva : Style :=
  {
    layout := { lineWidth := 120, indent := 2, continuationIndent := 4 }
    breaking := { colon := .breakAfter, binders := .oneLine, attributesOwnLine := true,
                    bodyOwnLine := false, compactDo := true }
    alignment := { structFields := .never, matchArms := .never, recordFields := .never,
                    trailingComments := .never }
    blankLines := { policy := .normalize, betweenTopLevelDecls := 1, maxConsecutive := 1 }
  }

/-- The `purtell` style (lithe-derived), PRESCRIPTIVE: inline signatures,
    attributes on the declaration line, inline-when-fits bodies, no grids. -/
def purtell : Style :=
  {
    layout := { lineWidth := 120, indent := 2, continuationIndent := 4 }
    breaking := { colon := .breakAfter, binders := .oneLine, attributesOwnLine := true,
                    bodyOwnLine := false, compactDo := true, inlineBranches := true,
                    ctorsOneLine := true }
    alignment := { structFields := .never, matchArms := .never, recordFields := .never,
                    trailingComments := .never }
    blankLines := { policy := .normalize, betweenTopLevelDecls := 1, maxConsecutive := 1 }
  }

/-- Look up a preset by name. -/
def by_name? : String → Option Style
  | "straylight" => some straylight
  | "mathlib"    => some mathlib
  | "aniva"      => some aniva
  | "purtell"    => some purtell
  | _            => none

/-- The default preset. -/
def default : Style := straylight

end Lean4Fmt.Style
