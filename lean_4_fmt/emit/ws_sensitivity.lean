/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                            // LEAN4FMT // EMIT // WS-SENSITIVITY
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    THE TAXONOMY of whitespace-sensitivity hazards — the one home for a class
    of bug that was previously scattered across commit messages and
    "gate-caught on <file>" comments. The general law, learned the hard way
    across the mathlib campaign:

        every class is "the layout changed a column the parser reads."

    Lean's grammar is whitespace-sensitive at specific seams (colGt/colGe
    constraints, block openers, bullet sequences). A layout decision that
    moves a column the parser CONSULTS changes the parse; the safety gate then
    rejects the output (reparse-fail, tree, tokens, or fixed-point) and the
    file silently degrades to identity. The classes, with mechanism homes:

    CLASS 1 — INLINE FORM AFTER A BLOCK-OPENING KEYWORD. A breakable doc glued
      after a keyword that opens a whitespace-sensitive block (`classical
      exact <breaks>`): the continuation lines fall out of the block and error
      recovery can silently DROP tokens. Mechanism: such keywords take the
      BLOCK form always (Emit/Tactic, `classical` branch). Never put a
      breakable doc after an inline block-opening keyword. Gate-caught:
      Denumerable (tokens).

    CLASS 2 — GLUED BLOCK ANCHORED SHALLOW (bullet column). A doc glued after
      visible text (`· `) whose interior breaks anchor at the LINE's indent,
      not the glue-point COLUMN: continuations land 2 columns shallow and
      re-parse as bullet-seq SIBLINGS. Mechanism: `.align` after the glue text
      (Emit/Tactic, `cdot` branch) — align sets break-indent to the current
      column, the general cure for text-shifted glue positions. Gate-caught
      ×2 (tree).

    CLASS 3 — MULTI-LINE TYPE IN FILL MODE IS UNPLACEABLE. A multi-line
      (verbatim) type in a fill-mode signature: GLUED, its re-anchor base
      drifts pass-to-pass (fixed-point reject); OWN-LINE, re-anchoring changes
      the type's interior COLUMN RELATIONS and a `letI`-in-type continuation
      re-parsed as an application argument under colGt (reparse-fail).
      Mechanism: whole-decl verbatim bail (Emit/Decl `defnDoc`,
      `!typeOK && binders == .fill`). Gate-caught: ZeroMorphisms,
      Localization/Monoidal/Functor.

    CLASS 4 — COLUMN-ALIGNED STRUCTINST (the lexical-exemption lesson). A
      comma-less multi-line `{  f := v` aligns its fields BY COLUMN and the
      post-`{` space run SETS that column; ws-canon collapsing it shifts the
      first field off the column and the output fails to reparse. Mechanism:
      canonVerbatimWs exempts exactly the space run after `{` (Doc/Render —
      LEXICAL, deliberately in the scanner); fuzz/perturb.py mirrors it (the
      post-`{` gap is content). THE LESSON: canon exemptions must be LEXICAL
      AND NARROW, never subtree-wide — the subtree-guard v1 traded
      zero-passthrough for safety and the fuzzer caught it (19 divergences).
      Gate-caught: Submonoid/Defs, Cones, Kernels.

    CLASS 5 — RE-ANCHORED MULTI-LINE TOKEN. A `verbatim` block re-anchors by
      column (dedent by its own base, re-indent at placement) — which REWRITES
      the interior bytes of any multi-line TOKEN it carries (docstrings,
      strings): placement-safe only at zero shift. Mechanism:
      `reanchorsMultilineToken` (below) keeps the carrying span whole-decl
      verbatim (Emit/Decl, suffix/tail sites ×3). The docstring-poison
      variant: a mutual-member drift-bail must use `hasMultilineReanchor`
      (verbatim-only), never `hasMultilineVerbatim` — `.textRaw` docstrings
      emit at source columns and are placement-stable. Gate-caught: Log
      (tokens), Squarefree (comments).

    New hazards join HERE: name the trigger, the failure signature (which gate
    check rejects), the mechanism and its home, and the fuzzer mirror if the
    mechanism touches ws-canon. The drill method (TOKDIFF/SPINEDIFF probes +
    writeFile-on-reject + reparse the dump) lives in the campaign log.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Lean4Fmt.Emit

/-- CLASS 5 detector: does this span carry a multi-line comment token
    (docstring or block comment)? A verbatim re-anchors by column, which
    rewrites the interior bytes of any multi-line token it contains — the
    carrying span must stay whole-decl verbatim. (The probe string is the
    comment OPENER; spelling it here would nest — this docstring is itself
    such a token.) -/
def reanchors_multiline_token (source : String) : Bool :=
  source.any (· == '\n') && (source.splitOn "/-").length > 1

end Lean4Fmt.Emit
