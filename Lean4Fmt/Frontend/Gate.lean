/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // FRONTEND // GATE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The runtime safety gate (DESIGN_V2 §4.2): format, then keep the result only
    if it reparses, preserves the token stream, keeps imports in the header, and
    is a fixed point — otherwise emit the original unchanged. Never worse than
    input, on any file.

    Drives the v2 `Emit → Doc → Render` spine (`Lean4Fmt.Emit.format`), which on
    the continuity corpus is correctness-parity with v1 (0 mangled / 0
    non-idempotent, 100% token-preserving over 234 files) and strictly better on
    layout (roughly half v1's over-width lines; preserves doc comments v1 dropped).
    The gate contract is unchanged: keep the active output only if it reparses,
    preserves the token stream, keeps imports in the header, and is a fixed point.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import Lean4Fmt.Emit
import Lean4Fmt.Style
import Lean4Fmt.Rules
import Lean4Fmt.Frontend.Parse
import Lean4Fmt.Frontend.Session
import Lean4Fmt.Syntax.Query

namespace Lean4Fmt.Frontend

open Lean

/-- Parse a module against `env`, cheap path first: the fast `testParseModule`
    (no elaboration) handles the vast majority; only when it can't (a file whose
    own/imported notation needs elaboration to parse, e.g. `Type*`) do we pay for
    the interleaved elaborating frontend (`Session.parseModule?`, `full` depth).
    `env` is imported once per process by `formatFile`; both the source parse and
    the fixed-point reparse reuse it (re-importing per call is what breaks). -/
unsafe def parseFull?
           (env : Environment)
           (path contents : String)
           (elabFallback : Bool := true)
           : IO (Option Lean.Syntax) := do

  match ← parseModule? env path contents with
  | some stx => pure (some stx)
  | none =>
    if elabFallback then Session.parseModule? env path contents
    else pure none

/-- The safety gate: return the text to emit — the actively-formatted output when
    it provably preserves meaning and is a fixed point, else the original — paired
    with the lint diagnostics for the source (the lint pass runs on the parsed
    syntax regardless of whether the reformat is kept). An unparseable file passes
    through UNCHANGED but never silently: a warning diagnostic says why (skipped
    coverage must be visible — a formatter that quietly no-ops looks like it ran). -/
unsafe def formatSafe
           (env : Environment)
           (path contents : String)
           (style : Lean4Fmt.Style.Style := Lean4Fmt.Style.default)
           (elabFallback : Bool := true)
           : IO (String × Array Lean4Fmt.Rules.Diagnostic) := do

  match ← parseFull? env path contents elabFallback with
  | none =>
    let msg :=
      if elabFallback then
        "not formatted: could not parse (unresolved imports or unsupported syntax)"
      else
        "not formatted: needs the elaborating frontend (rerun with --elab auto)"
    pure (contents, #[{ severity := .warning, rule := "parse", message := msg }])
  | some stx =>
    let lintDiags := Lean4Fmt.Rules.lint stx
    let (active, emitDiags) := Lean4Fmt.Emit.format style stx.updateLeading
    let diags := lintDiags ++ emitDiags
    if active == contents then pure (contents, diags)
    else
      match ← parseFull? env path active elabFallback with
      | none =>
        -- gate fallback is NEVER silent: an emitter bug that breaks the reparse
        -- would otherwise masquerade as a byte-identical "OK" in --check
        pure
          (
            contents,
            diags.push
              { severity := .warning,
                rule     := "gate",
                message  := "not formatted: output failed to reparse (gate fallback)" }
          )
      | some stx2 =>
        -- FRONTEND ALIGNMENT: a reformat can change which parser path a file
        -- takes (a sig-break moved a scoped-notation atom and the cheap
        -- parser gave up where it handled the source) — and the cheap and
        -- elaborating frontends can TOKENIZE such atoms differently, so
        -- comparing across paths spuriously rejects (gate-caught on mathlib
        -- PiSystem: source cheap / output Session → phantom "tokens").
        -- When the OUTPUT needed the elaborating frontend, re-parse the
        -- SOURCE through it too and compare like with like; if that parse
        -- fails, keep the conservative reject.
        let stx ← do
          if elabFallback
              && (← parseModule? env path active).isNone
              && (← parseModule? env path contents).isSome then
            pure ((← Session.parseModule? env path contents).getD stx)
          else pure stx
        let (active2, _) := Lean4Fmt.Emit.format style stx2.updateLeading
        let toksOk := Lean4Fmt.Syntax.leafToks stx == Lean4Fmt.Syntax.leafToks stx2 -- tokens preserved
        let spineOk := Lean4Fmt.Syntax.kindSpine stx == Lean4Fmt.Syntax.kindSpine stx2 -- tree shape kept: in
        -- whitespace-sensitive regions (tactic bullets, branches) identical
        -- tokens can parse to a DIFFERENT tree — re-scoped meaning the token
        -- check alone cannot see
        let cmtOk := Lean4Fmt.Syntax.commentContent stx == Lean4Fmt.Syntax.commentContent stx2 -- comments kept
        let hdrOk := headerToks stx == headerToks stx2 -- imports in header
        let fixOk := active2 == active -- fixed point
        if toksOk && spineOk && cmtOk && hdrOk && fixOk then pure (active, diags)
        else
          let why :=
            if !toksOk then
              "tokens"
            else if !spineOk then
              "tree"
            else if !cmtOk then "comments" else if !hdrOk then "header" else "fixed-point"
          -- L4F_DRILL_DIR: the drill loop's window into the otherwise
          -- unobservable pre-gate text — dump the rejected output (and the
          -- pass-2 text on fixed-point rejects), print the first token/spine
          -- divergence. Off unless the env var is set (this retires the
          -- hand-patched scratch-Gate dance the campaign log complains about).
          if let some dir ← IO.getEnv "L4F_DRILL_DIR" then
            let slug := path.replace "/" "_"
            IO.FS.createDirAll ⟨dir⟩
            IO.FS.writeFile ⟨s!"{dir}/{slug}.1.lean"⟩ active
            if !fixOk then IO.FS.writeFile ⟨s!"{dir}/{slug}.2.lean"⟩ active2
            if !toksOk then
              let t1 := Lean4Fmt.Syntax.leafToks stx
              let t2 := Lean4Fmt.Syntax.leafToks stx2
              let mut i := 0
              while i < Nat.min t1.size t2.size && t1[i]! == t2[i]! do
                i := i + 1
              IO.eprintln
                s!"TOKDIFF {path} @{i}: {(t1.extract (i - 2) (i + 4)).toList} vs {(t2.extract (i - 2) (i + 4)).toList} (sizes {t1.size}/{t2.size})"
            if toksOk && !spineOk then
              let k1 := Lean4Fmt.Syntax.kindSpine stx
              let k2 := Lean4Fmt.Syntax.kindSpine stx2
              let mut i := 0
              while i < Nat.min k1.size k2.size && k1[i]! == k2[i]! do
                i := i + 1
              IO.eprintln
                s!"SPINEDIFF {path} @{i}: {(k1.extract (i - 2) (i + 4)).toList} vs {(k2.extract (i - 2) (i + 4)).toList} (sizes {k1.size}/{k2.size})"
          pure
            (
              contents,
              diags.push
                { severity := .warning,
                  rule     := "gate",
                  message  := s!"not formatted: gate rejected output ({why})" }
            )

/-- Build the environment for a file (loads its imports) and format it. -/
unsafe def formatFile
           (path contents : String)
           (style : Lean4Fmt.Style.Style := Lean4Fmt.Style.default)
           (elabFallback : Bool := true)
           : IO (String × Array Lean4Fmt.Rules.Diagnostic) := do

  let ictx := Parser.mkInputContext contents path
  let (hdr, _, msgs) ← Parser.parseHeader ictx
  let (env, _) ← Elab.processHeader hdr {} msgs ictx (trustLevel := 1024)
  formatSafe env path contents style elabFallback

end Lean4Fmt.Frontend
