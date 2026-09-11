/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // FRONTEND // GATE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The runtime safety gate (doc/design.md §8): format, then keep the result only
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
import lean_4_fmt.emit
import lean_4_fmt.style
import lean_4_fmt.rules
import lean_4_fmt.frontend.parse
import lean_4_fmt.frontend.session
import lean_4_fmt.syntax.query

namespace Lean4Fmt.Frontend

open Lean

/-- Parse a module against `env`, cheap path first: the fast `testParseModule`
    (no elaboration) handles the vast majority; only when it can't (a file whose
    own/imported notation needs elaboration to parse, e.g. `Type*`) do we pay for
    the interleaved elaborating frontend (`Session.parseModule?`, `full` depth).
    `env` is imported once per process by `formatFile`; both the source parse and
    the fixed-point reparse reuse it (re-importing per call is what breaks). -/
unsafe
def parse_full?
    (env : Environment)
    (path contents : String)
    (elabFallback : Bool := true)
    : IO (Option Lean.Syntax) := do
  let some stx ← parse_module? env path contents |
    if elabFallback then Session.parse_module? env path contents else pure none
  pure (some stx)

private
structure rejection_context where
  path     : String
  active   : String
  active2  : String
  source   : Lean.Syntax
  output   : Lean.Syntax
  tokensOk : Bool
  spineOk  : Bool
  fixedOk  : Bool

/-- Materialize a rejected candidate for the opt-in drill workflow. -/
private unsafe
def dump_rejection (context : rejection_context) : IO Unit := do
  let some dir ← IO.getEnv "L4F_DRILL_DIR" | return
  let slug := context.path.replace "/" "_"
  IO.FS.createDirAll ⟨dir⟩
  IO.FS.writeFile ⟨s!"{dir}/{slug}.1.lean"⟩ context.active
  if !context.fixedOk then IO.FS.writeFile ⟨s!"{dir}/{slug}.2.lean"⟩ context.active2
  if !context.tokensOk then
    let sourceTokens := Lean4Fmt.Syntax.leaf_toks context.source
    let outputTokens := Lean4Fmt.Syntax.leaf_toks context.output
    let mut idx := 0
    while idx < Nat.min sourceTokens.size outputTokens.size
        && sourceTokens[idx]! == outputTokens[idx]! do
      idx := idx + 1
    IO.eprintln
      s!"TOKDIFF {context.path} @{idx}: {(sourceTokens.extract (idx - 2) (idx + 4)).toList} vs {(outputTokens.extract (idx - 2) (idx + 4)).toList} (sizes {sourceTokens.size}/{outputTokens.size})"
  if context.tokensOk && !context.spineOk then
    let sourceSpine := Lean4Fmt.Syntax.kind_spine context.source
    let outputSpine := Lean4Fmt.Syntax.kind_spine context.output
    let mut idx := 0
    while idx < Nat.min sourceSpine.size outputSpine.size
        && sourceSpine[idx]! == outputSpine[idx]! do
      idx := idx + 1
    IO.eprintln
      s!"SPINEDIFF {context.path} @{idx}: {(sourceSpine.extract (idx - 2) (idx + 4)).toList} vs {(outputSpine.extract (idx - 2) (idx + 4)).toList} (sizes {sourceSpine.size}/{outputSpine.size})"

private
def parse_failure
    (contents : String)
    (elabFallback : Bool)
    : String × Array Lean4Fmt.Rules.Diagnostic :=
  let message :=
    if elabFallback then
      "not formatted: could not parse (unresolved imports or unsupported syntax)"
    else
      "not formatted: needs the elaborating frontend (rerun with --elab auto)"
  (contents, #[{ severity := .warning, rule := "parse", message }])

/-- Exact-path identity clearances, composed as the union of colon-separated
    files in `L4F_IDENTITY_CLEARANCES`. Blank lines and `#` comments are inert.
    Set union makes layered policy associative, commutative, and idempotent;
    an absent file grants nothing. Clearances are consulted only AFTER a
    candidate has failed the semantic gate, so they cannot suppress linting or
    turn an unsafe candidate into formatted output — they name a deliberate
    identity result. -/
private unsafe
def identity_clearance? (target : String) : IO Bool := do
  let some specification ← IO.getEnv "L4F_IDENTITY_CLEARANCES" | return false
  for filename in specification.splitOn ":" do
    if filename.isEmpty then continue
    let path : System.FilePath := ⟨filename⟩
    if !(← path.pathExists) then continue
    let text ← IO.FS.readFile path
    for line in text.splitOn "\n" do
      let entry := line.trimAscii.toString
      if !entry.isEmpty && !entry.startsWith "#" && entry == target then
        return true
  return false

private
def identity_clearance_diag (reason : String) : Lean4Fmt.Rules.Diagnostic :=
  { severity := .debug, rule := "clearance", message := s!"identity fallback ({reason})" }

private unsafe
def reject_reparse
    (path contents active : String)
    (diags : Array Lean4Fmt.Rules.Diagnostic)
    : IO (String × Array Lean4Fmt.Rules.Diagnostic) := do

  -- expose the invalid candidate to the opt-in drill workflow.
  if let some dir ← IO.getEnv "L4F_DRILL_DIR" then
    IO.FS.createDirAll ⟨dir⟩
    IO.FS.writeFile ⟨s!"{dir}/{path.replace "/" "_"}.noparse.lean"⟩ active

  -- a cleared path degrades to identity quietly, at debug severity.
  if ← identity_clearance? path then
    return (contents, diags.push (identity_clearance_diag "reparse"))

  -- return the source with a visible safety-gate diagnostic.
  pure
    (
      contents,
      diags.push
        { severity := .warning,
          rule     := "gate",
          message  := "not formatted: output failed to reparse (gate fallback)" }
    )

private unsafe
def align_source_frontend
    (env : Environment)
    (path contents active : String)
    (elabFallback : Bool)
    (source : Lean.Syntax)
    : IO Lean.Syntax := do
  if elabFallback
      && (← parse_module? env path active).isNone
      && (← parse_module? env path contents).isSome then
    pure ((← Session.parse_module? env path contents).getD source)
  else
    pure source

private
def rejection_reason (tokensOk spineOk commentsOk headerOk : Bool) : String :=
  if !tokensOk then
    "tokens"
  else if !spineOk then
    "tree"
  else if !commentsOk then "comments" else if !headerOk then "header" else "fixed-point"

private unsafe
def validate_candidate
    (env : Environment)
    (path contents active : String)
    (style : Lean4Fmt.Style.Style)
    (elabFallback : Bool)
    (source output : Lean.Syntax)
    (diags : Array Lean4Fmt.Rules.Diagnostic)
    : IO (String × Array Lean4Fmt.Rules.Diagnostic) := do

  -- align both inputs on the elaborating frontend when the output requires it.
  let source ← align_source_frontend env path contents active elabFallback source
  let (active2, _) := Lean4Fmt.Emit.format style output.updateLeading

  -- prove preservation of tokens, tree shape, comments, header, and fixed point.
  let tokensOk := Lean4Fmt.Syntax.leaf_toks source == Lean4Fmt.Syntax.leaf_toks output
  let spineOk := Lean4Fmt.Syntax.kind_spine source == Lean4Fmt.Syntax.kind_spine output
  let commentsOk := Lean4Fmt.Syntax.comment_content source == Lean4Fmt.Syntax.comment_content output
  let headerOk := header_toks source == header_toks output
  let fixedOk := active2 == active
  if tokensOk && spineOk && commentsOk && headerOk && fixedOk then
    return (active, diags)

  -- record the failed proof and conservatively return the original source.
  let why := rejection_reason tokensOk spineOk commentsOk headerOk
  dump_rejection
    { path,
      active,
      active2,
      source,
      output,
      tokensOk,
      spineOk,
      fixedOk }
  if ← identity_clearance? path then
    return (contents, diags.push (identity_clearance_diag why))
  pure
    (
      contents,
      diags.push
        { severity := .warning,
          rule     := "gate",
          message  := s!"not formatted: gate rejected output ({why})" }
    )

/-- The safety gate: return the text to emit — the actively-formatted output when
    it provably preserves meaning and is a fixed point, else the original — paired
    with the lint diagnostics for the source (the lint pass runs on the parsed
    syntax regardless of whether the reformat is kept). An unparseable file passes
    through UNCHANGED but never silently: a warning diagnostic says why (skipped
    coverage must be visible — a formatter that quietly no-ops looks like it ran). -/
unsafe
def format_safe
    (env : Environment)
    (path contents : String)
    (style : Lean4Fmt.Style.Style := Lean4Fmt.Style.default)
    (elabFallback : Bool := true)
    : IO (String × Array Lean4Fmt.Rules.Diagnostic) := do
  let some source ← parse_full? env path contents elabFallback |
    return parse_failure contents elabFallback

  -- lint and render the parsed source.
  let lintDiags := Lean4Fmt.Rules.lint style source contents
  let (active, emitDiags) := Lean4Fmt.Emit.format style source.updateLeading
  let diags := lintDiags ++ emitDiags
  if active == contents then return (contents, diags)

  -- reject broken output or prove the complete safety-gate predicate.
  let some output ← parse_full? env path active elabFallback |
    return ← reject_reparse path contents active diags
  validate_candidate env path contents active style elabFallback source output diags

/-- Build the environment for a file (loads its imports) and format it. -/
unsafe
def format_file
    (path contents : String)
    (style : Lean4Fmt.Style.Style := Lean4Fmt.Style.default)
    (elabFallback : Bool := true)
    : IO (String × Array Lean4Fmt.Rules.Diagnostic) := do
  let ictx := Parser.mkInputContext contents path
  let (hdr, _, msgs) ← Parser.parseHeader ictx
  let (env, _) ← Elab.processHeader hdr {} msgs ictx (trustLevel := 1024)
  format_safe env path contents style elabFallback

end Lean4Fmt.Frontend
