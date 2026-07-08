/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // LEAN4FMT // FRONTEND
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The impure boundary: source → Environment → Syntax, plus the runtime SAFETY
    GATE (DESIGN_V2 §4.2). The gate guarantees the formatter is never worse than
    its input on ANY file:

        format s ⇒ s'
          keep s' only if  (1) it reparses,
                           (2) token stream is preserved (no drop/merge/reorder),
                           (3) the import header is unchanged, and
                           (4) it is a fixed point (format s' = s');
          otherwise emit s unchanged (identity is always meaning-preserving).

    This is the seatbelt from the v1 postmortem (§0.1): the pure emitter is
    meaning-preserving by construction, but the gate lets us honestly claim
    "never mangles" on corpora we have not exhaustively covered — a file using
    syntax the walker hasn't learned simply passes through untouched.

    NOTE (§0.5): parsing here uses `testParseModule`, which is sufficient for
    trees whose notation is import-provided (e.g. continuity) but cannot parse
    mathlib's `Type*` (registered by interleaved elaboration). A file it cannot
    parse degrades to identity — correct, just not reformatted. The interleaved
    parse+elaborate frontend that unblocks mathlib is deferred with mathlib.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import Lean4Fmt.Emitter

namespace Lean4Fmt.Frontend

open Lean

/-- Token stream (atoms + idents), ignoring whitespace/trivia and empty EOI
    atoms. A meaning-preserving formatter keeps this exactly (§0.1). -/
partial def leafToks : Syntax → Array String
  | .atom _ v => if v.isEmpty then #[] else #[v]
  | .ident _ _ n _ => #[n.toString]
  | .missing => #[]
  | .node _ _ args => args.foldl (fun acc x => acc ++ leafToks x) #[]

/-- Run an action with stdout redirected to a scratch buffer, so the lenient
    `testParseModule` (which prints diagnostics on parse errors) can never
    pollute our output. -/
def quietly {α} (act : IO α) : IO α := do
  let buf ← IO.mkRef { : IO.FS.Stream.Buffer }
  IO.withStdout (IO.FS.Stream.ofBuffer buf) act

/-- Parse a module quietly. Returns `none` if the source does not parse cleanly
    in this environment (parse error, missing nodes, or a thrown exception) —
    the caller then leaves the file untouched. -/
unsafe def parseModule? (env : Environment) (path contents : String) : IO (Option Syntax) :=
  quietly do
    try
      let stx ← Parser.testParseModule env path contents
      if stx.hasMissing then pure none else pure (some stx)
    catch _ => pure none

/-- Import tokens of a module's header — used to confirm the formatter did not
    move an `import` out of the header (a rule token-equality alone misses,
    since a misplaced import keeps the token *order*). -/
def headerToks (stx : Syntax) : Array String :=
  match stx.getArgs[0]? with
  | some h => leafToks h
  | none => #[]

/-- The safety gate. Given the file's environment and source, return the text to
    emit: the actively-formatted output when it provably preserves meaning and is
    a fixed point, otherwise the original source verbatim. -/
unsafe def formatSafe (env : Environment) (path contents : String)
    (cfg : StyleConfig := {}) : IO String := do
  match ← parseModule? env path contents with
  | none => pure contents                                    -- unparseable ⇒ identity
  | some stx =>
    let (active, _) := Lean4Fmt.format stx.updateLeading cfg
    if active == contents then pure contents                 -- already in form
    else match ← parseModule? env path active with
    | none => pure contents                                  -- output doesn't reparse ⇒ identity
    | some stx2 =>
      let (active2, _) := Lean4Fmt.format stx2.updateLeading cfg
      let ok := leafToks stx == leafToks stx2                -- (2) tokens preserved
            && headerToks stx == headerToks stx2             -- (3) imports stay in header
            && active2 == active                             -- (4) fixed point
      pure (if ok then active else contents)

/-- Build the environment for a file (loads its imports' oleans) and format it
    through the gate. -/
unsafe def formatFile (path contents : String) (cfg : StyleConfig := {}) : IO String := do
  let ictx := Parser.mkInputContext contents path
  let (hdr, _, msgs) ← Parser.parseHeader ictx
  let (env, _) ← Elab.processHeader hdr {} msgs ictx (trustLevel := 1024)
  formatSafe env path contents cfg

end Lean4Fmt.Frontend
