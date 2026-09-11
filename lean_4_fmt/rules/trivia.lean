/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // LEAN4FMT // RULES // TRIVIA
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Source-level whitespace and ruler hazards: trailing whitespace, missing
    final newline, and house banners that drift from the 81-column grid.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import lean_4_fmt.rules.diagnostic

namespace Lean4Fmt.Rules.Trivia

/-- Lint source-level whitespace hygiene. These are hazards rather than rewrites:
    the formatter normally removes them, while byte-exact policy regions may not. -/
def lint (src : String) : Array Lean4Fmt.Rules.Diagnostic :=
  let (_, diagnostics) :=
    (src.splitOn "\n").foldl
      (
        fun (state : Nat × Array Lean4Fmt.Rules.Diagnostic) line =>
          let (offset, diagnostics) := state
          let trailing := line.endsWith " " || line.endsWith "\t"
          let diagnostics :=
            if trailing then
              diagnostics.push
                { severity := .info,
                  pos      := offset,
                  rule     := "trivia/trailing-whitespace",
                  message  := "line has trailing whitespace" }
            else
              diagnostics
          let isRuler :=
            (line.startsWith "-- " && line.contains '─' && line.endsWith "─")
                || (line.startsWith "━" && line.all (· == '━'))
          let diagnostics :=
            if isRuler && line.length != 81 then
              diagnostics.push
                { severity := .info,
                  pos      := offset,
                  rule     := "house/ruler-width",
                  message  := s!"ruler spans {line.length} columns; house grid is 81" }
            else
              diagnostics
          (offset + line.utf8ByteSize + 1, diagnostics)
      )
      (0, #[])
  if !src.isEmpty && !src.endsWith "\n" then
    diagnostics.push
      { severity := .info,
        pos      := src.utf8ByteSize,
        rule     := "trivia/final-newline",
        message  := "file does not end with a newline" }
  else
    diagnostics

end Lean4Fmt.Rules.Trivia
