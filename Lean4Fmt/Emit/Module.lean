/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // LEAN4FMT // EMIT // MODULE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Header + per-command dispatch. THIS is the passthrough seam: each top-level
    command is independently routed through `walk` — a handled kind (e.g. a
    declaration) is actively formatted, everything else is reproduced verbatim,
    with byte-exact tiling of leading trivia. Per-top-level-form granularity.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Emit.Monad

namespace Lean4Fmt.Emit.Module

open Lean Lean4Fmt.Doc

/-- Emit a whole module: header verbatim, then each command via `walk` (which
    dispatches per-command — handled kinds format, the rest pass through). -/
def emit (walk : Lean4Fmt.Emit.Walk) (stx : Lean.Syntax) : Lean4Fmt.Emit.EmitM Doc := do
  let args := stx.getArgs
  let headerDoc ← match args[0]? with
    | some h => Lean4Fmt.Emit.passthrough h
    | none => pure .nil
  let cmds := (args[1]?.map (·.getArgs)).getD #[]
  let mut acc := headerDoc
  for c in cmds do
    if c.getKind == ``Lean.Parser.Command.eoi then continue
    -- leading trivia (comments/blanks) placed literally by the module; `walk`
    -- returns the bare form — so unhandled forms tile byte-exactly and handled
    -- forms are actively formatted. Per-top-level-form granularity.
    acc := acc ++ Lean4Fmt.Emit.leadingRaw c ++ (← walk c)
  return acc

end Lean4Fmt.Emit.Module
