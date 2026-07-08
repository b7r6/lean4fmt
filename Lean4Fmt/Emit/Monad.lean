/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // LEAN4FMT // EMIT // MONAD
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The walk monad: `EmitM = ReaderT Style (StateM Diagnostics)`, producing `Doc`.
    The walker expresses INTENT; the renderer decides realization.

    Note on structure (DESIGN_V2 §11): Lean can't have mutual recursion across
    modules, so the recursion lives in one place (`Emit.walk`) and the per-
    category emitters (`Emit/Module`, `Emit/Term`, …) are OPEN-RECURSION functions
    that take `walk` as a parameter. That is what lets the split live in separate
    files without a single 1.3k-line function.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean
import Lean4Fmt.Doc
import Lean4Fmt.Style
import Lean4Fmt.Rules.Diagnostic
import Lean4Fmt.Syntax.Trivia

namespace Lean4Fmt.Emit

open Lean Lean4Fmt.Doc Lean4Fmt.Style

abbrev EmitM := ReaderT Style (StateM (Array Rules.Diagnostic))

def style : EmitM Style := read
def emitDiag (d : Rules.Diagnostic) : EmitM Unit := modify (·.push d)

/-- The open-recursion walker type: category emitters receive `walk` so they can
    recurse into children without cross-module mutual recursion. -/
abbrev Walk := Lean.Syntax → EmitM Doc

/-- Bare source of a form (no leading/trailing trivia). -/
def bareSrc (stx : Lean.Syntax) : String :=
  (stx.getSubstring? false false).map (·.toString) |>.getD ""

/-- Opaque reproduction (§4.1): the safe default for any construct not yet
    actively formatted. Reproduces the BARE original source as a re-anchorable
    `verbatim` doc (leading trivia is placed by the caller / `Module`). -/
def verbatim (stx : Lean.Syntax) : EmitM Doc :=
  let s := bareSrc stx
  if s.isEmpty then
    match stx.reprint with | some r => pure (.verbatim r 0) | none => pure .nil
  else pure (.verbatim s 0)

/-- Byte-exact passthrough of a whole form INCLUDING its leading trivia. -/
def passthrough (stx : Lean.Syntax) : EmitM Doc :=
  pure (.textRaw ((stx.getSubstring? true false).map (·.toString) |>.getD ""))

/-- The leading trivia (comments + blank lines) before a form, as literal text. -/
def leadingRaw (stx : Lean.Syntax) : Doc :=
  .textRaw (Lean4Fmt.Syntax.leading? stx |>.getD "")

/-- The trailing trivia after a form, as literal text. `leadingRaw next` +
    `trailingRaw prev` partition the inter-form gap exactly. -/
def trailingRaw (stx : Lean.Syntax) : Doc :=
  .textRaw (Lean4Fmt.Syntax.trailing? stx |>.getD "")

end Lean4Fmt.Emit
