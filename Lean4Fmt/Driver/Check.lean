/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // LEAN4FMT // DRIVER // CHECK
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    --check: is the file already formatted? (DESIGN_V2 §11). First-difference
    reporting will use `StdlibEx.Bytes.memmem` (§11.1 stage 1); for now a plain
    equality check.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean4Fmt.Driver.Format

namespace Lean4Fmt.Driver

/-- `true` iff the file is already in formatted form. -/
unsafe
def isFormatted (path : String) (width : Nat := 100) : IO Bool := do
  let (out, _) ← formatFile path width
  let orig ← IO.FS.readFile path
  return out == orig

end Lean4Fmt.Driver
