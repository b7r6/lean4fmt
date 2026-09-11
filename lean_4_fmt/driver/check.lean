/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // LEAN4FMT // DRIVER // CHECK
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    --check: is the file already formatted? (doc/design.md §11). First-difference
    reporting will use `StdlibEx.Bytes.memmem` (§11.1 stage 1); for now a plain
    equality check.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import lean_4_fmt.driver.format

namespace Lean4Fmt.Driver

/-- `true` iff the file is already in formatted form. -/
unsafe
def is_formatted (path : String) (width : Nat := 100) : IO Bool := do
  let (out, _) ← format_file path width
  let orig ← IO.FS.readFile path
  return out == orig

end Lean4Fmt.Driver
