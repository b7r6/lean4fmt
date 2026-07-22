/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // LEAN4FMT // DRIVER // WALK
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Tree discovery: find `.lean` files under a root. DESIGN_V2 §11 will replace
    this plain walk with `StdlibEx.Linux.Fanotify.scanTree` (§11.1 stage 2) for
    (path, mtime, size) + an mtime skip-cache. Plain recursion for now.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean

namespace Lean4Fmt.Driver

/-- All `.lean` files under `root` (recursive), skipping `.lake` build dirs. -/
partial def findLean
            (root : System.FilePath)
            : IO (Array System.FilePath) := do

  let mut acc : Array System.FilePath := #[]
  if ← root.isDir then
    for entry in ← root.readDir do
      if entry.fileName == ".lake" then continue
      acc := acc ++ (← findLean entry.path)
  else if root.extension == some "lean" then acc := acc.push root
  return acc

end Lean4Fmt.Driver
