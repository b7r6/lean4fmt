/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // LEAN4FMT // DRIVER // WALK
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Tree discovery: find `.lean` files under a root. doc/design.md §11 will replace
    this plain walk with `StdlibEx.Linux.Fanotify.scanTree` (§11.1 stage 2) for
    (path, mtime, size) + an mtime skip-cache. Plain recursion for now.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Lean

namespace Lean4Fmt.Driver

/-- All `.lean` files under `root` (recursive), skipping `.lake` build dirs. -/
partial
def find_lean (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut files : Array System.FilePath := #[]
  if ← root.isDir then
    for entry in ← root.readDir do
      if entry.fileName == ".lake" then continue
      files := files ++ (← find_lean entry.path)
  else if root.extension == some "lean" then files := files.push root
  return files

end Lean4Fmt.Driver
