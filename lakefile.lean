import Lake
open Lake DSL

/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                          // LEAN4FMT // LAKEFILE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Lean 4 source formatter — one artifact, one target. It runs the real
    frontend (Parser → PrettyPrinter), so it imports only Lean core and requires
    NOTHING internal for now: it slots into the tree ahead of the stdlib
    straighten-out. When StdlibEx.{CLI,Logging,Bytes} land, they become `require`
    edges here and this becomes their second consumer.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

package «lean4fmt» where
  -- StdlibEx shims (spdlog logging) compile against libstdc++; the link names
  -- it here (stdlibex decision VII: never mix libc++ and libstdc++)
  moreLinkArgs := #["-lspdlog", "-lfmt", "-lstdc++", "-lpthread"]
  leanOptions := #[⟨`autoImplicit, false⟩]

-- StdlibEx.Logging (spdlog-backed leveled sinks) — the diagnostic sink.
-- The shims archive (extern_lib «straylight-shims») links automatically
-- through the dependency closure.
require «stdlibex» from ".." / "stdlibex"

lean_lib «Lean4Fmt» where
  -- the whole v2 tree: the barrel (Lean4Fmt.lean) plus every Lean4Fmt.* submodule
  globs := #[.andSubmodules `Lean4Fmt]

@[default_target]
lean_exe «lean4fmt» where
  root := `Main
  -- Required to run module initializers when importing syntax extensions
  supportInterpreter := true
