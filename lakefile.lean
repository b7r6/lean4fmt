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
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_exe «lean4fmt» where
  root := `Lean4Fmt
