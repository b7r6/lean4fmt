# lean4fmt

A trustworthy, multi-style source formatter, linter, and project renamer for
Lean 4. Unsafe formatting candidates return the original source; the runtime
gate checks token, comment, syntax-spine, import, reparse, and fixed-point
preservation before output ships.

## Run

The directory is a standalone flake with its Lean toolchain and Nix inputs
pinned independently:

```sh
nix run . -- main.lean
nix run . -- --write lean_4_fmt.lean
nix develop
lake build
```

Install or consume it from another flake through the default package or app:

```nix
inputs.lean4fmt.url = "git+ssh://git@git.s4.gl/continuity/continuity.git?dir=src/lean4fmt";
```

```sh
nix build .
nix flake check
```

The architectural argument is [DESIGN_V2.md](./DESIGN_V2.md). The source map
is [ARCHITECTURE.md](./ARCHITECTURE.md), and the full Mathlib engineering ledger
is [CAMPAIGN.md](./CAMPAIGN.md).
