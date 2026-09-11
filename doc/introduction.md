# Custody of Source

lean4fmt is a source formatter, linter, and identity-aware project renamer for
Lean 4. This book explains why it exists, what it promises, how it works, and
where it refuses to act.

The central rule is simple:

> A formatter may improve the presentation of a program. It may never take
> custody of the program away from its author.

Lean makes that rule difficult to honor. Its grammar is extensible. Parsing and
elaboration cooperate. Whitespace can be syntax. Comments can change the lexical
meaning of the next token. Identifier spelling is not identifier identity. Any
tool that treats Lean as ordinary text will eventually damage a file that still
looks convincing in review.

lean4fmt treats formatting as a restricted compiler pass. It builds layout from
syntax, renders a candidate, reparses it, compares the protected structure, and
checks the fixed point. If that proof fails, the original bytes ship instead.
Unsupported syntax is not guessed at; it is preserved at a measured local
boundary.

That changes the engineering question. We no longer ask whether the formatter
is clever enough to print every construct. We ask whether each transformation
has earned the right to ship.

## Run the tool

The repository is an independently pinned Nix flake:

```sh
nix run . -- main.lean
nix run . -- --check lean_4_fmt.lean
nix run . -- --write lean_4_fmt.lean
```

The default mode prints formatted source. `--check` changes no files and exits
nonzero when the source is not at the selected fixed point. `--write` is the
explicit mutation boundary.

Consume the package or application from another flake:

```nix
inputs.lean4fmt.url = "github:b7r6/lean4fmt";
```

## Read this book

The book has four parts.

1. **The Contract** states the laws and the house style built on them.
2. **The Machine** maps those laws onto the frontend, document algebra,
   renderer, emitter, linter, and runtime gate.
3. **Whole-Tree Change** explains renaming, dependency order, and distributed
   validation.
4. **Evidence** records the complete Mathlib campaign, including failed
   hypotheses and the measured boundary of the result.

Start with [the design](design.md). Read [the architecture](architecture.md)
when changing code. Use [the campaign](campaign.md) when challenging a claim or
planning the next clearance.

## What the numbers mean

The standing full-tree Mathlib census parses 8,245 files with zero missing
statistics and zero unclassified safety-gate rejects. The formatter actively
ships 91.9% of the portable surface. The remaining 113 exact-path identity
clearances return the original file and count as zero active coverage.

Those numbers are not a claim of universal formatting. They are a precise
statement about what the tool will and will not currently take responsibility
for.

The tree is self-hosting: every `.lean` file in this repository is at the
fixed point of the binary built from it, under the `straylight` preset.

The source is the authority. The book states the reasons. The gates decide what
may ship.
