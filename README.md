> `type Intelligence = AI | Human`

# lean4fmt

A trustworthy source formatter, linter, and identity-aware renamer for Lean 4.

> A formatter may improve the presentation of a program. It may never take
> custody of the program away from its author.

lean4fmt treats formatting as a restricted compiler pass: it builds layout from
syntax, renders a candidate, reparses it, compares the protected structure, and
checks the fixed point. If that proof fails, the original bytes ship instead.
The failure mode is "unformatted", never "damaged".

## Use it

```sh
nix run github:b7r6/lean4fmt -- MyFile.lean
```

The default mode prints formatted source. `--check` changes no files and exits
nonzero off the fixed point; `--write` is the explicit mutation boundary. From
another flake:

```nix
inputs.lean4fmt.url = "github:b7r6/lean4fmt";
```

## Provenance

lean4fmt was designed, directed, and reviewed by b7r6. The bulk of the
implementation was written by AI — OpenAI Codex and Anthropic's Claude —
under that direction, gate by gate. Disclosure is stated here once, in full,
because it is owed; it is not repeated throughout the tree.

The tool itself is built for exactly this question. It asks for no trust in
its authors, human or machine: every formatted file is verified by reparse,
protected-structure comparison, and a fixed-point check, and when that proof
fails the original bytes ship unchanged. The gates decide what may ship —
the evidence record in the book is theirs, not ours.

## Read the book

The design, the house style, the machine, and the complete Mathlib evidence
record live in one book, *Custody of Source*:

```sh
nix build .#book && xdg-open result/index.html
```

or `mdbook serve doc` from a checkout. Start with
[the introduction](doc/introduction.md).

Every `.lean` file in this repository is at the fixed point of the binary built
from it.
