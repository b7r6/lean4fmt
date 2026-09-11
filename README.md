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
nix run git+https://git.s4.gl/straylight/straylight-lean4fmt -- MyFile.lean
```

The default mode prints formatted source. `--check` changes no files and exits
nonzero off the fixed point; `--write` is the explicit mutation boundary. From
another flake:

```nix
inputs.lean4fmt.url = "git+https://git.s4.gl/straylight/straylight-lean4fmt.git";
```

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
