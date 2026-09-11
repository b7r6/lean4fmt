# CI gates for `nix flake check`. treefmt-nix (see fmt.nix) contributes the
# `formatting` check automatically; the package and the book are the rest.
_: {
  perSystem = { self', ... }: {
    checks.package = self'.packages.default;
    checks.book = self'.packages.book;
  };
}
