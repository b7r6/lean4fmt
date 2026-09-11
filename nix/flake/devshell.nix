# Development shell: the pinned lean/lake toolchain and the book tooling.
# Kept deliberately close to what CI (`nix flake check`) uses.
_: {
  perSystem = { pkgs, leanLib, ... }: {
    devShells.default = pkgs.mkShell {
      packages = [
        leanLib.leanPkgs.lean.lean-all
        pkgs.mdbook
        pkgs.rsync
      ];
    };
  };
}
