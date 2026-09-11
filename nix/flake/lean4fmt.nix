# The formatter, built by lake2nix against the pinned toolchain (the repo-root
# `lean-toolchain`). The source filter admits exactly what the build consumes:
# the library tree, the barrel, the executable root, and the lake trio.
#
# lean4-nix's overlay replaces `pkgs.lean`; it lives on its OWN nixpkgs
# instance so nothing else inherits the substitution.
{ inputs, ... }: {
  perSystem =
    { system, ... }:
    let
      leanPkgs = import inputs.nixpkgs {
        inherit system;
        overlays = [ (inputs.lean4-nix.readToolchainFile ../../lean-toolchain) ];
      };
      lake2nix = leanPkgs.callPackage inputs.lean4-nix.lake { };
      root = toString ../../.;
      source = inputs.nixpkgs.lib.cleanSourceWith {
        src = ../../.;
        filter =
          path: _type:
          let
            relative = inputs.nixpkgs.lib.removePrefix "${root}/" (toString path);
            top = builtins.head (inputs.nixpkgs.lib.splitString "/" relative);
          in
          relative == ""
          || top == "lean_4_fmt"
          || builtins.elem relative [
            "lake-manifest.json"
            "lakefile.lean"
            "lean-toolchain"
            "lean_4_fmt.lean"
            "main.lean"
          ];
      };
      lean4fmt = lake2nix.mkPackage {
        name = "lean4fmt";
        src = source;
        lakeDeps = { };
        buildInputs = [
          leanPkgs.rsync
          leanPkgs.lean.lean-all
          leanPkgs.makeWrapper
        ];
        installArtifacts = false;
        postInstall = ''
          mkdir -p $out/bin
          cp .lake/build/bin/lean4fmt $out/bin/
          wrapProgram $out/bin/lean4fmt --prefix PATH : ${leanPkgs.lean.lean-all}/bin
        '';
        meta = {
          description = "Trustworthy, multi-style source formatter for Lean 4";
          homepage = "https://github.com/b7r6/lean4fmt";
          mainProgram = "lean4fmt";
          platforms = import inputs.systems;
        };
      };
    in
    {
      packages.default = lean4fmt;
      packages.lean4fmt = lean4fmt;

      apps.default = {
        type = "app";
        program = "${lean4fmt}/bin/lean4fmt";
        meta.description = "Format Lean 4 source";
      };

      # The pinned toolchain, for the devshell and downstream consumers.
      _module.args.leanLib = { inherit leanPkgs lake2nix; };
    };
}
