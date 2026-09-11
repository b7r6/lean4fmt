{
  description = "// straylight // lean4fmt";

  outputs =
    inputs:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } {
      systems = import inputs.systems;
      imports = [ ./nix/flake ];
    };

  inputs = {
    nixpkgs.url = "github:sensenet-ai/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    systems.url = "github:nix-systems/default-linux";

    treefmt-nix.url = "github:numtide/treefmt-nix";
    treefmt-nix.inputs.nixpkgs.follows = "nixpkgs";

    # Lean 4 + lake via Nix: provides the lean/lake toolchain and `lake2nix`
    # (buildDeps/mkPackage) to build the formatter as a Nix derivation.
    # Pinned to manifest/v4.31.0 (PR #127); re-pin to main once it merges.
    lean4-nix.url = "github:lenianiva/lean4-nix/1ac326fe8e88796156906b0ad8272364f01a7cdc";
    lean4-nix.inputs.nixpkgs.follows = "nixpkgs";
  };
}
