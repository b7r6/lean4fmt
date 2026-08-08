{
  description = "lean4fmt — trustworthy source transformation for Lean 4";

  inputs = {
    nixpkgs.url = "github:sensenet-ai/nixpkgs";
    systems.url = "github:nix-systems/default-linux";

    lean4-nix.url = "github:lenianiva/lean4-nix/1ac326fe8e88796156906b0ad8272364f01a7cdc";
    lean4-nix.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs =
    {
      self,
      nixpkgs,
      systems,
      lean4-nix,
    }:
    let
      eachSystem = nixpkgs.lib.genAttrs (import systems);
      packageFor =
        system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
          };
          lake2nix = pkgs.callPackage lean4-nix.lake { };
          root = toString ./.;
          source = nixpkgs.lib.cleanSourceWith {
            src = ./.;
            filter =
              path: _type:
              let
                relative = nixpkgs.lib.removePrefix "${root}/" (toString path);
                top = builtins.head (nixpkgs.lib.splitString "/" relative);
              in
              relative == ""
              || top == "lean_4_fmt"
              || builtins.elem relative [
                "lake-manifest.json"
                "lakefile.lean"
                "lean-toolchain"
                "lean_4_fmt.lean"
                "main.lean"
                "dag.py"
              ];
          };
        in
        lake2nix.mkPackage {
          name = "lean4fmt";
          src = source;
          lakeDeps = { };
          buildInputs = [
            pkgs.rsync
            pkgs.lean.lean-all
            pkgs.makeWrapper
            pkgs.python3
          ];
          installArtifacts = false;
          postInstall = ''
            mkdir -p $out/bin
            cp .lake/build/bin/lean4fmt $out/bin/
            cp dag.py $out/bin/lean4fmt-dag
            chmod +x $out/bin/lean4fmt-dag
            wrapProgram $out/bin/lean4fmt --prefix PATH : ${pkgs.lean.lean-all}/bin
            wrapProgram $out/bin/lean4fmt-dag --prefix PATH : ${pkgs.python3}/bin
          '';
          meta = {
            description = "Trustworthy, multi-style source formatter for Lean 4";
            homepage = "https://git.s4.gl/continuity/continuity";
            mainProgram = "lean4fmt";
            platforms = import systems;
          };
        };
      bookFor =
        system:
        let
          pkgs = import nixpkgs { inherit system; };
          root = toString ./.;
          source = nixpkgs.lib.cleanSourceWith {
            src = ./.;
            filter =
              path: _type:
              let
                relative = nixpkgs.lib.removePrefix "${root}/" (toString path);
                top = builtins.head (nixpkgs.lib.splitString "/" relative);
              in
              relative == ""
              || top == "theme"
              || relative == "Lean4Fmt"
              || relative == "Lean4Fmt/Solve"
              || relative == "Lean4Fmt/Solve/CAMPAIGN.md"
              || builtins.elem relative [
                "ARCHITECTURE.md"
                "CAMPAIGN.md"
                "DAG.md"
                "DESIGN.md"
                "DESIGN_V2.md"
                "DISTRIBUTED_GATE.md"
                "LINT.md"
                "README.md"
                "RENAME.md"
                "SUMMARY.md"
                "book.toml"
              ];
          };
        in
        pkgs.stdenvNoCC.mkDerivation {
          pname = "custody-of-source";
          version = "0-unstable";
          src = source;
          nativeBuildInputs = [ pkgs.mdbook ];
          buildPhase = ''
            runHook preBuild
            mdbook build
            runHook postBuild
          '';
          installPhase = ''
            runHook preInstall
            cp -r .book $out
            runHook postInstall
          '';
        };
    in
    {
      packages = eachSystem (system: {
        default = packageFor system;
        lean4fmt = packageFor system;
        book = bookFor system;
      });

      apps = eachSystem (system: {
        default = {
          type = "app";
          program = "${self.packages.${system}.default}/bin/lean4fmt";
          meta.description = "Format Lean 4 source";
        };
        lean4fmt = self.apps.${system}.default;
      });

      checks = eachSystem (system: {
        package = self.packages.${system}.default;
        book = self.packages.${system}.book;
      });

      devShells = eachSystem (
        system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
          };
        in
        {
          default = pkgs.mkShell {
            packages = [
              pkgs.lean.lean-all
              pkgs.mdbook
              pkgs.rsync
            ];
          };
        }
      );
    };
}
