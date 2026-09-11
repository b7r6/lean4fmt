# The book (Custody of Source), rendered by mdbook from doc/ + theme/.
_: {
  perSystem =
    { pkgs, ... }:
    let
      root = toString ../../.;
      source = pkgs.lib.cleanSourceWith {
        src = ../../.;
        filter =
          path: _type:
          let
            relative = pkgs.lib.removePrefix "${root}/" (toString path);
            top = builtins.head (pkgs.lib.splitString "/" relative);
          in
          relative == "" || top == "theme" || top == "doc" || relative == "book.toml";
      };
    in
    {
      packages.book = pkgs.stdenvNoCC.mkDerivation {
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
    };
}
