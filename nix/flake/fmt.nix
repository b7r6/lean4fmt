# treefmt for everything that is not Lean; the Lean tree is lean4fmt's own
# fixed point and stays out of scope here.
{ inputs, ... }: {
  imports = [ inputs.treefmt-nix.flakeModule ];
  perSystem = _: {
    treefmt = {
      # `deadnix`: dead code elimination for `nixlang`
      programs.deadnix.enable = true;

      # `nixfmt`: nixlang formatter
      programs.nixfmt.enable = true;
      programs.nixfmt.strict = true;
      programs.nixfmt.width = 100;

      # `statix`: static analysis for `nixlang`
      programs.statix.enable = true;
    };
  };
}
