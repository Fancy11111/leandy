{
  description = "tests of lean";
  inputs = { utils.url = "github:numtide/flake-utils"; };
  outputs = { self, nixpkgs, utils }:
    utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
      in {
        devShell = pkgs.mkShell {
          name = "lean";
          buildInputs = with pkgs; [ elan nixd gitlab-ci-local ] ;
        };
        formatter = pkgs.nixfmt;
      });
}
