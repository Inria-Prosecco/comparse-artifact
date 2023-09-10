{
  inputs = {
    fstar-flake.url = "github:FStarLang/FStar";
    nixpkgs.follows = "fstar-flake/nixpkgs";
  };

  outputs = {self, nixpkgs, fstar-flake}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    z3 = fstar-flake.packages.${system}.z3;
    fstar = fstar-flake.packages.${system}.fstar;
    fstar-dune = fstar-flake.packages.${system}.fstar-dune;
    comparse = pkgs.callPackage ./default.nix {inherit fstar z3 fstar-dune; ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;};
  in {
    devShells.${system}.default = pkgs.mkShell {
      packages = [
        fstar z3
      ] ++ (with pkgs.ocaml-ng.ocamlPackages_4_14; [
        ocaml dune_3 findlib yojson
      ])
      ++ (fstar.buildInputs)
      ++ (fstar-dune.buildInputs);
    };
  };
}
