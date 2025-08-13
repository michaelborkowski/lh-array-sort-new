{ compiler ? "ghc910", pkgs ? import <nixpkgs> {}, ... }: # don't pint nixpkgs for now as this is a trivial shell file
pkgs.mkShell {
  name = "haskell-shell";
  buildInputs = [
    pkgs.haskell.compiler.${compiler}
    pkgs.haskellPackages.cabal-install # have to use default cabal instead of ${compiler}'s one to hit nix cache
    pkgs.z3
    ];
}
