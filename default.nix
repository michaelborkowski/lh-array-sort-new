{ compiler ? "ghc910", pkgs ? import <nixpkgs> {}, ... }:
with pkgs;
    haskell.packages.${compiler}.extend (haskell.lib.packageSourceOverrides {
        lh-array-sort = ./.;
        benchrunner = ./benchrunner;
        quest-plugin = ./quest-plugin;
    })
