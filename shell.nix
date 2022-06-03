let
  pkgs = import (builtins.fetchGit {
                   name = "nixos-unstable-2021-03-11";
                   url = "https://github.com/nixos/nixpkgs/";
                   ref = "refs/heads/master";
                   # Commit hash for nixos-unstable as of 2021-03-11
                   rev = "a3228bb6e8bdbb9900f30a11fe09006fdabf7b71";
                 }) {};
  ghc = pkgs.haskell.compiler.ghc8102;
  ghc901 = pkgs.haskell.compiler.ghc901;
  stdenv = pkgs.overrideCC pkgs.stdenv pkgs.gcc7;
in
  with pkgs;
  stdenv.mkDerivation {
    name = "lh-array-sort";
    buildInputs = [ ghc ghc901 cabal-install stack ghcid z3
                    stdenv gcc gdb uthash ];
  }
