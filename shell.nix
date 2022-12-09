let
  pkgs = import (builtins.fetchGit {
                   name = "nixos-unstable-2021-03-11";
                   url = "https://github.com/nixos/nixpkgs/";
                   ref = "refs/heads/master";
                   # Commit hash for nixos-unstable as of 2022-01-30
                   rev = "8b01281b66cba818abea8dbbdb3614b1b38961e3";
                 }) {};
  ghc = pkgs.haskell.compiler.ghc8107;
  # ghc901 = pkgs.haskell.compiler.ghc901;
  stdenv = pkgs.overrideCC pkgs.stdenv pkgs.gcc11;
in
  with pkgs;
  stdenv.mkDerivation {
    name = "lh-array-sort";
    buildInputs = [ ghc cabal-install stack ghcid z3
                    stdenv gcc gdb uthash ];
  }
