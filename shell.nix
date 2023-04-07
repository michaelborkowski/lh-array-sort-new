let
  pkgs = import (builtins.fetchGit {
                   name = "nixos-git";
                   url = "https://github.com/nixos/nixpkgs/";
                   ref = "refs/heads/master";
                   # Commit hash for nixos-unstable as of 2021-12-01
                   # # rev = "8b01281b66cba818abea8dbbdb3614b1b38961e3";
                   rev = "c610be58c0b6484c18728dc3ed60310cdbfbd456";
                 }) {};
  ghc = pkgs.haskell.compiler.ghc8107;
  ghc901 = pkgs.haskell.compiler.ghc901;
  stdenv = pkgs.overrideCC pkgs.stdenv pkgs.gcc7;
  gcc = pkgs.gcc7;
in
  with pkgs;
  stdenv.mkDerivation {
    name = "lh-array-sort";
    buildInputs = [ ghc ghc901 cabal-install stack ghcid z3 numactl
                    stdenv gcc gdb uthash ];
  }
