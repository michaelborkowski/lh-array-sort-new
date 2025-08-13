{ compiler ? "ghc910", pkgs ? import <nixpkgs> {}, ... }:
(pkgs.callPackage ./. { inherit pkgs; inherit compiler; }).shellFor {
       packages = p: [p.lh-array-sort p.benchrunner p.quest-plugin];
       buildInputs = [ pkgs.z3 pkgs.cabal-install ];
     }
