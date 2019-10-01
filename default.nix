{ nixpkgs ? import <nixpkgs> {}, haskellPackages ? nixpkgs.haskellPackages, extra ? {}, drv ? {} }:
let
  path = ./.;
  name = builtins.baseNameOf path;
in
  with (nixpkgs.haskell.lib);
  with (nixpkgs.haskellPackages);
  overrideCabal
  (callCabal2nix name path
    (if builtins.isFunction extra then extra nixpkgs else extra))
  (drv0: (drv0 // {
    doCheck = true;
    doBenchmark = false;
    doHaddock = true;
    doCoverage = false;
    enableLibraryProfiling = false;
    enableExecutableProfiling = false;
  }) // drv)

