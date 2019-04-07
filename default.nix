{ 
  ghc ? "ghc863", 
  nixpkgs ? import <nixpkgs> {} 
}:
nixpkgs.haskell.packages.${ghc}.callCabal2nix "aeson-flowtyped" ./. {}

