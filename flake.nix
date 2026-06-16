{
  description = "mcc - A microc compiler in Haskell";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        hsPkgs = pkgs.haskell.packages.ghc910;
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            # Haskell tooling
            hsPkgs.haskell-language-server
            hsPkgs.ghc
            pkgs.stack
            pkgs.cabal-install

            # Build tools referenced in package.yaml
            hsPkgs.alex
            hsPkgs.happy

            # Common native dependencies
            pkgs.pkg-config
            pkgs.zlib
          ];

          shellHook = ''
            echo "mcc dev shell — GHC $(ghc --version | awk '{print $NF}'), HLS available"
          '';
        };
      }
    );
}
