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

        # LTS 24.33 uses GHC 9.8.x
        # If your GHC version differs, adjust accordingly (e.g. ghc96, ghc910)
        hsPkgs = pkgs.haskell.packages.ghc98;
      in
      {
        devShells.default = hsPkgs.shellFor {
          packages = p: [];

          nativeBuildInputs = [
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
