{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    naersk = {
      url = "github:nix-community/naersk";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, naersk, fenix }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = (import nixpkgs) {
          inherit system;
        };

        toolchain = with fenix.packages.${system}; fromToolchainFile {
          file = ./rust-toolchain; # alternatively, dir = ./.;
          sha256 = "sha256-rLP8+fTxnPHoR96ZJiCa/5Ans1OojI7MLsmSqR2ip8o=";
        };

      in rec {
        defaultPackage = (naersk.lib.${system}.override {
          # For `nix build` & `nix run`:
          cargo = toolchain;
          rustc = toolchain;
        }).buildPackage {
          src = ./.;
        };

        # For `nix develop` or `direnv allow`:
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            pkg-config
            openssl
            ocl-icd
            toolchain
            rust-analyzer
            clang
          ];
        };
      }
    );
}
