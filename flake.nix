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
          file = ./rust-toolchain.toml; # alternatively, dir = ./.;
<<<<<<< HEAD
          sha256 = "sha256-/F36bL5WoJ7opVs7o96dwVHE9SEt3am+6N3jPygJRKY=";

          };
=======
          sha256 = "sha256-riZUc+R9V35c/9e8KJUE+8pzpXyl0lRXt3ZkKlxoY0g=";
        };
>>>>>>> 30c8fd43e21b14b6cdcf7c5ea7613e43fbbfe456

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
            ocl-icd
            toolchain
          ];
        };
      }
    );
}
