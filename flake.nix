{
  description = "Lurk (rust)";
  inputs = {
    nixpkgs.url = github:nixos/nixpkgs/nixos-21.05;
    flake-utils = {
      url = github:numtide/flake-utils;
      inputs.nixpkgs.follows = "nixpkgs";
    };
    naersk = {
      url = github:yatima-inc/naersk;
      inputs.nixpkgs.follows = "nixpkgs";
    };
    utils = {
      url = github:yatima-inc/nix-utils;
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.naersk.follows = "naersk";
    };
  };

  outputs =
    { self
    , nixpkgs
    , flake-utils
    , utils
    , naersk
    }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      lib = utils.lib.${system};
      pkgs = nixpkgs.legacyPackages.${system};
      inherit (lib) buildRustProject testRustProject rustDefault filterRustProject;
      rust = rustDefault;
      crateName = "lurk";
      src = ./.;
      buildInputs = with pkgs; [ opencl-clhpp opencl-clang mesa ];
      project = buildRustProject {
        inherit src buildInputs;
        copyLibs = true;
      };
      lurk-example = project.override {
        cargoBuildOptions = d: d ++ [ "--example lurk" "--no-default-features" ];
        copyBins = true;
      };
    in
    {
      packages = {
        ${crateName} = project;
        inherit lurk-example;
      };
      checks.${crateName} = project.override { doCheck = true; };

      defaultPackage = self.packages.${system}.${crateName};

      # To run with `nix run`
      apps.lurk-example = flake-utils.lib.mkApp {
        drv = lurk-example;
      };

      defaultApp = self.apps.${system}.lurk-example;

      # `nix develop`
      devShell = pkgs.mkShell {
        inputsFrom = builtins.attrValues self.packages.${system};
        nativeBuildInputs = [ rust ];
        buildInputs = with pkgs; buildInputs ++ [
          rust-analyzer
          clippy
          rustfmt
        ];
      };
    });
}
