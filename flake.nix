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
    let
      supportedSystems = [
        "aarch64-linux"
        "aarch64-darwin"
        "i686-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];
    in
    flake-utils.lib.eachSystem supportedSystems (system:
    let
      lib = utils.lib.${system};
      pkgs = nixpkgs.legacyPackages.${system};
      inherit (lib) buildRustProject testRustProject rustDefault filterRustProject;
      rust = rustDefault;
      crateName = "lurk";
      src = ./.;
      buildInputs = with pkgs;
        if !stdenv.isDarwin
        then [ ocl-icd ]
        else [
          darwin.apple_sdk.frameworks.OpenCL
        ];
      project = buildRustProject {
        root = ./.;
        inherit src buildInputs;
        copyLibs = true;
      };
      lurk-example = project.override {
        cargoBuildOptions = d: d ++ [ "--example lurk" ];
        copySources = [ "examples" "src" ];
        copyBins = true;
      };
      packages = {
        ${crateName} = project;
        inherit lurk-example;
      };
    in
    {
      inherit packages;
      checks = {
        ${crateName} = project.override { doCheck = true; };
      };

      defaultPackage = self.packages.${system}.${crateName};

      # To run with `nix run`
      apps.lurk-example = flake-utils.lib.mkApp {
        drv = lurk-example;
        name = "lurk";
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
