{
  description = "Extended FS flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-23.05";
    flake-utils.url = "github:numtide/flake-utils/v1.0.0";
    rust-overlay.url = "github:oxalica/rust-overlay";
    crane = {
      url = "github:ipetkov/crane";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.rust-overlay.follows = "rust-overlay";
    };
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
    rust-overlay,
    crane,
  }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system: let
      overlays = [ rust-overlay.overlays.default ];
      pkgs = import nixpkgs { inherit system overlays; };

      rust = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;

      craneLib = crane.lib.${system}.overrideToolchain rust;
      
      commonArgs = {
        src = craneLib.cleanCargoSource self;
      };

      cargoArtifacts = craneLib.buildDepsOnly commonArgs;

    in rec {
      formatter = pkgs.alejandra;

      devShells.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          rust
          cargo
          cargo-deny
          clippy
          rustfmt
          alejandra
        ];
      };

      packages.efs = craneLib.buildPackage (commonArgs // {
        inherit cargoArtifacts;
      });

      checks.efs = packages.efs;

      checks.efs-clippy = craneLib.cargoClippy (commonArgs // {
        inherit cargoArtifacts;
      });

      checks.nix-formatter = pkgs.stdenv.mkDerivation rec {
        name = "nix-fmt-check";
        nativeCheckInputs = [ pkgs.alejandra ];
        phases = [ "checkPhase" ];
        checkPhase = ''
          alejandra -c .
          echo 1 > $out
        '';
        src = ./.;
        doCheck = true;
      };
    });
}
