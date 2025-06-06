{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages."${system}";
        agda = pkgs.agda.withPackages (
          pkgs: with pkgs; [
            cubical
          ]
        );
      in
      {
        devShell = pkgs.mkShell {
          packages = [ agda ];
        };
      }
    );
}
