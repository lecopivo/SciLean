{
  description = "SciLean development environment";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs =
    { self, nixpkgs, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in
    {
      devShells = forAllSystems (
        system:
        let
          pkgs = import nixpkgs { inherit system; };
        in
        {
          default = pkgs.mkShell {
            packages = with pkgs; [
              elan
              openblas
              gcc
              git
            ];

            shellHook = ''
              export OPENBLAS_PATH="${pkgs.openblas}"
              export LD_LIBRARY_PATH="${pkgs.openblas}/lib:$LD_LIBRARY_PATH"
              export LIBRARY_PATH="${pkgs.openblas}/lib:$LIBRARY_PATH"
              export CPATH="${pkgs.openblas.dev}/include:$CPATH"
            '';
          };
        }
      );
    };
}
