{
  description = "Binary rewriter for AArch64";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    picinae = {
      type = "github";
      owner = "CharlesAverill";
      repo = "Picinae";
      ref = "duneify";
      flake = false;
    };
    rocq-primitive = {
      type = "github";
      owner = "peregrine-project";
      repo = "rocq-primitive";
      ref = "9.0.0";
      flake = false;
    };
  };

  outputs = inputs @ {
    self,
    nixpkgs,
    ...
  }: let
    supportedSystems = ["x86_64-linux" "aarch64-linux"];
    forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
  in {
    packages = forAllSystems (
      system: let
        pkgs = import nixpkgs {inherit system;};
        coqPackages = pkgs.coqPackages_9_1;
        rocq = pkgs.rocqPackages_9_1.rocq-core;
        ocamlPackages = pkgs.ocamlPackages;
        rocq-picinae = ocamlPackages.buildDunePackage {
          pname = "picinae-rocq";
          version = "0.0.0";
          src = inputs.picinae;
          nativeBuildInputs = [rocq];
          buildInputs = [coqPackages.stdlib];
          postInstall = ''
            mkdir -p $out/lib/coq/${rocq.rocq-version}
            ln -s $out/lib/ocaml/*/site-lib/coq/user-contrib \
              $out/lib/coq/${rocq.rocq-version}/user-contrib
          '';
          env.OCAMLPATH = "${rocq}/lib";
        };
        rocq-primitive = ocamlPackages.buildDunePackage {
          pname = "rocq-primitive";
          version = "9.0.0";
          src = inputs.rocq-primitive;
        };
        a64-cc = let
          cc = pkgs.pkgsCross.aarch64-multiplatform.stdenv.cc;
        in
          pkgs.symlinkJoin {
            name = "a64-cc";
            paths = [cc];
            postBuild = ''
              mkdir -p $out/bin
              for file in ${cc}/bin/*; do
                filename=$(basename "$file")
                ln -sf "$file" "$out/bin/a64-''\${filename#aarch64-unknown-linux-gnu-}"
              done
            '';
          };
        kotori = ocamlPackages.buildDunePackage {
          pname = "kotori";
          version = "0.0.0";
          src = ./.;
          nativeBuildInputs = [rocq a64-cc];
          buildInputs =
            [pkgs.lief]
            ++ (with ocamlPackages; [
              rocq-primitive
              ctypes
              ctypes-foreign
              cmdliner
              ppx_deriving
              ppx_import
              parmap
              yojson
            ])
            ++ (with coqPackages; [
              stdlib
              stdpp
              rocq-picinae
              coq-record-update
              coqutil
            ]);
          passthru = {
            inherit ocamlPackages coqPackages rocq;
          };
          env.OCAMLPATH = "${rocq}/lib";
        };
      in {
        default = kotori;
      }
    );
    devShells = forAllSystems (
      system: let
        pkgs = import nixpkgs {inherit system;};
        kotori = self.packages.${system}.default;
      in {
        default = pkgs.mkShell {
          inputsFrom = [kotori];
          packages = [
            kotori.coqPackages.coq
            kotori.ocamlPackages.utop
            pkgs.perf
          ];
          env.OCAMLPATH = "${kotori.rocq}/lib";
        };
      }
    );
  };
}
