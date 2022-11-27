{ pkgs ? import <nixpkgs> { } }:
with pkgs;
mkShell {
  buildInputs = [
    (agda.withPackages (ps: [
      ps.standard-library
    ]))
    (emacs.pkgs.withPackages (epkgs: (with epkgs.melpaStablePackages; [
      epkgs.agda2-mode
    ])))
  ];
}
