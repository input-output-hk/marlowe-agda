{ repoRoot, inputs, pkgs, lib, system }:

pkgs.emacs.pkgs.withPackages (epkgs: [
  epkgs.agda2-mode
])