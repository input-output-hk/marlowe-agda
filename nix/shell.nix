{ repoRoot, inputs, pkgs, lib, system }:

cabalProject:

{
  name = "nix-shell";

  # prompt = null;

  # welcomeMessage = null;

  packages = [
    repoRoot.nix.agda2hs-project.hsPkgs.Agda.components.exes.agda 
    repoRoot.nix.agda2hs-project.hsPkgs.agda2hs.components.exes.agda2hs 

    (pkgs.emacsWithPackages (epkgs: [epkgs.agda2-mode]))
  ];

  # scripts = {};

  # env = {};

  # shellHook = "";

  tools = {
    # haskellCompilerVersion = cabalProject.args.compiler-nix-name;
    # cabal-fmt = null;
    # cabal-install = null;
    # haskell-language-server = null;
    # haskell-language-server-wrapper = null;
    # fourmolu = null;
    # hlint = null;
    # stylish-haskell = null;
    # ghcid = null;
    # shellcheck = null;
    # prettier = null;
    # editorconfig-checker = null;
    # nixpkgs-fmt = null;
    # optipng = null;
    # purs-tidy = null;
  };

  # preCommit = {
  #   cabal-fmt.enable = false;
  #   cabal-fmt.extraOptions = "";
  #   stylish-haskell.enable = false;
  #   stylish-haskell.extraOptions = "";
  #   fourmolu.enable = false;
  #   fourmolu.extraOptions = "";
  #   hlint.enable = false;
  #   hlint.extraOptions = "";
  #   shellcheck.enable = false;
  #   shellcheck.extraOptions = "";
  #   prettier.enable = false;
  #   prettier.extraOptions = "";
  #   editorconfig-checker.enable = false;
  #   editorconfig-checker.extraOptions = "";
  #   nixpkgs-fmt.enable = false;
  #   nixpkgs-fmt.extraOptions = "";
  #   optipng.enable = false;
  #   optipng.extraOptions = "";
  #   purs-tidy.enable = false;
  #   purs-tidy.extraOptions = "";
  # };
}
 