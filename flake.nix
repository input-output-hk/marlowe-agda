{
  description = "marlowe-spec";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs { inherit system; };
          lib = pkgs.stdEnv.lib;
          localEmacs = (pkgs.emacs.pkgs.withPackages (epkgs: (with epkgs.melpaStablePackages; [
            epkgs.agda2-mode
          ])));
          locales = {
            LANG = "en_US.UTF-8";
            LC_ALL = "en_US.UTF-8";
            LOCALE_ARCHIVE = if pkgs.system == "x86_64-linux"
                             then "${pkgs.glibcLocales}/lib/locale/locale-archive"
                             else "";
            };

          agdaStdlib = pkgs.agdaPackages.standard-library;

          agdaStdlibClasses = pkgs.agdaPackages.mkDerivation {
            inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
            pname = "agda-stdlib-classes";
            version = "2.0";
            src = pkgs.fetchFromGitHub {
              repo = "agda-stdlib-classes";
              owner = "omelkonian";
              rev = "2b42a6043296b4601134b8ab9371b37bda5d4424";
              sha256 = "sha256-kTqS9p+jjv34d4JIWV9eWAI8cw9frX/K9DHuwv56AHo=";
            };
            meta = { };
            libraryFile = "agda-stdlib-classes.agda-lib";
            everythingFile = "standard-library-classes.agda";
            buildInputs = [ agdaStdlib ];
          };

          agdaStdlibMeta = pkgs.agdaPackages.mkDerivation {
            inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
            pname = "agda-stdlib-meta";
            version = "2.1.1";
            src = pkgs.fetchFromGitHub {
              repo = "stdlib-meta";
              owner = "omelkonian";
              rev = "480242a38feb948cafc8bcf673d057c04b0ed347";
              sha256 = "pa6Zd9O3M1d/JMSvnfgteAbDMgHyelQrR5xyibU0EeM=";
            };
            meta = { };
            libraryFile = "agda-stdlib-meta.agda-lib";
            everythingFile = "standard-library-meta.agda";
            buildInputs = [ agdaStdlib agdaStdlibClasses ];
          };

          agdaIOGPrelude = pkgs.agdaPackages.mkDerivation {
            inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
            pname = "agda-prelude";
            version = "2.0";
            src = pkgs.fetchFromGitHub {
              repo = "iog-agda-prelude";
              owner = "input-output-hk";
              rev = "ee289f9a0b2ec0a3bfc43c3f678a17c174b397e6";
              sha256 = "sha256-noLUBl9d/vDNbAzWfnBrWoATlBrVG1DwzRV7/2uRHoE=";
            };
            meta = { };
            libraryFile = "iog-prelude.agda-lib";
            everythingFile = "src/Everything.agda";
            buildInputs = [ agdaStdlib agdaStdlibClasses ];
          };

          deps = [ agdaStdlib agdaStdlibClasses agdaStdlibMeta agdaIOGPrelude ];

          marloweSpec = pkgs.agdaPackages.mkDerivation {
            inherit (locales) LANG LC_ALL LOCALE_ARCHIVE;
            pname = "marlowe-spec";
            name = "marlowe-spec";
            src = ./formal-spec;
            meta = { };
            libraryFile = "formal-spec/marlowe-spec.agda-lib";
            everythingFile = "Everything.agda";
            buildInputs = deps;
          };

          agdaWithPkgs = p: pkgs.agda.withPackages { pkgs = p; ghc = pkgs.ghc; };
          agdaWithDeps = agdaWithPkgs deps;
        in
        {
          packages.default = marloweSpec;
          defaultPackage = marloweSpec;
          devShell = pkgs.mkShell {
            buildInputs = [
              pkgs.nixpkgs-fmt
              pkgs.mononoki
              localEmacs
              agdaWithDeps
            ];
          };
        }
      );

  nixConfig = {
    bash-prompt = "\\n\\[\\033[1;32m\\][marlowe-spec:\\w]\\$\\[\\033[0m\\] ";
  };
}
