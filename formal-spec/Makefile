# Constants
AGDA?=agda
AGDA_RUN=$(AGDA) --transliterate
OUT_DIR?=dist
HS_DIR=$(OUT_DIR)/haskell
MALONZO_DIR=MAlonzo/Code
CABAL_TEST=cabal run test

# Agda -> Haskell
define agdaToHs
    @echo "Generating $@"
    $(eval CABAL_FILE=marlowe-spec.cabal)
    $(eval HS_DIST=$(HS_DIR)/)
    mkdir -p $(HS_DIST)
    cp -r hs-src/* $(HS_DIST)/
    cp hs-src/$(CABAL_FILE) $(HS_DIST)/
    $(AGDA_RUN) -c --ghc-dont-call-ghc --compile-dir $(HS_DIST) $<
    find $(HS_DIST)/MAlonzo -name "*.hs" -print\
      | sed "s#^$(HS_DIST)/#        #;s#\.hs##;s#/#.#g"\
      >> $(HS_DIST)/$(CABAL_FILE)
endef
HS_MARLOWE=$(HS_DIR)/$(MALONZO_DIR)/Marlowe/Examples/Cardano.hs
$(HS_MARLOWE): Marlowe/Examples/Cardano.lagda.md
	$(call agdaToHs,marlowe-spec)

# Haskell -> HTML
define hsToHtml
	@echo "Generating $@"
	cd $$(dirname $@)\
	  && cabal haddock --haddock-hyperlink-source\
	  && find -type f -name 'index.html' -exec dirname {} \;\
	     | xargs -I{} mv {} html/
endef
$(HS_DIR)/$(LEDGER)/html/: # $(HS_MARLOWE)
	$(hsToHtml)
