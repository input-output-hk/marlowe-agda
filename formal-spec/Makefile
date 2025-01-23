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
    $(eval HS_DIST=$(HS_DIR)/src)
    mkdir -p $(HS_DIST)
    cp -r hs-src/* $(HS_DIR)/
    cp hs-src/$(CABAL_FILE) $(HS_DIR)/
    $(AGDA_RUN) -c --ghc-dont-call-ghc --compile-dir $(HS_DIST) $<
    find $(HS_DIST)/MAlonzo -name "*.hs" -print\
      | sed "s#^$(HS_DIST)/#        #;s#\.hs##;s#/#.#g"\
      >> $(HS_DIR)/$(CABAL_FILE)
endef
HS_MARLOWE=$(HS_DIST)/$(MALONZO_DIR)/Everything.hs
$(HS_MARLOWE): Everything.agda
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
