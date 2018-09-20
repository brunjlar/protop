INCLUDE_DIR = $(TOP_DIR)/includes
OUTPUT_DIR = ./output

%.ghci : %.lhs $(INCLUDE_DIR)/*
	ghci -pgmL "lhs2TeX" -optL-P$(INCLUDE_DIR): -optL--pre $<

%.ghcid : %.lhs $(INCLUDE_DIR)/*
	ghcid -c "ghci -pgmL "lhs2TeX" -optL-P$(INCLUDE_DIR): -optL--pre" $<

%.tex : %.lhs $(INCLUDE_DIR)/*
	lhs2TeX -P$(INCLUDE_DIR): --poly -o $@ $<

%.hs : %.lhs $(INCLUDE_DIR)/*
	lhs2TeX -P$(INCLUDE_DIR): --newcode -o $@ $<

%.pdf : %.tex force
	TEXINPUTS=$(INCLUDE_DIR): latexmk $(LATEXMK_FLAGS) -xelatex -output-directory=$(OUTPUT_DIR) $<
	ln -sf $(OUTPUT_DIR)/$@ .

default : $(notdir $(CURDIR)).pdf

ghci : $(notdir $(CURDIR)).ghci

ghcid : $(notdir $(CURDIR)).ghcid

.PHONY : force default ghci ghcid
