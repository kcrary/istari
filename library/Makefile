
ISTARIBIN=../ui/bin

DOCUNITS = girard-paradox smith-paradox
UNITS = $(DOCUNITS)
DOCS =


.PHONY : all
all : $(foreach i, $(UNITS), $(i).isto)

.PHONY : docs
docs : $(foreach i, $(DOCUNITS), ../docs/lib/$(i).md) $(foreach i, $(DOCS), ../docs/lib/$(i).md)

%.isto : %.ist %-aux.iml
	$(ISTARIBIN)/istari $<

../docs/lib/%.md : %.md
	$(ISTARIBIN)/procdoc $< $@

.PHONY : clean
clean :
	rm -f *.isto
