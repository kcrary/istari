
ISTARIBIN=../ui/bin

DOCUNITS = girard-paradox smith-paradox
UNITS = $(DOCUNITS)
DOCS =


all : $(foreach i, $(UNITS), $(i).isto)

docs : $(foreach i, $(DOCUNITS), ../docs/lib/$(i).md) $(foreach i, $(DOCS), ../docs/lib/$(i).md)

%.isto : %.ist %-aux.iml
	$(ISTARIBIN)/istari $<

../docs/lib/%.md : %.md
	$(ISTARIBIN)/procdoc $< $@

clean :
	rm -f *.isto
