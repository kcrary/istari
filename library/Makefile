
ISTARI=../ui/bin/istari-nolib
PROCDOC=../ui/bin/procdoc

DOCUNITS = acc bar bool integer logic list nat nat-eff
UNITS = $(DOCUNITS) datatype

all : $(foreach i, $(UNITS), $(i).isto)

docs : $(foreach i, $(DOCUNITS), ../docs/lib/$(i).md)

%.isto : %.ist
	$(ISTARI) $<

../docs/lib/%.md : %.md
	$(PROCDOC) $< $@

bar.isto : bar-aux.iml
bool.isto : logic.isto
datatype.isto : datatype-aux.iml acc.isto nat.isto nat-aux.iml
integer.isto : nat-eff.isto
list.isto : list-aux.iml nat.isto nat-aux.iml datatype.isto
logic.isto : logic-aux.iml
nat.isto : nat-aux.iml acc.isto
nat-eff.isto : bool.isto logic.isto nat.isto

clean :
	rm -f *.isto
