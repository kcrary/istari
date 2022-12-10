
ISTARI=../ui/bin/istari-nolib
PROCDOC=../ui/bin/procdoc

DOCUNITS = acc bar bool decidable integer logic list nat stable
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
decidable.isto : logic.isto bool.isto
integer.isto : nat.isto acc.isto bool.isto decidable.isto stable.isto
list.isto : list-aux.iml nat.isto nat-aux.iml datatype.isto
logic.isto : logic-aux.iml
nat.isto : nat-aux.iml acc.isto bool.isto decidable.isto stable.isto
stable.isto : decidable.isto logic.isto

clean :
	rm -f *.isto
