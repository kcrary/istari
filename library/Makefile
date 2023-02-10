
ISTARI=../ui/bin/istari-nolib
PROCDOC=../ui/bin/procdoc

DOCUNITS = acc bar bool decidable integer logic list nat relations stable
UNITS = $(DOCUNITS) datatype omega

all : $(foreach i, $(UNITS), $(i).isto)

docs : $(foreach i, $(DOCUNITS), ../docs/lib/$(i).md)

%.isto : %.ist %-aux.iml
	$(ISTARI) $<

../docs/lib/%.md : %.md
	$(PROCDOC) $< $@

bool.isto : logic.isto logic-aux.iml
datatype.isto : acc.isto acc-aux.iml nat.isto nat-aux.iml
decidable.isto : logic.isto logic-aux.iml bool.isto bool-aux.iml
integer.isto : nat.isto nat-aux.iml acc.isto acc-aux.iml bool.isto bool-aux.iml decidable.isto decidable-aux.iml stable.isto stable-aux.iml
list.isto : nat.isto nat-aux.iml datatype.isto
nat.isto : acc.isto acc-aux.iml bool.isto bool-aux.iml decidable.isto decidable-aux.iml stable.isto stable-aux.iml
omega.isto : logic.isto logic-aux.iml bool.isto bool-aux.iml nat.isto nat-aux.iml integer.isto integer-aux.iml list.isto list-aux.iml
relations.isto : acc.isto acc-aux.iml
stable.isto : decidable.isto decidable-aux.iml logic.isto logic-aux.iml

clean :
	rm -f *.isto
