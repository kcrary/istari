
ISTARIBIN=../ui/bin

DOCUNITS = acc bar bool decidable finite girard-paradox integer logic list nat option relations stable symbol wtype
UNITS = $(DOCUNITS) datatype omega

all : $(foreach i, $(UNITS), $(i).isto)

docs : $(foreach i, $(DOCUNITS), ../docs/lib/$(i).md)

%.isto : %.ist %-aux.iml
	$(ISTARIBIN)/istari-nolib $<

../docs/lib/%.md : %.md
	$(ISTARIBIN)/procdoc $< $@

.PHONY : tags
tags :
	$(ISTARIBIN)/istaritags $(foreach i, $(UNITS), $(i).ist)

DATATYPES = acc.isto nat.isto datatype.isto integer.isto

## In many of these, the dependency is on both x.isto and x-aux.iml, but since
## the former always depends on the latter, there's no need to include the latter
## dependency.

bool.isto : logic.isto
datatype.isto : acc.isto nat.isto
decidable.isto : logic.isto bool.isto
finite.isto : logic.isto decidable.isto list.isto
girard-paradox.isto : $(DATATYPES) logic.isto nat.isto
integer.isto : nat.isto acc.isto bool.isto decidable.isto stable.isto
list.isto : $(DATATYPES) nat.isto  option.isto integer.isto
nat.isto : acc.isto bool.isto decidable.isto stable.isto
omega.isto : logic.isto bool.isto nat.isto integer.isto list.isto
option.isto : $(DATATYPES) integer.isto
relations.isto : $(DATATYPES) acc.isto decidable.isto finite.isto
stable.isto : decidable.isto logic.isto
symbol.isto : logic.isto bool.isto
wtype.isto : acc.isto

clean :
	rm -f *.isto
