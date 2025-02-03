
ISTARIBIN=../ui/bin

DOCUNITS = acc bar bool decidable finite finite-map function integer kindlike logic list miscellaneous nat natural option partial permutation relations stable symbol tuple union wtype
UNITS = $(DOCUNITS) datatype syntactic-equality omega
DOCS = finite-map-class


all : $(foreach i, $(UNITS), $(i).isto)

docs : $(foreach i, $(DOCUNITS), ../docs/lib/$(i).md) $(foreach i, $(DOCS), ../docs/lib/$(i).md)

%.isto : %.ist %-aux.iml
	$(ISTARIBIN)/istari-nolib $<

../docs/lib/%.md : %.md
	$(ISTARIBIN)/procdoc $< $@

.PHONY : tags
tags :
	$(ISTARIBIN)/istaritags $(foreach i, $(UNITS), $(i).ist)

## In many of these, the dependency is on both x.isto and x-aux.iml, but since
## the former always depends on the latter, there's no need to include the latter
## dependency.

## everything Istari's datatype implementation needs, including stuff datatype.ist doesn't
datatype.isto : acc.isto miscellaneous.isto nat.isto partial.isto     integer.isto

bool.isto : logic.isto
decidable.isto : logic.isto bool.isto
finite.isto : logic.isto decidable.isto list.isto
finite-map.isto : bool.isto decidable.isto function.isto kindlike.isto list.isto logic.isto option.isto
integer.isto : acc.isto bool.isto decidable.isto nat.isto partial.isto stable.isto
kindlike.isto : bar.isto function.isto
list.isto : bool.isto datatype.isto decidable.isto function.ist kindlike.ist logic.isto miscellaneous.isto nat.isto option.isto partial.isto
nat.isto : acc.isto bool.isto decidable.isto stable.isto
natural.isto : bool.isto integer.isto nat.isto logic.isto
omega.isto : datatype.isto logic.isto bool.isto nat.isto integer.isto list.isto natural.isto
option.isto : datatype.isto function.isto kindlike.isto integer.isto
permutation.isto : list.isto logic.isto nat.isto
relations.isto : datatype.isto acc.isto decidable.isto finite.isto
stable.isto : decidable.isto logic.isto
symbol.isto : bool.isto logic.isto partial.isto
syntactic-equality.isto : nat.isto integer.isto natural.isto symbol.isto
tuple.isto : datatype.isto miscellaneous.isto
union.isto : logic.isto
wtype.isto : acc.isto

clean :
	rm -f *.isto
