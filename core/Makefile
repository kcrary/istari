
ISTARIBIN=../ui/bin

DOCUNITS = acc bool decidable eventually finite finite-map function integer irrelevance kindlike logic list misc nat natural option partial permutation quotient rational relations sqstable stable symbol tuple weaksum wtype
UNITS = $(DOCUNITS) datatype syntactic-equality omega
DOCS = finite-map-class


.PHONY : all
all : $(foreach i, $(UNITS), $(i).isto)

.PHONY : docs
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
datatype.isto : acc.isto misc.isto nat.isto partial.isto     integer.isto

acc.isto : partial.isto
bool.isto : logic.isto
decidable.isto : logic.isto bool.isto
eventually.isto : logic.isto misc.isto sqstable.isto
finite.isto : logic.isto decidable.isto list.isto
finite-map.isto : bool.isto decidable.isto function.isto kindlike.isto list.isto logic.isto option.isto permutation.isto
function.isto : logic.isto
integer.isto : acc.isto bool.isto decidable.isto nat.isto partial.isto stable.isto
irrelevance.isto : function.isto misc.isto
kindlike.isto : eventually.isto function.isto misc.isto
list.isto : bool.isto datatype.isto decidable.isto function.ist kindlike.ist logic.isto misc.isto nat.isto option.isto partial.isto
misc.isto :
nat.isto : acc.isto bool.isto decidable.isto partial.isto stable.isto
natural.isto : bool.isto integer.isto nat.isto logic.isto
omega.isto : datatype.isto logic.isto bool.isto nat.isto integer.isto list.isto misc.isto natural.isto
option.isto : datatype.isto function.isto kindlike.isto integer.isto
partial.isto : logic.isto
permutation.isto : list.isto logic.isto misc.isto nat.isto
quotient.isto : logic.isto
rational.isto : bool.isto decidable.isto integer.isto logic.isto partial.isto quotient.isto stable.ist
relations.isto : datatype.isto acc.isto decidable.isto finite.isto
sqstable.isto : decidable.isto logic.isto stable.isto syntactic-equality.isto
stable.isto : decidable.isto logic.isto
symbol.isto : bool.isto logic.isto partial.isto
syntactic-equality.isto : nat.isto integer.isto natural.isto symbol.isto
tuple.isto : datatype.isto misc.isto
weaksum.isto : eventually.isto kindlike.isto logic.isto misc.isto
wtype.isto : acc.isto

.PHONY : clean
clean :
	rm -f *.isto
