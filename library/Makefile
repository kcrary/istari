
ISTARI=../ui/bin/istari-nolib

all : acc.isto bar.isto bool.isto datatype.isto list.isto logic.isto nat.isto nat-eff.isto

acc.isto : acc.ist
	$(ISTARI) acc.ist

bar.isto : bar.ist bar-aux.iml
	$(ISTARI) bar.ist

bool.isto : bool.ist logic.isto
	$(ISTARI) bool.ist

datatype.isto : datatype.ist datatype-aux.iml acc.isto nat.isto nat-aux.iml
	$(ISTARI) datatype.ist

list.isto : list.ist list-aux.iml acc.isto nat.isto nat-aux.iml datatype.isto
	$(ISTARI) list.ist

logic.isto : logic.ist logic-aux.iml
	$(ISTARI) logic.ist

nat.isto : nat.ist nat-aux.iml acc.isto
	$(ISTARI) nat.ist

nat-eff.isto : nat-eff.ist acc.isto bool.isto nat.isto
	$(ISTARI) nat-eff.ist

clean :
	rm -f *.isto
