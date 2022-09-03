
ISTARI=../ui/bin/istari-nolib

all : acc.isto datatype.isto nat.isto 

acc.isto : acc.ist
	$(ISTARI) acc.ist

nat.isto : nat.ist nat-aux.iml acc.isto
	$(ISTARI) nat.ist

datatype.isto : datatype.ist datatype-aux.iml acc.isto nat.isto nat-aux.iml
	$(ISTARI) datatype.ist

clean :
	rm -f *.isto
