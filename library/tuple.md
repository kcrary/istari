open:Tuple
# `Tuple`

The Tuple library provides tuples of lengths up to 5.  (These are
slightly faster than iterated pairs.) It also provides a
pattern-matching elim form for each tuple, including pairs.

### Pairs

The pattern-matching elim for pairs is:

    letpair : type:letpair

    letpair (M1, M2) P --> P M1 M2

It has concrete syntax:

    let (x, y) = M in N   =def=   letpair M (fn x y . N)


### Triples

    datatype
      intersect (lv : level) .
      intermediate (a b c : U lv) .
      U lv
    of
      triple : type =
      | trip : a -> b -> c -> triple

    triple : type:triple
    trip   : type:trip

The pattern-matching elim for triples is:

    lettrip : type:lettrip

    lettrip (trip M1 M2 M3) P --> P M1 M2 M3

It has concrete syntax:

    let trip x y z = M in N   =def=   lettrip M (fn x y z . N)

Open-scope elims for triples are:

    trip1 : type:trip1

    trip2 : type:trip2

    trip3 : type:trip3

    trip1 (triple x y z) --> x
    trip2 (triple x y z) --> y
    trip3 (triple x y z) --> z


### Quadruples

    datatype
      intersect (lv : level) .
      intermediate (a b c d : U lv) .
      U lv
    of
      quadruple : type =
      | quad : a -> b -> c -> d -> quadruple

    quadruple : type:quadruple
    quad      : type:quad

The pattern-matching elim for quadruples is:

    letquad : type:letquad

    letquad (quad M1 M2 M3 M4) P -> P M1 M2 M3 M4

It has concrete syntax:

    let quad w x y z = M in N   =def=   letquad M (fn w x y z . N)

Open-scope elims for quadruples are:

    quad1 : type:quad1

    quad2 : type:quad2

    quad3 : type:quad3

    quad4 : type:quad4

    quad1 (quad w x y z) --> w
    quad2 (quad w x y z) --> x
    quad3 (quad w x y z) --> y
    quad4 (quad w x y z) --> z


### Quintuples

    datatype
      intersect (lv : level) .
      intermediate (a b c d e : U lv) .
      U lv
    of
      quintuple : type =
      | quint : a -> b -> c -> d -> e -> quintuple

    quintuple : type:quintuple
    quint     : type:quint

The pattern-matching elim for quintuples is:

    letquint : type:letquint

    letquint (quint M1 M2 M3 M4 M5) P -> P M1 M2 M3 M4 M5

It has concrete syntax:

    let quint v w x y z = M in N   =def=   letquint M (fn v w x y z . N)

Open-scope elims for quintuples are:

    quint1 : type:quint1

    quint2 : type:quint2

    quint3 : type:quint3

    quint4 : type:quint4

    quint5 : type:quint5

    quint1 (quint v w x y z) --> v
    quint2 (quint v w x y z) --> w
    quint3 (quint v w x y z) --> x
    quint4 (quint v w x y z) --> y
    quint5 (quint v w x y z) --> z
