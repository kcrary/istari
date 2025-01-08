# `Tuple`

The Tuple library provides tuples of lengths up to 5.  (These are
slightly faster than iterated pairs.) It also provides a
pattern-matching elim form for each tuple, including pairs.

### Pairs

The pattern-matching elim for pairs is:

    letpair : intersect (i : level) (a b c : U i) . a & b -> (a -> b -> c) -> c

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

    triple : intersect (lv : level) . forall (a b c : U lv) . U lv
    trip   : intersect (lv : level) (a b c : U lv) . a -> b -> c -> triple a b c

The pattern-matching elim for triples is:

    lettrip : intersect (i : level) (a b c d : U i) . triple a b c -> (a -> b -> c -> d) -> d

    lettrip (trip M1 M2 M3) P --> P M1 M2 M3

It has concrete syntax:

    let trip x y z = M in N   =def=   lettrip M (fn x y z . N)

Open-scope elims for triples are:

    trip1 : intersect (i : level) (a b c : U i) . triple a b c -> a

    trip2 : intersect (i : level) (a b c : U i) . triple a b c -> b

    trip3 : intersect (i : level) (a b c : U i) . triple a b c -> c

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

    quadruple : intersect (lv : level) . forall (a b c d : U lv) . U lv
    quad      : intersect (lv : level) (a b c d : U lv) . a -> b -> c -> d -> quadruple a b c d

The pattern-matching elim for quadruples is:

    letquad : intersect (i : level) (a b c d e : U i) .
                 quadruple a b c d -> (a -> b -> c -> d -> e) -> e

    letquad (quad M1 M2 M3 M4) P -> P M1 M2 M3 M4

It has concrete syntax:

    let quad w x y z = M in N   =def=   letquad M (fn w x y z . N)

Open-scope elims for quadruples are:

    quad1 : intersect (i : level) (a b c d : U i) . quadruple a b c d -> a

    quad2 : intersect (i : level) (a b c d : U i) . quadruple a b c d -> b

    quad3 : intersect (i : level) (a b c d : U i) . quadruple a b c d -> c

    quad4 : intersect (i : level) (a b c d : U i) . quadruple a b c d -> d

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

    quintuple : intersect (lv : level) . forall (a b c d e : U lv) . U lv
    quint     : intersect (lv : level) (a b c d e : U lv) .
                   a -> b -> c -> d -> e -> quintuple a b c d e

The pattern-matching elim for quintuples is:

    letquint : intersect (i : level) (a b c d e f : U i) .
                  quintuple a b c d e -> (a -> b -> c -> d -> e -> f) -> f

    letquint (quint M1 M2 M3 M4 M5) P -> P M1 M2 M3 M4 M5

It has concrete syntax:

    let quint v w x y z = M in N   =def=   letquint M (fn v w x y z . N)

Open-scope elims for quintuples are:

    quint1 : intersect (i : level) (a b c d e : U i) . quintuple a b c d e -> a

    quint2 : intersect (i : level) (a b c d e : U i) . quintuple a b c d e -> b

    quint3 : intersect (i : level) (a b c d e : U i) . quintuple a b c d e -> c

    quint4 : intersect (i : level) (a b c d e : U i) . quintuple a b c d e -> d

    quint5 : intersect (i : level) (a b c d e : U i) . quintuple a b c d e -> e

    quint1 (quint v w x y z) --> v
    quint2 (quint v w x y z) --> w
    quint3 (quint v w x y z) --> x
    quint4 (quint v w x y z) --> y
    quint5 (quint v w x y z) --> z
