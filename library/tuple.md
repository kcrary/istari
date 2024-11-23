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
