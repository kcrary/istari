open:Wtype
# `Wtype`

Martin-L&ouml;f's well-founded (or "W") types are a solution to the equation:

    wtype (x : A) . B(x)  ==  exists (x : A) . B(x) -> wtype (x' : A) . B(x')

Martin-L&ouml;f (1984) intended them as constructive ordinals, but
they can also be used to implement a variety of data structures.  (In
Istari, datatypes usually provide a more convenient mechanism with
better canonicity properties.)

    wtype : type:wtype
          = def:wtype

    wtype_unroll : type:wtype_unroll

    wtype_roll : type:wtype_roll

    wtype_eeqtp : type:wtype_eeqtp

    wind : type:wind
         =rec= defrec:wind

    wtype_iter : type:wtype_iter
               = def:wtype_iter

The unroll rewrite for wtype_iter is:

    wtype_iter a b P f m --> f (m #1) (m #2) (fn z . wtype_iter a b P f (m #2 z)) ;

It can be found in the registry as `Wtype.unroll_wtype_iter`.

Induction over W-types employs the `precedes` predicate, wherein
`precedes A B M N` states that `M` is an immediate prececessor of
`N`:

    precedes : type:precedes
             = def:precedes

    precedes_well_founded : type:precedes_well_founded
