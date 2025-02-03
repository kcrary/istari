# `Wtype`

Martin-L&ouml;f's well-founded (or "W") types are a solution to the equation:

    wtype (x : A) . B(x)  ==  exists (x : A) . B(x) -> wtype (x' : A) . B(x')

Martin-L&ouml;f (1984) intended them as constructive ordinals, but
they can also be used to implement a variety of data structures.  (In
Istari, datatypes usually provide a more convenient mechanism with
better canonicity properties.)

    wtype : intersect (i : level) . forall (a : U i) . (a -> U i) -> U i
          = fn a b . mu t . (exists (x : a) . b x -> t)

    wtype_unroll : forall (i : level) (a : U i) (b : a -> U i) .
                      (wtype (x : a) . b x) <: (exists (x : a) . b x -> wtype (x1 : a) . b x1)

    wtype_roll : forall (i : level) (a : U i) (b : a -> U i) .
                    (exists (x : a) . b x -> wtype (x1 : a) . b x1) <: (wtype (x : a) . b x)

    wtype_eeqtp : forall (i : level) (a : U i) (b : a -> U i) .
                     (wtype (x : a) . b x) <:> (exists (x : a) . b x -> wtype (x1 : a) . b x1)

    wind : intersect (i : level) (a : U i) (b : a -> U i) (P : (wtype (x : a) . b x) -> U i) .
              (forall (x : a) (y : b x -> wtype (x1 : a) . b x1) .
                 (forall (z : b x) . P (y z)) -> P (x, y))
              -> forall (m : wtype (x : a) . b x) . P m
         =rec= fn f m . f (m #1) (m #2) (fn z . wind f (m #2 z))

    wtype_iter : intersect (i : level) .
                    forall (a : U i) (b : a -> U i) (P : (wtype (x : a) . b x) -> U i) .
                      (forall (x : a) (y : b x -> wtype (x1 : a) . b x1) .
                         (forall (z : b x) . P (y z)) -> P (x, y))
                      -> forall (m : wtype (x : a) . b x) . P m
               = fn a b P f m . wind f m

The unroll rewrite for wtype_iter is:

    wtype_iter a b P f m --> f (m #1) (m #2) (fn z . wtype_iter a b P f (m #2 z)) ;

It can be found in the registry as `Wtype.unroll_wtype_iter`.

Induction over W-types employs the `precedes` predicate, wherein
`precedes A B M N` states that `M` is an immediate prececessor of
`N`:

    precedes : intersect (i : level) .
                  forall (a : U i) (b : a -> U i) .
                    (wtype (x : a) . b x) -> (wtype (x : a) . b x) -> U i
             = fn a b m n . exists (y : b (n #1)) . m = n #2 y : (wtype (x : a) . b x)

    precedes_well_founded : forall
                               (i : level)
                               (a : U i)
                               (b : a -> U i)
                               (m : wtype (x : a) . b x) .
                               Acc.Acc (wtype (x : a) . b x) (precedes a b) m
