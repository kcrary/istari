# `Relations`

Lexicographic order on pairs.

    lexrel : intersect (i : level) .
                forall (a b : U i) (Q : a -> a -> U i) (R : b -> b -> U i) (x y : a & b) . U i
           = fn a b Q R x y . Q (x #1) (y #1) % x #1 = y #1 : a & R (x #2) (y #2)

    lexrel_well_founded : forall (i : level) (a b : U i) (Q : a -> a -> U i) (R : b -> b -> U i) .
                             (forall (x : a) . Acc a Q x)
                             -> (forall (x : b) . Acc b R x)
                             -> forall (x : a & b) . Acc (a & b) (lexrel Q R) x

