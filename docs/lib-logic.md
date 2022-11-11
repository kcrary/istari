# `Logic`

    not : intersect (i : level) . U i -> U i
        = fn P . P -> void

    iff : intersect (i : level) . U i -> U i -> U i
        = fn P Q . (P -> Q) & (Q -> P)

    iff_refl : forall (i : level) (P : U i) . P <-> P

    iff_symm : forall (i : level) (P : U i) (Q : U i) . P <-> Q -> Q <-> P

    iff_trans : forall (i : level) (P : U i) (Q : U i) (R : U i) .
                   P <-> Q -> Q <-> R -> P <-> R
