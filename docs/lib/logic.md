# `Logic`

    not : intersect (i : level) . U i -> U i
        = fn P . P -> void

    not_inhabitant : forall (i : level) (P : U i) . not P -> (fn v0 . ()) : not P

    not_compat_arrow : forall (i : level) (P P' : U i) . (P -> P') -> not P' -> not P

    iff : intersect (i : level) . U i -> U i -> U i
        = fn P Q . (P -> Q) & (Q -> P)

    iff_refl : forall (i : level) (P : U i) . P <-> P

    iff_symm : forall (i : level) (P Q : U i) . P <-> Q -> Q <-> P

    iff_trans : forall (i : level) (P Q R : U i) . P <-> Q -> Q <-> R -> P <-> R

    iff_compat : forall (i : level) (P P' Q Q' : U i) .
                    P <-> P' -> Q <-> Q' -> (P <-> Q) <-> (P' <-> Q')

    iff_compat_1 : forall (i : level) (P P' Q : U i) . P <-> P' -> (P <-> Q) <-> (P' <-> Q)

    iff_compat_2 : forall (i : level) (P Q Q' : U i) . Q <-> Q' -> (P <-> Q) <-> (P <-> Q')

    not_compat_iff : forall (i : level) (P P' : U i) . P <-> P' -> not P <-> not P'
