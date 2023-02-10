# `Logic`

### Negation

    not : intersect (i : level) . U i -> U i
        = fn P . P -> void

    not_inhabitant : forall (i : level) (P : U i) . not P -> (fn v0 . ()) : not P

    not_compat_arrow : forall (i : level) (P P' : U i) . (P -> P') -> not P' -> not P


### If-and-only-if

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

    prod_compat_iff : forall (i : level) (P P' Q Q' : U i) .
                         P <-> P' -> Q <-> Q' -> P & Q <-> P' & Q'

    sum_compat_iff : forall (i : level) (P P' Q Q' : U i) .
                        P <-> P' -> Q <-> Q' -> P % Q <-> P' % Q'


##### Rewriting propositions

    prod_commute : forall (i : level) (P Q : U i) . P & Q <-> Q & P

    prod_assoc : forall (i : level) (P Q R : U i) . (P & Q) & R <-> P & Q & R

    prod_id_l : forall (i : level) (P : U i) . unit & P <-> P

    prod_id_r : forall (i : level) (P : U i) . P & unit <-> P

    prod_ann_l : forall (i : level) (P : U i) . void & P <-> void

    prod_ann_r : forall (i : level) (P : U i) . P & void <-> void

    sum_commute : forall (i : level) (P Q : U i) . P % Q <-> Q % P

    sum_assoc : forall (i : level) (P Q R : U i) . (P % Q) % R <-> P % Q % R

    sum_id_l : forall (i : level) (P : U i) . void % P <-> P

    sum_id_r : forall (i : level) (P : U i) . P % void <-> P

    sum_ann_l : forall (i : level) (P : U i) . unit % P <-> unit

    sum_ann_r : forall (i : level) (P : U i) . P % unit <-> unit

    true_iff_unit : forall (i : level) (P : U i) . P -> P <-> unit

    false_iff_void : forall (i : level) (P : U i) . not P -> P <-> void


### Equality

    eq_refl : forall (i : level) (a : U i) (x : a) . x = x : a

    eq_symm : forall (i : level) (a : U i) (x y : a) . x = y : a -> y = x : a

    eq_symm_iff : forall (i : level) (a : U i) (x y : a) . x = y : a <-> y = x : a

    eq_trans : forall (i : level) (a : U i) (x y z : a) . x = y : a -> y = z : a -> x = z : a
