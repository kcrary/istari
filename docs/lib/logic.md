# `Logic`

### Negation

    not : intersect (i : level) . U i -> U i
        = fn P . P -> void

    not_inhabitant : forall (i : level) (P : U i) . not P -> (fn v0 . ()) : not P

    not_compat_arrow : forall (i : level) (P P' : U i) . (P -> P') -> not P' -> not P


### If-and-only-if

    iff : intersect (i : level) . U i -> U i -> U i
        = fn v0 v1 . (v0 -> v1) & (v1 -> v0)

    iff_refl : forall (i : level) (P : U i) . P <-> P

    iff_refl' : forall (i : level) (P Q : U i) . P = Q : U i -> P <-> Q

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


### Not equal

    (* != *)
    neq : intersect (i : level) . forall (a : U i) . a -> a -> U i
        = fn a m n . not (m = n : a)

    neq_symm : forall (i : level) (a : U i) (x y : a) . x != y : a -> y != x : a

    neq_symm_iff : forall (i : level) (a : U i) (x y : a) . x != y : a <-> y != x : a


### Transport

In Istari's type theory, if the types `A` and `B` are equal, the
members of `A` are also members of `B`.  It is not type-theoretically
necessary to transport terms from `A` to `B`.  However, putting an
explicit transport into a term can make things easier for the
typechecker.

    transport : intersect (i : level) .
                   forall (a : U i) (x y : a) (b : a -> U i) . x = y : a -> b x -> b y
              = fn a x y b h m . m
              (3 implicit arguments)

Note that `transport` can be folded into or out of existence, as
desired.

    subtransport : intersect (i : level) . forall (a b : U i) . a <: b -> a -> b
                 = fn a b h m . m
                 (2 implicit arguments)


### Constructive choice

    function_description : forall
                              (i : level)
                              (a : U i)
                              (b : a -> U i)
                              (P : forall (x : a) . b x -> U i) .
                              (forall (x : a) . exists (y : b x) . P x y)
                              -> exists (f : forall (x : a) . b x) . forall (x : a) . P x (f x)

    function_description_nondep : forall (i : level) (a b : U i) (P : a -> b -> U i) .
                                     (forall (x : a) . exists (y : b) . P x y)
                                     -> exists (f : a -> b) . forall (x : a) . P x (f x)
