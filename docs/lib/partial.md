# `Partial`

The type `partial A` is the type of partial computable objects:

    partial : intersect (i : level) . U i -> U i

The (possibly partial) term `M` belongs to `partial A` if `M : A`
whenever `M` halts.

The predicate `halts M` indicates that the term `M` halts:

    halts : intersect (i : level) (a : U i) . partial a -> U 0

    partial_elim : forall (i : level) (a : U i) (x : partial a) . halts x -> x : a

The predicate `admiss A` indicates that `A` is eligible for fixpoint induction.

    admiss : intersect (i : level) . U i -> U i

    fixpoint_induction : forall (i : level) (a : U i) (f : partial a -> partial a) .
                            admiss a -> fix f : partial a

A principal tool for showing that a type is admissible is to show that
it is *upwards closed* with respect to computational approximation.
Such types are called *uptypes*:

    uptype : intersect (i : level) . U i -> U i

    uptype_impl_admiss : forall (i : level) (a : U i) . uptype a -> admiss a

The advantage of uptypes is they have very good closure properties.
Nearly every type that does not involve partiality is an uptype.


The divergent term `bottom` belongs to every partial type:

    bottom : intersect (i : level) (a : U i) . partial a
           = fix (fn v0 . v0)
