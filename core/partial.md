open:Partial
# `Partial`

The type `partial A` is the type of partial computable objects:

    partial : type:partial

The (possibly partial) term `M` belongs to `partial A` if `M : A`
whenever `M` halts.

The predicate `halts M` indicates that the term `M` halts:

    halts : type:halts

    partial_elim : type:partial_elim

The predicate `admiss A` indicates that `A` is eligible for fixpoint induction.

    admiss : type:admiss

    fixpoint_induction : type:fixpoint_induction

A principal tool for showing that a type is admissible is to show that
it is *upwards closed* with respect to computational approximation.
Such types are called *uptypes*:

    uptype : type:uptype

    uptype_impl_admiss : type:uptype_impl_admiss

The advantage of uptypes is they have very good closure properties.
Nearly every type that does not involve partiality is an uptype.


The divergent term `bottom` belongs to every partial type:

    bottom : type:bottom
           = def:bottom
