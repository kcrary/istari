open:Partial
# `Partial`

The type `partial A` is the type of partial computable objects:

    partial : type:partial

The (possibly partial) term `M` belongs to `partial A` if `M : A`
whenever `M` halts.

The predicate `halts M` indicates that the term `M` halts:

    halts : type:halts

    partial_elim : type:partial_elim

The predicate `admiss A` indicates that `A` is eligible for forming
well-typed fixpoints:

    admiss : type:admiss

    fixpoint_formation : type:fixpoint_formation

A principal tool for showing that a type is admissible is to show that
it is *upwards closed* with respect to computational approximation.
Such types are called *uptypes*:

    uptype : type:uptype

    uptype_impl_admiss : type:uptype_impl_admiss

The advantage of uptypes is they have very good closure properties.
Nearly every type that does not involve `partial` is an uptype.

To show admissibility of exists and set type requires the auxiliary
notion of predicate admissibility.

    padmiss : type:padmiss

The syntactic sugar `padmiss (x : A) . B` is accepted for 
`padmiss A (fn x . B)`.

The `seq` form is used to force the computation of one term before
another:

    seq : type:seq

The syntactic sugar `seq x = M in N` is accepted for 
`seq M (fn x . N)`. 


The divergent term `bottom` belongs to every partial type:

    bottom : type:bottom
           = def:bottom


Predicate admissibility gives us one of the most useful tools for
proving facts about partial computations:

    fixpoint_induction : type:fixpoint_induction

To assist in typechecking partial terms, there are injection and
extraction forms for partial types:

    inpar : type:inpar
          = def:inpar

    outpar : type:outpar
           = def:outpar

Note that both `inpar` and `outpar` are both the identity, so they can
be folded into existence, and unfolded out of existence.  They are
used just as hints for the typechecker.
