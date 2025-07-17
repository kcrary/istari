# `Partial`

The type `partial A` is the type of partial computable objects:

    partial : intersect (i : level) . U i -> U i

The (possibly partial) term `M` belongs to `partial A` if `M : A`
whenever `M` halts.

The predicate `halts M` indicates that the term `M` halts:

    halts : intersect (i : level) (a : U i) . partial a -> U 0

    partial_elim : forall (i : level) (a : U i) (x : partial a) . halts x -> x : a

The predicate `admiss A` indicates that `A` is eligible for forming
well-typed fixpoints:

    admiss : intersect (i : level) . U i -> U i

    fixpoint_formation : forall (i : level) (a : U i) (f : partial a -> partial a) .
                            admiss a -> fix f : partial a

A principal tool for showing that a type is admissible is to show that
it is *upwards closed* with respect to computational approximation.
Such types are called *uptypes*:

    uptype : intersect (i : level) . U i -> U i

    uptype_impl_admiss : forall (i : level) (a : U i) . uptype a -> admiss a

The advantage of uptypes is they have very good closure properties.
Nearly every type that does not involve `partial` is an uptype.

To show admissibility of exists and set type requires the auxiliary
notion of predicate admissibility.

    padmiss : intersect (i : level) . forall (a : U i) . (a -> U i) -> U i

The syntactic sugar `padmiss (x : A) . B` is accepted for 
`padmiss A (fn x . B)`.

The `seq` form is used to force the computation of one term before
another:

    seq : intersect (i : level) (a b : U i) . partial a -> (a -> partial b) -> partial b

The syntactic sugar `seq x = M in N` is accepted for 
`seq M (fn x . N)`. 


The divergent term `bottom` belongs to every partial type:

    bottom : intersect (i : level) (a : U i) . partial a
           = fix (fn v0 . v0)


Predicate admissibility gives us one of the most useful tools for
proving facts about partial computations:

    fixpoint_induction : forall
                            (i : level)
                            (a : U i)
                            (P : partial a -> U i)
                            (f : partial a -> partial a) .
                            admiss a
                            -> (padmiss (x : partial a) . P x)
                            -> (forall (x : partial a) . (halts x -> P x) -> P x)
                            -> (forall (x : partial a) . P x -> P (f x))
                            -> P (fix f)

To assist in typechecking partial terms, there are injection and
extraction forms for partial types:

    inpar : intersect (i : level) (a : U i) . forall (m : a) . strict a -g> partial a
          = fn m . m

    outpar : intersect (i : level) (a : U i) . forall (m : partial a) . halts m -g> a
           = fn m . m

Note that both `inpar` and `outpar` are both the identity, so they can
be folded into existence, and unfolded out of existence.  They are
used just as hints for the typechecker.
