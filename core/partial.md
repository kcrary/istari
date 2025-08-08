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

This compatibility lemma is useful for rewriting with `outpar`:

    outpar_compat : type:outpar_compat

Attempting to rewrite the term immediately beneath an `outpar` tends
to generate an unprovable termination subgoal.


### Inducement

Given some recursive function `h`, we say that `y` induces `x` when
computing `h y` entails computing `h x`.  If `h y` halts, we can do
induction using the entailment relation (over the arguments that `y`
induces), viewing `x` as less than `y` when `y` induces `x`.

In our formulation of inducement, it is convenient not to restrict
ourselves only to partial functions with a single argument.  Instead,
we work with partial terms (say, having type `partial a`) and a
function that adapts such partial terms into partial function with a
single argument.  Thus the adapter has type:

    partial a -> forall (x : b) . partial (c x)

In the special case where the computation of interest actually is a
partial function with a single argument, the adapter can be simply the
eta-expanded identity `fn h x . h x`.

Suppose `p` and `q` are partial terms and `f` is an adapter.  Then we
say that `p` approximates `q` when `f p` and `f q` agree for every
argument on which `f p` halts.

    approx : type:approx
           = def:approx
           imp:approx

Now we say that `y` induces `x` (for adapter `f` and recursive
operator `g : partial a -> partial a`) when for every `p` that
approximates `fix g`, the termination of `f (g p) y` implies the
termination of `f p x`:

    induce : type:induce
           = def:induce
           imp:induce

The proviso that `p` approximates `fix g` is necessary because
sometimes an argument to a recursive call is determined by the result
of a previous recursive call, and in such cases we usually need to
know that previous recursive result was correct.

With these definitions in hand, we can prove that inducement is
well-founded:

    induce_well_founded : type:induce_well_founded

Note that `Acc` is an uptype whenever the underlying type is an
uptype.  This fact is necessary because we prove well-foundedness
using fixpoint induction.

    Acc_uptype : type:Acc_uptype
