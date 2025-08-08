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

This compatibility lemma is useful for rewriting with `outpar`:

    outpar_compat : forall (i : level) (a : U i) (x y : partial a) .
                       halts x -> x = y : partial a -> outpar x = outpar y : a

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

    approx : intersect (i : level) .
                forall (a b : U i) (c : b -> U i) .
                  (partial a -> forall (x : b) . partial (c x)) -> partial a -> partial a -> U i
           = fn a b c f p q . forall (x : b) . halts (f p x) -> f p x = f q x : partial (c x)
           (3 implicit arguments)

Now we say that `y` induces `x` (for adapter `f` and recursive
operator `g : partial a -> partial a`) when for every `p` that
approximates `fix g`, the termination of `f (g p) y` implies the
termination of `f p x`:

    induce : intersect (i : level) .
                forall (a b : U i) (c : b -> U i) .
                  admiss a
                  -g> (partial a -> forall (x : b) . partial (c x))
                      -> (partial a -> partial a)
                      -> b
                      -> b
                      -> U i
           = fn a b c f g x y .
                forall (p : partial a) . approx f p (fix g) -> halts (f (g p) y) -> halts (f p x)
           (3 implicit arguments)

The proviso that `p` approximates `fix g` is necessary because
sometimes an argument to a recursive call is determined by the result
of a previous recursive call, and in such cases we usually need to
know that previous recursive result was correct.

With these definitions in hand, we can prove that inducement is
well-founded:

    induce_well_founded : forall
                             (i : level)
                             (a b : U i)
                             (c : b -> U i)
                             (f : partial a -> forall (x : b) . partial (c x))
                             (g : partial a -> partial a) .
                             admiss a
                             -> uptype b
                             -> (forall (x : b) . admiss (c x))
                             -> (forall (p : partial a) (x : b) . halts (f p x) -> halts p)
                             -> (forall (p q : partial a) . approx f p q -> approx f (g p) (g q))
                             -> forall (x : b) . halts (f (fix g) x) -> Acc.Acc b (induce f g) x

Note that `Acc` is an uptype whenever the underlying type is an
uptype.  This fact is necessary because we prove well-foundedness
using fixpoint induction.

    Acc_uptype : forall (i : level) (a : U i) (P : a -> a -> U i) (x : a) .
                    uptype a -> uptype (Acc.Acc a P x)
