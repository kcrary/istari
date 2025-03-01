# Proof irrelevance

The [squash type](type-theory.html#subset-types) `{ A }` provides a
way to assert that `A` is true without providing the inhabitant.  The
type `{ A }` contains `()` exactly when `A` contains something.
Destructing a hypothesis of type `{ A }` produces a new hypothesis of
type `A`, but that new hypothesis is *hidden*, which means that it can
be used only in very limited ways.

Hidden variables are a device in the proof engine.  They ensure that
the hidden variable does not appear in the proof's computational
content.  To write a *program* that refers to unknown inhabitants, one
requires **proof irrelevance**.

We say that a function `fn x . M` is *parametric* if the argument `x`
does not contribute to the computational or semantic meaning of `M`.
We call this notion *irrelevance*, saying "`x` appears only in
irrelevant positions within `M`", or, more briefly, "`x` is irrelevant
in `M`".  Intuitively, `x` is irrelevant in `M` when fully unfolding
all the constants in `M` and normalizing the result results in a
normal form that does not contain `x`.

The type `parametric (x : A) . B` contains the parametric dependent
functions from `A` to `B`.  It is introduced by `fn` as usual, and
eliminated by parametric application: `f Ap m`.  Importantly, the
argument in parametric application is an irrelevant position.

Some other irrelevant arguments to important constants are `x` and `A`
in `f ap x`, `abort x`, `M :> A`, and `fn (x : A) . M`.


#### Applications

One important use for parametric functions is in impredicativity.  The
semantic requirements of impredicative quantification demand that an
impredicative function's argument not be available computationally in
its body.  In Istari's primitive [impredicative
functions](type-theory.html#impredicative-quantification), the
argument is not passed into the "function" at all.  However,
impredicative functions are
[isomorphic](lib/irrelevance.html#impredicative-functions) to
parametric functions, which do allow the argument to be manipulated,
albeit irrelevantly.  (Note that the isomorphism does not mean that
parametric functions are impredicative, so we cannot simply dispense
with impredicative functions.)

This makes for a similar situation as in the polymorphic lambda
calculus.  In the polymorphic lambda calculus, a polymorphic
function's type argument can only be used in a lambda abstraction's
type annotation, or in a polymorphic application.  In Istari, both of
those (written `fn (x : A) . M` and `f Ap t`) are irrelevant
positions, and are thus permissible uses of a parametric argument.

[Weak sums](lib/weaksum.html) are a particularly important application
of parametric functions.  Weak sums are isomorphic to impredicative
existentials, but the latter behaves like a union type and can be very
difficult to use practically.

The [proof irrelevance
modality](lib/irrelevance.html#proof-irrelevance) is yet another
application.  It allows a computation to manipulate unknown (*i.e.,*
proof irrelevant) objects.


#### Formalization

The introduction rule for parametric functions states:

    G |- (fn x . M) : parametric A (fn x . B)
    >>
    G |- A : type
    G |- irrelevant (fn x . M)
    G, x : A |- M : B

The second premise states that `x` is irrelevant in `M`.  That is the
case when `M` is syntactically equivalent to `[unavailable / x]M`.
The typechecker will normally discharge irrelevance premises
automatically.


#### Practical considerations

Consider parametric application of a known function:

    (fn x . M) Ap N

This reduces to `[N / x]M`, but only when `x` is irrelevant in `M`.
The `reduce` tactic will not do this, as it only handles unconditional
reductions.  Instead, use the `reduceParam` tactic.

Suppose `foo` is a newly defined constant.  To tell Istari that its
first and second arguments are irrelevant, call:

    recordIrrelevance /foo/ [0, 1];

Istari will check that arguments 0 and 1 are indeed irrelevant, then
record that information in the database.  The list of indices must be
strictly increasing.  Once the irrelevance is recorded, parametric
variables can be used in `foo`'s first and second arguments.

