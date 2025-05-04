# The Istari type theory

## Organizing principles

Istari's logic is a *type assignment* system, meaning that
computational terms (more-or-less the untyped lambda calculus) exist
prior to the type system, and the type system assigns types to them.
A term might have no type (in which case we call it ill-typed), or it
might have multiple types.

Membership in a type is a fact that is proven, and it may depend on
all available hypotheses.  This means that typechecking is
undecidable.  For example, if `M : A(N)` then whether `M : A(N')` may
depend on whether `N` and `N'` are equal, which is undecidable in
general.  Or, as a simpler example, if `void` follows from the current
hypotheses (which is undecidable), then any term has any type.

The undecidability of typechecking means that typing is a subject of
discourse *within the logic.*  Typically, the Istari typechecker
discharges typechecking goals, but under some circumstances the user
might have to prove them.  Put another way, Istari affords the user
the opportunity to establish typings that can be established
automatically.

Typing proofs are not part of the terms being typed.  Thus, in the
earlier example, the `M` that belongs to `A(N)` and the `M` that
belongs to `A(N')` are literally the same term.  There is no
"transport" from `A(N)` to `A(N')` to create obstacles to reasoning
about `M` and its interaction with other terms.  An important
consequence of this design is it streamlines the use of dependent
types.

All of Istari's primitive rules are given [here](rules.html).


#### What is a type?

Istari is a Martin-L&ouml;f-style type theory [4], which means (in
part) that a type consists not only of a set of elements, but also an
*equality* relation on its elements.  Two terms might be equal in one
type but inequal in another.  (This is most obvious with [quotient
types](#quotient-types), which coarsen the equality of an existing type.)

There is no categorical or Leibniz equality in Istari.  Type-theoretic
equality is always relative to a particular type.  (But see
[*computational equality*](#computational-equality) below.)  This has
some important consequences in the [substitution rule](#substitution).
There also is no "definitional equality" as a separate concept from
the equalities given by types.  Put another way, the equality given
by a type **is** definitional equality.

Most Istari equalities are *extensional* in a sense appropriate to the
type.  For example, to prove:

    (fn x . M) = (fn x . N) : (A -> B)

one can show that `M = N : B` assuming `x : A`.

On the other hand, type equivalence in Istari is *intentional*,
meaning that it depends on the structure of the type expression,
rather than on its set of members or its equality.  For example,
consider `A -> B` and `A' -> B'`.  The two types are equal only when
`A` is equivalent to `A'` and `B` to `B'`, even though it is easier
for them to have the same membership (such as when `A` and `A'` are
empty).  Formation is reflexive equivalence (see
[below](#judgements)), so without this injectivity property we could
not, for example, conclude from `A -> B` being well-formed that `A`
and `B` are well-formed, which in turn would necessitate an extra
premise `B : type` for every function application.


#### Computational equality

Every type (and its equality) is closed with respect to *computational
equality*.  Thus, in order to show `M : A`, it is permissible first to
show that `M` is computationally equivalent to `M'` and then show that
`M' : A`.

Computational equality consists of beta equivalence and unfolding of
defined constants.  Beta equivalence is call-by-name, but that rarely
matters since terms have no side effects and most types contain only
terminating terms.  In the implementation, reductions and certain
rewrites express computational equality, and unification also
understands computational equality to some extent.

Computational equality unfortunately does *not* include eta
equivalence, although most types' equalities *are* closed under eta.
This is inevitable since computational equality is prior to types,
because one cannot justify saying `M` is equivalent to `fn x . M x`
unless one knows that `M` is a function.  Moreover, if `M` diverges
then clearly it cannot be considered equal to the value `fn x . M x`.


#### Judgements

Martin-L&ouml;f type theory is based on four judgements:

1. type formation (`A : type`)
2. type equivalence (`A = B : type`)
3. membership (`M : A`)
4. equality (`M = N : A`)

In Istari, as in some other realizations of Martin-L&ouml;f type
theory [1], the four judgements are collapsed into one
inhabitation judgement, written `A ext M`.  Type-theoretically this
means `M = M : A`, but the user is presented only with the type `A`.
The inhabitant (or "extract") `M` is obtained automatically from the
proof.

Martin-L&ouml;f's four judgements are internalized as types: `istp`,
`eqtp`, `of`, and `eq`, respectively.  For example, `M = N : A` is
expressed as the inhabitation of the type `eq A M N`.  Type formation
and membership are in turn defined as reflexive instances of equality;
`istp A` means `eqtp A A`, and `of A M` means `eq A M M`.


#### Hypotheses

The Istari implementation understands seven sorts of hypothesis:

1. term assumptions, written `x : A`
2. future term assumptions, written `x (later) : A`
3. hidden term assumptions, written `x (hidden) : A`
4. type assumptions, written `t : type`
5. future type assumptions, written `t (later) : type`
6. hidden type assumptions, written `t (hidden) : type`
7. let assumptions, written `x = M`

Most hypotheses are simple term assumptions.  Hypothetical types are
usually written as term assumptions with a [universe](#universes-and-kinds) as
its type, but they can also be expressed without a level using a type
assumption.

Future assumptions are used in conjunction with the [future
modality](#future-modality) and [recursive types](#recursive-types).
They represent assumptions that will become available only in the
future.  When using a rule that moves into the future (such as [future
introduction](rules.html#future-modality)), any future assumptions are
automatically promoted to become ordinary (term or type) assumptions.

Hidden assumptions have no special status in the type theory.  A
hidden assumption, say `x (hidden) : A`, expresses the syntactic
restriction that `x` cannot appear in the extract.  This expresses a
sort of proof irrelevance; the extract cannot make decisions based on
`x` if it cannot refer to `x` at all.  Hidden assumptions arise in
various ways, but especially from [subset types](#subset-types): when
destructing `M : { x : A | B(x) }`, we learn that `B(M)` must be
inhabited but we have no access to the inhabitant.

A let assumption `x = M` makes `x` synonymous with `M`, which can be
used to manage complexity in proofs.  Like hidden assumptions, let
assumptions are unknown to the type theory.  When `M` is a fixed point
`fix (fn x . N)`, the implementation displays the let assumption as
`x =rec= N`.

The meaning of a hypothetical judgement is always *functional*.  For
example, `x : A |- B ext M` does **not** merely mean that 
`[N/x]M : [N/x]B` for every `N : A`.  It means that 
`[N/x]B = [N'/x]B : type` and `[N/x]M = [N'/x]M : [N/x]B` for every 
`N = N' : A`.  Additional complications arise in judgements with two
or more hypotheses (see [pointwise
functionality](#pointwise-functionality) below).


#### Universes and Kinds

Istari supports both predicative and impredicative quantification:

Predicative quantification is accomplished using dependent types and a
cumulative hierarchy of universes.  The universe `U(0)` contains all
small types (*i.e.,* types built without mentioning universes or
kinds).  The universe `U(1)` contains all small types, and also types
built using `U(0)`.  When `j < i`, the universe `U(i)` contains all
types in `U(j)` plus all types built using the universe `U(j)`.

Note the collection of all types is not merely the union of the
universes.  There exist some types that are too large to fit into any
universe.  A simple example is `forall (i : level) . U(i)`.

To quantify universally over all small types, one writes 
`forall (a : U(0)) . whatever`.  The resulting type is not small;
it belongs to `U(1)`, assuming that `whatever` belongs to `U(1)`.

Predicative quantification can be done using any valid type as the
domain, and results in a type one level higher.  In contrast,
*impredicative* quantification can be done with only certain types,
and results in a type at the same level.  The types that may be used
in impredicative quantification are called *kinds.* The type `K(i)`
contains all kinds available at level `i`.  Notably, `U(i)` belongs to
`K(i)`.

For example, to quantify
[impredicatively](#impredicative-quantification) over all small types,
one might write `iforall 0 (a : U(0)) . whatever`.  This quantifies
impredicatively at level `0`, since `U(0)` belongs to `K(0)`.  Thus,
the resulting type belongs to `U(0)`, assuming that `whatever` also
belongs to `U(0)`.  Note that the quantifier in that type ranges over
itself.

(In the implementation, the impredicative quantifier's level (*e.g.,*
the first `0` in the example) is kept implicit; it is not displayed
and it is inferred automatically.  Thus impredicative quantifiers look
similar to predicative ones.)

In general, a type `A` is a kind when `A` is isomorphic to a space in
Istari's metric-space semantics.  Such types include [function
spaces](#functions) (specifically T-functions and K-functions),
non-dependent [products](#strong-sums-and-products),
[unit](#base-types), the [future modality](#future-modality), and
[guarded recursive types](#recursive-types).  Impredicative
quantification over guarded recursive types is one of the main
novelties of the Istari type theory.

Note that the indexing for kinds is off by one from the indexing for
universes: `K(i)` (which contains `U(i)`) is a subset of `U(i+1)`.
Unlike universes, kinds are not cumulative.  For example, `U(0)`
belongs to `K(0)`, but not `K(1)`.




## Types

#### Functions

[[rules]](rules.html#dependent-functions)

Istari includes four function types.  The dependent function space,
`forall (x : A) . B`, contains functions `(fn x . M)` such that `M : B`
assuming that `x : A`.  The non-dependent function space `A -> B` is
the same, except `x` does not appear free in `B`.

Function equality is extensional.  That is, `(fn x . M)` and 
`(fn x . N)` are equal at `forall (x : A) . B` if `M = N : B` assuming
`x : A`.  Furthermore, since hypotheticals are always interpreted
functionally, it follows that `(fn x . M)` equals 
`(fn x . N)` at `forall (x : A) . B` exactly when
`[P/x]M = [Q/x]N : [P/x]B` whenever `P = Q : A`.

Note that if `A` is uninhabited, `forall (x : A) . B` and `A -> B` are
well-formed types even when `B` is junk.

The remaining basic function spaces are T-functions (`A -t> K`) and
K-functions (`K -k> K'`).  Both of them are equal to the ordinary
function type, so they are are interchangeable with ordinary functions
to a significant degree.  A minor difference is the codomain of a T-
or K-arrow must be well-formed without any assumptions, while the
codomain of an arrow may assume the domain.

The distinction of T- and K-arrow is they are kinds, so they can be
used in impredicative quantification.  In a T-function the domain is
an ordinary type (at the same level as the kind), while in a
K-function the domain is a kind.

For example, `nat -t> U(0)` and `U(0) -k> U(0)` both belong to `K(0)`,
and `U(0) -t> U(1)` belongs to `K(1)`.

Other function-like types (intersection types, parametric functions,
and future functions) are discussed below.


#### Strong sums and products

[[rules]](rules.html#strong-sums)

The strong sum, `exists (x : A) . B`, is Istari's dependent type for
pairs.  It contains pairs `(M , N)` such that `M : A` and 
`N : [M / x]B`.  It also requires that `B : type` assuming `x : A`,
since this does not follow from the substitution instance `[M / x]B`
being a type.

The defining property of a strong sum is the elimination forms for it
are projection.  If `M : exists (x : A) . B`, then the first
projection from `M` (written `M #1`) has type `A`, while the second
projection (written `M #2`) has type `[M #1 / x]B`.

(In contrast, the elimination form for a weak sum (such as the
[impredicative existential](#impredicative-quantification)) would only
give access to the constituents of the pair in a closed scope.
Sometimes the weak sum is called an existential type, but we do not
use that terminology in Istari, since Istari uses the strong sum for
existential quantification.)

The non-dependent form of the strong sum is the product type, written
`A & B`.  (We reserve the operator `*` for multiplication.)  It plays
the role of the "and" connective.  A variant of the product is the
semi-dependent product, written `A &d B`: when showing `A &d B` is
well-formed, one can assume `A` is inhabited while showing `B` is
well-formed.


#### Disjoint sums

[[rules]](rules.html#disjoint-sums)

The disjoint sum type, written `A % B`, plays the role of the "or"
connective.  (We reserve the operator `+` for addition.)  It contains
`inl M` ("in left") when `M : A`, and `inl N` ("in right") when `N : B`.


#### Intersection types

[[rules]](rules.html#intersection-types)

The intersection type, written `intersect (x : A) . B`, is the
intersection of `B` over all `x : A`.  Thus `N` belongs to 
`intersect (x : A) . B` if for all `M : A` we have `N :
[M / x]B`.

The intersection type is much like a [dependent function](#functions)
(particularly one whose argument is marked as implicit), but there is
an important difference: If `f : forall (x : A) . B` and `M, M' : A`,
then `f M : [M / x]B` and `f M' : [M' / x]B` are *different terms*,
even if the difference is not visually apparent because the argument
is marked implicit.  However, if `g : intersect (x : A) . B`, then 
`g : [M / x]B` and `g : [M' / x]B` are the exact same term.

We refer to the argument to an intersection type as an *invisible*
argument, to contrast it with implicit arguments, which are present
in the term but not displayed.  Invisible arguments can be supplied to
the typechecker using [visibilized
application](typechecking.html#coping-strategies).

Intersection types can be used however the user desires, but their
intended use is with [levels](#levels).  Consider:

    list : intersect (i : level) . forall (a : U i) . U i

Recall that `nat : U i`, for all `i`, and that `U 0` is contained in
`U 1` by cumulativity.  Then `list nat : U 1` two ways: by
instantiating `i` with `0` and subsuming `U 0` to `U 1`; or by
instantiating `i` with `1`.  Nevertheless, both paths to `U 1` are the
*same type.* In contrast, if instead `list` were a dependent function,
then the two paths would result in two different types, `list 0 nat`
and `list 1 nat`.


#### Parametric functions

[[rules]](rules.html#parametric-functions)

The parametric function type, written `parametric (x : A) . B` is the
type of dependent functions belonging from `A` and `B`, but the
argument cannot be used [relevantly](proof-irrelevance.html) in the
body.  It is useful for writing impredicative functions, or
manipulating impredicative packages (a.k.a. [weak
sums](lib/weaksum.html)).

Parametric functions are applied using parametric application, written
`f Ap x`.  The argument of a parametric application is an irrelevant
position, so `fn x . f Ap x` is a parametric function.

The intersection type `intersect (x : A) . B[x]` (and the impredicative
function type `iforall (x : K) . B[x]`, which works in much the same way)
can be hard to use, because the "body" must have the type `B[x]` but
isn't allowed to mention `x`.  This can make things challenging for
the typechecker.  In contrast, the body of a parametric function *can*
mention `x`, provided it uses it only irrelevantly.

This makes for a similar situation as in the polymorphic lambda
calculus.  In the polymorphic lambda calculus, a polymorphic
function's type argument can only be used in a lambda abstraction's
type annotation, or in a polymorphic application.  In Istari, both of
those (written `fn (x : A) . M` and `f Ap t`) are irrelevant
positions, and are thus permissible uses of a parametric argument.


#### Union types

[[rules]](rules.html#union-types)

The union type, written `union (x : A) . B`, is the
union of `B` over all `x : A`.  Thus `N` belongs to 
`union (x : A) . B` whenever there exists `M : A` such that 
`N : [M / x]B`.

The intersection is like a [dependent sum](#strong-sums-and-products)
(a.k.a. `exists`) except that the first constituent of the pair is
missing.  Only the second constituent is present.

The missing first component cannot be recovered by an open scope
elimination form.  Instead the elimination rule for union types
requires that the union be opened for some closed scope.  Thus a union
type is a form of what is called a *weak sum.* (In other settings,
weak sums are sometimes referred to as existential types, but we will
not use that terminology here, since we use strong sums for
existential quantification).

The practical impact of this is if `x` has a union type, `x` cannot be
destructed if any other hypothesis refers to `x`.  (This condition can
be obtained by reverting hypotheses if necessary.)  This is necessary
because the destruction tactic uses the conclusion as the closed scope
for eliminating the union.


#### Guarded types

[[rules]](rules.html#guarded-types)

The guarded type, written `A -g> B`, is equivalent to `B` if `A` is
true.  When showing membership or equality in `A -g> B`, one may
assume `A`.  Thus when `A` is false, `A -g> B` contains everything.

A guarded type is similar to a non-dependent [intersection
type](#intersection-types), but not quite the same.  If `A` is
inhabited, then `intersect (_ : A) . B` is extensionally equivalent to
`B` (*i.e.,* they contain the same elements) but they are not equal
types.  However, if `A` is inhabited then `A -g> B` is *equal* to `B`.
(This fact is necessary to support the [kindlike
construction](lib/kindlike.html).)


#### Coguarded types

[[rules]](rules.html#coguarded-types)

The coguarded type, written `A &g B`, is equivalent to `B` if `A` is
true.  When showing membership or equality in `A &g B`, one must also
prove `A`.  Conversely, from a proof of `A &g B` one may conclude that
`A` is true; although that fact will be [hidden](#hypotheses) and thus
not available to computational content.

A guarded type is similar to a non-dependent [union
type](#union-types), but not quite the same.  Since the union type is
a weak sum, it has a limited destruction rule, but the only limitation
when destructing a coguard is the hypothesis representing its
left-hand-side is hidden.


#### Future modality

[[rules]](rules.html#future-modality)

The future modality, written `future A` expresses that `A` will be
true *in the future*.  It contains `next M` when `M : A`.  But, while
checking `M : A`, any [future assumptions](#hypotheses) in the context
are promoted to the present.

For example, suppose the context contains `x (later) : A`.  Then
within the `next`, the context contains `x : A`.  Consequently we may
conclude `next x : future A`.

Future assumptions are also promoted while showing that a future
modality is well-formed.  For example, suppose again that the context
contains `x (later) : A`.  Then `future (x = x : A)` is a well-formed
type.

The future modality is eliminated by the `let next` form.  If 
`M : future A`, then `let next x = M in N` will add a future
hypothesis `x (later) : A` (corresponding to the body of `M`) while
typechecking `N`.  Moreover, `let next x = next M in N` is beta
equivalent to `[M / x]N`.

The main use of the future modality is (directly or indirectly) in
conjunction with [recursive types](#recursive-types).


##### Previous

An alternative way to eliminate the future modality is using the
"previous" form, written `M #prev`.  Previous is the inverse of
next, so `(next M) #prev` is beta equivalent to `M`, and `next (M
#prev)` is eta equivalent to `M`.  However, type checking `#prev` is
more baroque than `let next`.  When `M : future A`, we may say that 
`M #prev : A` **provided** that `M #prev` appears within a form that
moves into the future (such as `next` or `future`).  This is necessary
because previous moves us backward in time, and we must avoid moving
all the way into the past.

(We must avoid moving into the past because the future modality is
justified by a step-indexed semantics, and it is important that 
indices be well-ordered, so negative indices cannot be allowed.)

The two elimination forms are actually equivalent.  In fact, 
`let next x = M in N` is defined to mean `[M #prev / x]N`.  Thus, `let
next` is `#prev` wrapped up to make it more convenient to use.


#### Future functions

[[rules]](rules.html#future-functions)

The future dependent function space, written `forallfut (x : A) . B`
is very similar to the type 
`forall (x' : future A) . let next x = x' in B` except that a future
function's argument is not `next M` but simply `M` (unless `A` is
another future, of course).  Thus, if `f : forallfut (x : A) . B` and
`f` is being applied to `M`, `M` must have type `A`, but while
checking `M : A`, any future assumptions are promoted to the present.

In `B` and in the function body, `x` is a later assumption.
Consequently, `x` must appear guarded by `future` or `next`, or in the
argument to another future function.

As noted, a future function is very similar to an ordinary function
that uses a future domain.  Nevertheless they can be useful in some
situations because applying a future function does not involve a
`next`, which may improve the effectiveness of unification.

The future intersection, written `intersectfut (x : A) . B` is the
analogous intersection type with its invisible argument in the future.


#### Recursive types

[[rules]](rules.html#recursive-types)

Recursive types are written `rec t . A`.  As usual, 
`rec t . A` is equal to `[rec t . A / t]A`.
However, Istari's recursive types are *guarded* recursive types, which
means that every occurrence of `t` in `A` must be guarded by moving
into the future, usually using the future modality.

For example, the type [`ev A`](lib/eventually.html) is defined as
`rec t . A % future t`, which means `A` at some point in the future.
The recursive occurrence of `t` is guarded by placing it within the
`future`.

The guard requirement ensures that one cannot write nonsensical types
such as `rec t . t -> void`.  If it were a legal type (let's call it
`S`), then one could inhabit `void` using the omega combinator:

    (fn (x : S) . x x) (fn (x : S) . x x)

With the guard requirement in place, the closest one can write is 
`rec t . future t -> void`.  That is a legal type, but it cannot be
used to give a type to the omega combinator.

However, one can use guarded recursive types to give a type to a
variation on the Y combinator.  Let `T` be `rec t . future t -> A`.
Observe that the recursive occurrence of `t` is properly guarded.
Then the following ornamented Y combinator has the type 
`(future A -> A) -> A`:

    fn (f : future A -> A) .
      (fn (x : future T) . f (let next x' = x in next (x' x)))
      (next (fn (x : future T) . f (let next x' = x in next (x' x))))

Thus, to prove `A` it is sufficient to prove `A` assuming that `A` is
true in the future.  This is tantamount to proving `A` by induction
over time.  This is developed (with some minor differences) in the
[simulated partial types library](lib/eventually.html) `Eventually`.

One of the main features of the Istari type theory is that recursive
types are not only legal types, but they are also
[kinds](#universes-and-kinds), and are thus eligible for use as
domains for impredicative quantification.  With some work, this makes
it possible to express a store-passing transformation for imperative
code [5].

In a proof, one can unroll recursive types using the
[rewrite](rewriting.html#rewriting-tactics) `unrollType`.


#### Inductive types

[[rules]](rules.html#inductive-types)

A different self-referential type is the inductive type.  Inductive
types form the basis for the [datatype
mechanism](definitions.html#datatypes), which is usually more
convenient to use.  However, there are some inductive idioms that
cannot be expressed as datatypes.

An inductive type is written `mu t . A`.  The type `mu t . A` is
extensionally equivalent to `[mu t . A / t]A` in the sense that they
contain the same elements.  However, they are not equal types.
As with [recursive types](#recursive-types), not every inductive type
expression is legal.  For `mu t . A` to be valid, `A` must be
*positive* in `t`.

We say that `A` is positive in `t` if it satisfies the following
grammar:

    P ::= t
        | M
        | P & P
        | P % P
        | N -> P
        | forall (x : N) . P
        | exists (x : P) . P
        | future P
        | mu x . P
        | if M then P else P

    N ::= M
        | N & N
        | N % N
        | P -> N
        | forall (x : P) . N
        | exists (x : N) . N
        | future N
        | mu x . N
        | if M then N else N

Here, `P` and `N` express when a type is positive/negative in `t`,
while `M` refers to expressions that do not mention `t` free at all.
These are merely the connectives that Istari currently supports;
several other connectives could be added without any semantic obstacle.

In a proof, one can unroll inductive types using the
[rewrite](rewriting.html#rewriting-tactics) `unrollType`.

##### Robustness

Positivity ensures both the usual monotonicity condition that one
expects for inductive types, and also a condition specific to Istari
called *robustness*.  Both are necessary for an inductive type to be
semantically well-formed.  Robustness is a technical condition in the
semantics pertaining to candidates arising from impredicative
quantification.  Suppose `C` and `D` are equivalent candidates (in the
sense of having the same membership and equality), but `D` resides in
a higher universe than `C`.  Roughly speaking, we say that `A` is
robust in `t` if `[C / t]A` being well-formed implies that `[D / t]A`
is also well-formed and has the same meaning.  Most type expressions
are naturally robust &mdash; since most connectives cannot distinguish
between equivalent candidates &mdash; but type expressions (notably
equality types) that can refer to `t` being a member of a type are not
necessarily robust.


#### Base types

[[rules]](rules.html#void)

Istari's primitive base types are `void`, `unit`, and `bool`.
([Integers](#integers) can also be regarded as a base type.)  As
usual, `void` is uninhabited, `unit` contains the unit term (written
`()`), and `bool` contains `true` and `false`.


#### Natural numbers

[[rules]](rules.html#natural-numbers)

The natural number type `nat` is introduced by `zero` and `succ` and
eliminated by `natcase` and `nat_iter`.  (See the 
[`Nat` library](lib/nat.html) for details.)

Natural numbers are defined as `mu t . unit % t` rather than using the
datatype mechanism because the implementation of datatypes relies on
natural numbers.


#### Universes

[[rules]](rules.html#universes)

The universe type `univ i` contains all types at level `i`.  (Recall
the [discussion above](#universes-and-kinds).)


#### Kinds

[[rules]](rules.html#kinds)

The universe type `kind i` contains all the types at level `i` that
correspond to spaces in Istari's metric-space semantics, and are
therefore eligible for impredicative quantification.  (Recall the
[discussion above](#universes-and-kinds).)


##### Levels

[[rules]](rules.html#levels)

Levels are numbers used to express levels in the universe hierarchy.
Semantically levels are simply natural numbers, but in the
implementation it is convenient to consider levels and natural numbers
to be distinct types.

Levels are expressed using `lzero`, `lsucc`, and `lmax`, with the
expected meanings.  In a level expression, `lzero` is written `0`,
`lsucc i` is written `1 + i`, and `lmax i j` is written `[i j]`.


#### Equality

[[rules]](rules.html#equality)

Equality is written `M = N : A`.  The type is well-formed whenever 
`M : A` and `N : A`.  If true, its inhabitant is `()`.  It belongs to
universe `U(i)` whenever `A` belongs to `U(i)`.  Equality is
always symmetric, transitive, and closed under beta equivalence.  Its
other properties depend on the type `A`.


#### Typing

[[rules]](rules.html#typing)

Typing, written `M : A`, is defined to mean `M = M : A`.  As such it
is closed under beta equivalence, and, if true, its inhabitant is
`()`.

##### Negatability

Since `M : A` is defined to mean `M = M : A`, it is well-formed when
`M : A`.  Thus, `M : A` is well-formed exactly when it is true.  This
gives rise to a phenomenon called *negatability*, which is something
of a wart in Martin-L&ouml;f-style type theory.

Typing cannot usefully be written in an antecedent position such as
`(M : A) -> B`.  The type is well-formed only when we already know
`M : A`, so the implication serves no purpose.  In the extreme case,
`not (M : A)`, which is defined to mean `(M : A) -> void`, can never be
true.  It is well-formed only when it is false.  Thus we say that
typing is *not negatable.*

Note that this does *not* mean that typing (or other non-negatable
types) cannot appear in hypotheses.  On the contrary, typing
hypotheses can be very useful.  It just means that typing hypotheses
do not usually arise from implication.


#### Type equality

[[rules]](rules.html#type-equality)

It is sometimes useful to say that two types are equal without
reference to a universe, either because the universe is unknown, or
the types actually do not belong to a universe.  The type expressing
this fact is written `A = B : type`.  Note that this is not a form of
the equality type and there is no type called `type`.

The type `A = B : type` is well-formed when `A` and `B` are
well-formed types.  If true, its inhabitant is `()`.  It belongs to
universe `U(i)` when `A` and `B` both belong to universe `U(i)`,
although that is rarely important.  Type equality is always symmetric,
transitive, and closed under beta equivalence.


#### Type formation

[[rules]](rules.html#type-formation)

Type formation, written `A : type`, is defined to mean `A = A : type`.
As such it is closed under beta equivalence, and, if true, its
inhabitant is `()`.  Like typing, type formation is
[non-negatable](#negatability).


#### Subtyping

[[rules]](rules.html#subtyping)

Subtyping is written `A <: B`.  It means that every element of `A` is
an element of `B`, and equal elements of `A` are also equal in `B`.
The type is well-formed whenever `A` and `B` are well-formed types.
If true, its inhabitant is `()`.  It belongs to universe `U(i)`
whenever `A` and `B` belong to `U(i)`.  Subtyping is always transitive
and closed under beta equivalence.

One can almost define `A <: B` as `forall (x : A) . x : B`.  In fact,
the latter is sufficient to establish the former.  However, the latter
is well-formed only when `A` is a type, and when `x : B` for all 
`x : A`.  In other words, it is well-formed only when it is true, so
it is [non-negatable](#negatability).  In contrast, the former
only requires `A` and `B` to be types.  This means that one can
usefully express lemmas that take subtyping as antecedents.


#### Subset types

[[rules]](rules.html#subset-types)

The subset type `{ x : A | B }` contains all the elements `M : A` such
that `[M / x]B` is inhabited.  This is different from the dependent
sum `exists (x : A) . B` in that the subset type does not retain the
proof of `B`.  For example, the elements of `{ x : nat | is_even(x) }`
are just numbers, while the elements of 
`exists (x : nat) . is_even(x)` are pairs of numbers and proofs.

Destructing `x : { x : A | B }` produces `x : A` and `y : B`, but
since the proof of `B` is not retained, the `y` hypothesis must be
[*hidden*](#hypotheses) to ensure that it is not used in the extract.

Equality of subset types is strong as regards the type, but weak as
regards the predicate.  For `{ x : A | B }` to be equal to 
`{ x : C | D }`, we must have that `A` and `C` are equal types, but
`B` and `D` merely need to imply each other.  This is usually
convenient as it makes subset types much more likely to be equal, but
a less-desirable consequence is that we cannot conclude from
`{ x : A | B } = { x : A | C } : type` that `x : A |- B = C : type`.
A special case of this is we cannot conclude from 
`{ x : A | B } : type` that `x : A |- B : type`, and that means that
eliminating a subset-type hypothesis must usually generate a subgoal
to ensure the predicate is well-formed.

A variation on the subset type (the *intensional* subset type) chooses
the other side of the tradeoff.  For `iset (x : A) . B` to equal
`iset (x : C) . D` requires that `B` and `D` be equal, and not
merely imply each other.  This allows one to conclude 
`x : A |- B : type` from `iset (x : A) . B : type`, which allows us to
eliminate a premise in some rules.  Intensional subset types are less
useful for most purposes due to their restricted equality, but
they are occasionally preferable due to their streamlined inference
rules.  Istari uses them internally in its treatment of datatypes.

A degenerate form of the subset type that is often useful is the
squash type: `{ A }` is defined to mean `{ _ : unit | A }`.  The
squashed type `{ A }` is inhabited (by `()`) exactly when `A` is
inhabited, but one can prove a squash type without computational
access to the evidence, as might happen for example if the evidence is
in a hidden hypothesis.

Also observe that `{ A }` is equal to `{ B }` whenever `A` and `B`
imply each other.  This means that the squash type collapses all
inhabited types to a single type, which is useful for some purposes.


#### Quotient types

[[rules]](rules.html#quotient-types)

The quotient type `quotient (x y : A) . B` coarsens the equality of
`A`.  In the quotient type, `M` and `N` are equal whenever 
`[M / x, N / y]B` is inhabited.

For the type `quotient (x y : A) . B` to be well-formed, we need `A`
and `B` to be well-formed, but we also need `B` to be symmetric and
transitive in an appropriate sense.  We do not require `B` to be
reflexive, so the quotient type could fail to contain some elements of
`A`.

The laws of functionality mean that some extra work must be done when
eliminating a quotient type.  To show that `f` belongs to 
`(quotient (x y : A) . B) -> C`, one must not only show that `f`
produces a `C` for every argument in `A`, but that it produces the
*same* `C` for arguments that are equivalent according to `B`.


#### Impredicative quantification

[[rules]](rules.html#impredicative-universals)

Universal and existential quantification enjoy impredicative versions,
which might be written `iforall i (t : A) . B` and 
`iexists i (t : A) . B`.  (In the implementation, the `i` is kept
implicit; it is not displayed and it is inferred automaticaly.)  In
each, `A` must be a kind belonging to `K(i)` and `B` must be a type
belonging to `U(i)`.  Then each belongs to `U(i)`.  In contrast, if
the usual predicative quantification were used, then each would belong
to `U(1 + i)`, since `A` would belong to `U(1 + i)`, not `U(i)`.

The impredicative universal is like an intersection type in that the
argument `t` is not passed as an argument to the "function."  This is
because impredicative quantification relies on the function being
*parametric*, but if the `t` were available to the function, it could
discriminate on it.  (In the polymorphic lambda calculus, the
dependency is typically written as a function, but there is a
syntactic separation that prevents the terms from discriminating on
types.  Istari does not have syntactic separation between types and
terms, but something similar can be accomplished using 
[proof irrelevance](proof-irrelevance.html).)

Similarly, the impredicative existential does not pair the witness `t`
with the inhabitant of `B`.  Thus, the impredicative existential is a
weak sum, like [union types](#union-types), and is subject to the same
limitations.

A related type provides impredicative polymorphism:  The type
`foralltp t . B` contains `M` if `M : [A / t]B` for every type `A`
(regardless of `A`'s universe, if any).  Like the impredicative
universal, `A` is not passed as an argument to `M`.  Impredicative
polymorphism can be used with any type regardless of universe, but it
never belongs to a universe.

For technical reasons, one cannot deduce from 
`iforall i (t : A) . B : type` that `t : A |- B : type`.  (Briefly,
constructing intentional versions of impredicative types seems to
require a form of self-reference that cannot be shown to be
well-founded.)  Consequently, eliminating impredicative types (and
introducing impredicative existentials) requires generating a subgoal
to establish that `B` is well-formed.  This makes impredicative
quantification not useful for typing lemmas, as such lemmas could only
be called when one knows the result already.

Both a level and a kind are necessary to determine a space.  This is
why the impredicative quantifiers need to mention a level, internally
at least.  In normal cases, indeed in all non-degenerate cases, the
level is uniquely determined by the kind, so it can be kept implicit.
But the type theory must include them because it is difficult to
exclude the degenerate cases, such as `rec t . future t`.


#### Integers

[[rules]](rules.html#integers)

Integers can be defined as a quotient over pairs of natural numbers:

    quotient (a b : nat & nat) . a #1 + b #2 = a #2 + b #1 : nat

This is worked out in the internals of the `Integer` library.

However, integers defined this way computationally perform very badly,
like the natural numbers they are based on.  For practical arithmetic,
Istari provides "native" integers, where native means using the bignum
library in your ML implementation.  This is native enough to achieve
tolerable performance.

Thus native integers do not exist in the semantics at all.  Instead,
the implementation supplies axioms that assert that native integers
are isomorphic to defined integers in an appropriate way.  (This relies
on the bignum implementation being correct, of course.)

The introduction form for native integers are the integer literals
(written ``z`-1``, ``z`0``, ``z`1``, ``z`2``, etc.)  An elimination
form `integer_iter` is provided by the [Integer
library](lib/integer.html), and a variety of native operations are
provided as well.


#### Symbols

[[rules]](rules.html#symbols)

Symbols are a simple base type representing impoverished strings.
Symbol literals are written like ``sym`"foo"``, and the only operation
on symbols is equality.


#### Partial types

[[rules]](rules.html#partial-types)

Partial types make it possible to express possibly non-terminating
computations [2, 6, 3].  We refer to such computations as *partial
objects*. The partial type, `partial A`, contains all the elements of
`A`, in addition to all divergent terms.  Two terms are equal at
`partial A` if they have the same halting behavior, and if they are
equal at `A` if they halt.

There are three main ways to inhabit a partial type:

- First, the canonical divergent term `bottom` (defined as 
  `fix (fn x . x)`) inhabits every partial type.

- Second, we say that a type `A` is *strict* if `A <: partial A`.
  Since `partial A` contains all the members of `A`, the only fact we
  need to say that `A` is strict is that the inclusion of `A` into
  `partial A` preserves equality.  For that to be the case, we need
  `A` not to equate any convergent term with any divergent term, since
  in `partial A` terms with different halting behavior are never
  equal.

  Most types in Istari are strict.  Indeed, most types in Istari have
  the stronger property of totality, meaning they contain *only*
  convergent terms.  Thus one may usually take members of `A` to be
  members of `partial A`.

- Third, we can create a partial object by recursion, using the
  *fixpoint induction* rule.

Given a term `F` with type `partial A -> partial A`, fixpoint
induction allows us to conclude (under certain circumstances) that
`fix F : partial A`.  Alas, this principle is available only for types
`A` that are **admissible**, and there do exist 
[non-admissible types](lib/smith-paradox.html).

Roughly speaking, a type `A` is semantically admissible if whenever
`A` contains an infinite chain of approximations to some recursive
computation `M`, it also contains `M`.  However, within the logic we
cannot reason about such chains directly and we must instead rely on a
set of rules for showing that types are admissible.  For example, 
`A -> B` is admissible whenever `B` is admissible, and `A & B` is
admissible whenever both `A` and `B` are admissible.

One major device for showing that a type is admissible is
upwards-closure.  We say that `A` is an *uptype* (short for
"upwards-closed type") if whenever `M : A` and `M` computationally
approximates `M'` then `M' : A`.  Every uptype is admissible since the
members of a chain approximate their limit.

Uptypes are a useful way to show admissibility because most types are
uptypes.  The main exceptions are partial types (`bottom` approximates
everything but partial types do not contain everything) and universes
(which can talk about membership in a partial type).

(Note that more admissibility and uptype rules could be added than
Istari currently supports.)

The type `halts M` expresses the fact that `M` halts; it is
well-formed when `M` belongs to any partial type.  If 
`M = N : partial A` and `halts M`, we can conclude that `M = N : A`.



## Additional topics

#### Pointwise functionality

The semantic meaning of the judgement `G |- A ext M` is for all
closed substitutions `s` and `s'` that are equivalent at `G`, `s(A) = s'(A) :
type` and `s(M) = s'(M) : s(A)`.  The subtle point is what it means
for two substitutions to be equivalent at a context.

(This account is a simplification of the actual Istari semantics
&mdash; for various technical reasons &mdash; but it is not misleading
for the purpose of understanding pointwise functionality.)

Suppose that `G` binds each variable at most once.  We say that `s`
and `s'` are equivalent at `G` if, for all `x` in the domain of `G`, if
`G(x)` is `A` then:

1. `x` is in the domain of `s` and `s'`
2. `s(A) = s'(A) : type`
3. `s(x) = s'(x) : s(A)`
4. `A` is **functional** in an appropriate sense

One notion of functionality, called *full functionality*, would
require that `t(A) = t'(A) : type` for any closed substitutions `t`
and `t'` that are *similar* at the context obtained by truncating `G`
immediately before `x`'s binding.  Similarity is the same as
equivalence except the functionality requirement is dropped.

Full functionality is a common requirement in mathematics, but it
turns out not to work well in this sort of type theory.  Instead, we
employ a looser notion of functionality called **pointwise**.  Note that
looser functionality means more substitutions are equivalent, and
therefore the semantics of judgements is stronger.  Thus, a theorem
proved with pointwise functionality holds true with full functionality
as well.  However, pointwise functionality provides a stronger
invariant that is useful in induction arguments.

Under pointwise functionality, we require that `s(A) = s''(A) : type`
for any `s''` that is similar to `s` (again, at the context
obtained by truncating `G` immediately before `x`'s binding).  Thus,
we require that `A` be functional not over *all pairs* of equivalent
substitutions, but merely over substitutions that are similar to
the one under consideration.

There are various ramifications to pointwise functionality, but the
most important pertains to induction.  Consider a proposed rule for
natural number induction:

    G |- [M/x]C
    >>
    G |- M : nat
    G |- [0 / x]C
    G, x:nat, y:C |- [succ x / x]C
    G, x:nat |- C : type

Consider the fourth and final premise.  It establishes that `C` is
well-formed for all natural numbers `x`.  The premise is necessary
with full functionality: without it we cannot show that there are
*any* substitutions that are equivalent at `G, x:nat, y:C`, and
without knowing that, the third premise (the inductive case) is
useless.

However, the fourth premise is a non-starter for the Istari type
theory.  In many important cases, `C` is not even well-formed unless
it is true.  Every typing lemma is an example.  (Recall the discussion
of negatability [above](#negatability).)  In such cases, it is
impossible to prove the well-formedness of `C` before proving its
truth.  Consequently, one cannot reason by induction!

Pointwise functionality allows us to scrap the fourth premise.  Since
we only need to know that `C` is functional over substitutions
equivalent to the one under consideration, we can establish that `C`
is well-formed simultaneously with its truth.  The second premise
tells us that `[0 / x]C` is well-formed and true, while the third
premise tells us that if `[n / x]C` is well-formed and true, then
`[succ n / x]C` is well-formed and true.


#### Substitution

The absence of any categorical equality in Istari has as an impact on
the substitution rule:

    G1, x : A, G2 |- B ext N
    >>
    G1, x : A, G2 |- B : type
    G1, x : A, G2 |- x = M : A
    G1, [M / x]G2 |- [M / x]B ext N

The equality in the second premise does not guarantee that we can
replace `x` with `M` in any context (as would be the case with
categorical equality), but only that `x` are `M` are equal at type
`A`.  Thus, without the first premise, Istari has no way of knowing
that `[x / x]B` is equal to `[M / x]B`.

(But note: a simpler rule applies when `x` does not appear free in
`B`, in which this issue does not arise.)

As a consequence, one cannot use substitution unless `B` is already
known to be well-formed (or `x` is not free in `B`).  This can cause a
problem when `C` is a hypothesis that is not well-formed unless it is
true, as is the case in typing lemmas.  (Recall the discussion
of negatability [above](#typing).)  Fortunately, there are usually
workarounds that do not require substitution.


#### Generalization

The generalization rule allows one to generalize occurrences of a term
in the conclusion:

    G |- [M / x]B ext [M / x]N
    >>
    G |- M : A
    G, x : A |- B ext N

But observe that the rule does not generalize occurrences of `M` in
the context.  It would be nice to have a rule that does so, such as:

    G1, [M / x]G2 |- [M / x]B ext [M / x]N
    >>
    G1 |- M : A
    G1, x : A, G2 |- B ext N

Alas, this rule is unsound.  Consider the goal `G, y : [M / x]B |- C`.
Faced with this goal, we can assume that the substitution instance 
`[M / x]B` is well-formed, but it does not follow that `B` is
well-formed for all `x : A`, even when `M : A`.  But if we proceeded
to the premise `G, x : A, y : B |- C`, that is exactly what we would
be promising.

In order to generalize in this example, we must show that `B` is
well-formed for all `x : A`.  The easiest way to do so is to move the
hypotheses that we want to generalize to the right-hand side:

    G |- [M / x]B -> C

Then we can generalize, obtaining `G, x : A |- B -> C`, and finally
reintroduce the hypothesis: `G, x : A, y : B |- C`.  That final step of
reintroducing the hypothesis generates the premise 
`G, x : A |- B : type`.

Note that the situation with generalization is opposite to that of
[substitution](#substitution).  In substitution we must generate
premises requiring the conclusion to be well-formed, while in
generalization we must generate premises requiring hypotheses to be
well-formed.


---

[1] R.L. Constable, S.F. Allen, H.M. Bromley, W.R. Cleaveland,
J.F. Cremer, R.W. Harper, D.J. Howe, T.B. Knoblock, N.P. Mendler,
P. Panangaden, J.T. Sasaki, and S.F. Smith. *Implementing Mathematics
with the Nuprl Proof Development System.* Prentice-Hall, 1986.

[2] Robert L Constable and Scott Fraser Smith. Partial Objects in
Constructive Type Theory.  In *Second IEEE Symposium on Logic in
Computer Science*. 1984.

[3] Karl Crary. *Type-Theoretic Methodology for Practical Programming
Languages*. Ph.D. dissertation, Cornell University, 1998.

[4] Per Martin-L&ouml;f. Constructive mathematics and computer
programming. In *Sixth International Congress of Logic Methodology and
Philosophy of Science,* volume 104 of *Studies in
Logic and the Foundations of Mathematics*. North-Holland, 1982.

[5] Fran&ccedil;ois Pottier. A Typed Store-Passing Translation for
General References. In *Thirty-Eighth Symposium on Principles of
Programming Languages,* 1996.

[6] Scott Fraser Smith. *Partial Objects in Type Theory*.
Ph.D. dissertation, Cornell University. 1989.
