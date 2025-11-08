# Partiality

Normally, the Istari type theory deals with total (a.k.a. terminating)
objects.  For example, the `nat` type contains only `0`, `1`, `2`,
etc.  It does not contain a divergent "bottom" term, as it does in
many languages, such as ML.  In some languages, `nat` contains even
more spurious terms, such as `succ bottom`, `succ (succ bottom)`, etc.
This strong property allows one to invoke induction for any term
belonging to `nat`, while in ML one must restrict one's attention to
values.  (If `succ bottom` is a `nat`, merely restricting to values is
not enough.)  This makes Istari more convenient for mathematical
reasoning.

Nevertheless, it is sometimes also useful to reason about partial
objects.  Istari provides two mechanisms for doing so: partial types,
and simulated partial types using guarded recursion (the
[`Eventually`](lib/eventually.html) library).  These two mechanisms
have a lot in common, but have two main differences: On the one hand,
simulated partial types are fundamentally unable to express
termination, or any idiom that depends on it.  On the other hand,
simulated partial types need not deal with the hassle of
admissibility.  In this document we consider partial types.

As a running example, we implement the "hailstone" sequence from the
Collatz conjecture.  In the hailstone sequence, any even number *n*
greater than zero is followed by *n / 2*, and any odd number greater
than one is followed by *3n + 1*.  The sequence ends if it ever
reaches zero or one.  For example: 3, 10, 5, 16, 8, 4, 2, 1.

In order to give our hailstone function an interesting return value,
it will return the number of times the hailstone sequence starting
from its argument uses the *3n + 1* case.  Thus:

    hailstone 0 = 0
    hailstone 1 = 0
    hailstone n = hailstone (n / 2)           (if n > 1 and n even)
    hailstone n = 1 + hailstone (n * 3 + 1)   (if n > 1 and n odd)

For example, `hailstone 3 = 2` (3 to 10, and 5 to 16).

It is not known whether `hailstone` terminates on every input.  Thus,
it is not known whether `hailstone` has type `nat -> nat`, but it does
have type `nat -> partial nat`.  The type `partial nat` contains all
the elements of `nat`, and it also contains all nonterminating terms.

The reader may find the full hailstone development in Istari
[here](hailstone.ist).  It may be helpful to load it into Istari and
follow along line-by-line.


#### Definition

To implement `hailstone` in Istari, we first need a helper function:

    div2 : nat -> option nat

Given an even argument *n*, `div2` returns Some of *n / 2*, and
given an odd argument `div2` returns None.

Now we can define:

    definerec /hailstone n/
    /
      if n <=? 1 then
        0
      else
        (case div2 n : option of
         | Some m . 
             hailstone m
    
         | None .
             seq x = hailstone (n * 3 + 1)
             in
               succ x)
    //
      nat -> partial nat
    /;

Note the `seq` in the None branch.  The form `seq x = M in N`
evaluates `M` first; if it reaches a value, it substitutes that value
for `x` in `N` and proceeds.  This is necessary because 
`hailstone (n * 3 + 1)` returns `partial nat`, but `succ` expects a
`nat`.  The typing rule for `seq` allows us to assume `x : nat` while
checking `succ x`.

We are now presented with the goal:

    |-
    hailstone : nat -> partial nat

At this point, one would typically take the argument `n` into scope
and use some sort of inductive argument to show that `hailstone n`
halts.  But that is not possible here.  Instead we use fixpoint
induction.  In general, fixpoint induction allows us to conclude 
`fix f : partial A` from `f : partial A -> partial A`, provided `A` is
admissible.

(Admissibility is a technical condition that says that if `A` contains
an infinite chain of finite approximations of a recursively defined
term, it also contains the chain's limit.  We will not belabor
admissibility at this time, except to mention that most types tend to
be admissible, but [not all are](lib/smith-paradox.html).)

Our goal is not immediately in the proper form for fixpoint induction,
but the `typecheckFixpoint` tactic casts it in the proper form, and
also discharges the admissibility subgoal, leaving us with:

    (fn hailstone1 n .
      if n <=? 1
      then 0
      else (fnind option_fn : forall (v0 : option [E155]) . E156 of
            | None . seq x = hailstone1 (n * 3 + 1) in succ x
            | Some m . hailstone1 m) (div2 n))
      : partial (nat -> partial nat) -> nat -> partial nat

(The `(fnind ...) (div2 n)` business is equivalent to the syntactic
sugar `(case div2 n : option of ...)`.)

This goal can be discharged automatically by `typecheck`.


#### Completeness

This defines the hailstone function, but that's not very interesting
unless we can prove facts about it.  The fact we will prove is that it
is equivalent to the following relational definition:

    typedef
    /
      datatype
        intersect (i : level) .
        U i
      of
        hailstonerel : nat -> nat -> type =
        | Stop : forall n . n <= 1 -> hailstonerel n 0
    
        | Down : 
            forall n n' x . 
              1 < n
              -> div2 n = Some n' : option nat
              -> hailstonerel n' x 
              -> hailstonerel n x
    
        | Up :
            forall n x .
              1 < n
              -> div2 n = None : option nat
              -> hailstonerel (n * 3 + 1) x
              -> hailstonerel n (succ x)
    /;

Specifically, we want to show that `hailstone n` terminates and
returns `x` exactly when `hailstonerel n x` holds.

The easier side of this proof is completeness:

    lemma "hailstone_complete"
    /
      forall n x .
        hailstonerel n x
        -> hailstone n = x : partial nat
    /;

This admits a straightforward proof by induction over the derivation
of `hailstonerel n x`.  The only interesting step in the proof is the
goal:

    x : nat
    |-
    (seq x1 = x in succ x1) = succ x : partial nat

(When presenting Istari goals, we will thin out irrelevant hypothesis
for the sake of simplicity.)

Here we can use the tactic `reduceSeq /concl/` to reduce the `seq`,
leaving us with

    [goal 1]
    x : nat
    |-
    succ x = succ x : partial nat
    
    [goal 0]
    x : nat
    |-
    halts x

Goal 1 is trivial.  Goal 0 can be discharged using the tactic
`totality`, which uses the fact that `nat` is total (*i.e.,* every
inhabitant of `nat` terminates) and `x` belongs to it.


#### Typechecking

We can state the soundness theorem as follows:

    lemma "hailstone_sound"
    /
      forall n .
        halts (hailstone n)
        -> hailstonerel n (outpar (hailstone n))
    /;

First, note the use of `outpar` in the theorem statement.  The forms
`inpar` and `outpar` are used as hints for the typechecker; `inpar`
hints that a terms of type `A` should be viewed as belonging to
`partial A`, while `outpar` does the reverse.

    inpar : intersect (i : level) (a : U i) . forall (m : a) . strict a -g> partial a
          = fn m . m

    outpar : intersect (i : level) (a : U i) . forall (m : partial a) . halts m -g> a
           = fn m . m

Both are merely the identity, so they can be folded into existence and
unfolded out of existence.

Note the provisos.  An `inpar` can be used only when the underlying
type is *strict*.  A strict type is one that does not equate any
terminating and nonterminating terms.  Most types are strict, and
strictness subgoals are usually discharged automatically by the
typechecker.

An `outpar` can be used only when the term when the term halts.  This
usually must be proven manually, but if a `halts m` hypothesis already
exists in the context, the typechecker will usually find it
automatically.

The `inpar` form is usually not necessary.  The typechecker knows that
`A <: partial A` when `A` is strict (indeed, that is the formal
definition of strictness) and can usually prove it automatically.
However, since the typechecker uses the "greedy algorithm" to resolve
unification variables, when it is presented with a goal of the form 
`M : E0` in which `M` has the type `A`, the algorithm will guess that
`E0` should be `A`.  This is usually true, but another possibility
could have been `partial A`, and when dealing with partiality
sometimes that possibility is intended.  This problem will typically
present with an unprovable subgoal `partial A = A`.  Writing `inpar M`
in place of `M` resolves the problem by forcing the typechecker to
infer that `E0` is `partial A`.

In contrast, the typechecker does not reason about termination, so the
`outpar` form *is* usually necessary if one wishes to avoid the
typechecker generating auxiliary goals.

In the soundness theorem, `hailstone` returns `partial nat` but the
second argument of `hailstonerel` is expected to be a `nat` so we
insert `outpar` to coerce it.  This generates a `halts (hailstone n)`
subgoal, but that is precisely the antecedent of the implication, so
that fact will be in the context and will be found automatically.


#### Fixpoint induction

Proving the soundness direction is more challenging than completeness.
The problem is, because of the nature of hailstone sequences, we
cannot prove the result by induction on `n`.  Instead, the assumption
`halts (hailstone n)` is what tells us that hailstone makes progress
at all, so we need somehow to leverage that termination fact into a
useful induction principle.

We do this using fixpoint induction.  Classically, fixpoint induction
is the statement: if (base case) *P (bottom)* and if (inductive case)
*P (x)* implies *P (f x)*, then *P (fix f)*, provided the predicate
*P* is admissible.  In a constructive setting, we need to state
fixpoint induction a little differently:

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

The antecedents after `f` are: admissibility of `a`,
predicate-admissibility of `P`, the base case, and the inductive case.
The limitations of admissibility and predicate admissibility are
discussed [below](#admissibility).  The base case is written:

    forall (x : partial a) . (halts x -> P x) -> P x

This is classically equivalent to `P bottom`, since all nonterminating
terms are equal at partial types, but `P bottom` is not very useful
in a constructive setting because of the undecidability of the halting
problem.


#### Soundness

Recall the soundness theorem:

    lemma "hailstone_sound"
    /
      forall n .
        halts (hailstone n)
        -> hailstonerel n (outpar (hailstone n))
    /;

First we need to change the goal slightly.  When we start fixpoint
induction, the two appearances of `hailstone` will become uncoupled,
but we still need `halts (hailstone n)` in order for 
`outpar (hailstone n)` to be well-formed.  So we change the goal to
make two copies:

    forall (n : nat) .
      halts (hailstone n)
      -> halts (hailstone n)
      -> hailstonerel n (outpar (hailstone n))

Note that the goal is not written in the proper form for fixpoint
induction, because it does not look like `P (hailstone)`.  We need to
put it in that form by abstracting over `hailstone`.

The tactic `abstractOverAt /hailstone/ /concl/ /0/` abstracts over the
first appearance of `hailstone`, giving us:

    (fn v0 .
      forall (n : nat) .
        halts (v0 n)
        -> halts (hailstone n)
        -> hailstonerel n (outpar (hailstone n)))
      hailstone

Now we are ready for fixpoint induction.  We could use the lemma, but
that involves some tedious work that we can automate.  Instead we use
the tactic:

    fixpointInduction /nat -> partial nat/ >> reduce /concl/

The argument to `fixpointInduction` is the type of `hailstone`.
(Usually, including in this case, it can be omitted and replaced by an
underscore.)  The tactic discharges the admissibility goals, and the
reduction cleans up some beta redices, resulting in two goals:

    [goal 1]
    forall (x : partial (nat -> partial nat)) .
      (forall (n : nat) .
         halts (x n)
         -> halts (hailstone n)
         -> hailstonerel n (outpar (hailstone n)))
      -> forall (n : nat) .
           halts
             (if n <=? 1
              then 0
              else (fnind option_fn : forall (v0 : option [nat]) . partial nat of
                    | None . seq x1 = x (n * 3 + 1) in succ x1
                    | Some m . x m) (div2 n))
           -> halts (hailstone n)
           -> hailstonerel n (outpar (hailstone n))
    
    [goal 0]
    forall (x : partial (nat -> partial nat)) .
      (halts x
       -> forall (n : nat) .
            halts (x n)
            -> halts (hailstone n)
            -> hailstonerel n (outpar (hailstone n)))
      -> forall (n : nat) .
           halts (x n)
           -> halts (hailstone n)
           -> hailstonerel n (outpar (hailstone n))

Reading from bottom to top, these are the base case and the inductive
case.

##### Base case

After introducing hypotheses we have:

    f : partial (nat -> partial nat)
    Hif : halts f
          -> forall (n : nat) .
               halts (f n)
               -> halts (hailstone n)
               -> hailstonerel n (outpar (hailstone n))
    n : nat
    Hhalt : halts (f n)
    Hhalthail : halts (hailstone n)
    |-
    hailstonerel n (outpar (hailstone n))

The `Hif` hypothesis gives us what we need, provided that `f` halts,
so `apply /Hif/ >> auto` gives us:

    f : partial (nat -> partial nat)
    n : nat
    Hhalt : halts (f n)
    |-
    halts f

The termination of `f` follows from the termination of `f n` (*i.e.,*
from `Hhalt`), which we can reason out using the tactic 
`termination /Hhalt/`.

##### Inductive case

After introducing hypotheses we have:

    f : partial (nat -> partial nat)
    IH : forall (n : nat) .
           halts (f n)
           -> halts (hailstone n)
           -> hailstonerel n (outpar (hailstone n))
    n : nat
    |-
    halts
      (if n <=? 1
       then 0
       else (fnind option_fn : forall (v0 : option [nat]) . partial nat of
             | None . seq x = f (n * 3 + 1) in succ x
             | Some m . f m) (div2 n))
    -> halts (hailstone n)
    -> hailstonerel n (outpar (hailstone n))

The body of `hailstone` has been unrolled in its first appearance in
the conclusion by the fixpoint induction tactic, but we need to unroll
the other two, by `unroll /hailstone at 1 0/`.  This unrolls the
second appearance, then the first.

    halts
      (if n <=? 1
       then 0
       else (fnind option_fn : forall (v0 : option [nat]) . partial nat of
             | None . seq x = f (n * 3 + 1) in succ x
             | Some m . f m) (div2 n))
    -> halts
         (if n <=? 1
          then 0
          else (fnind option_fn : forall (v0 : option [nat]) . partial nat of
                | None . seq x = hailstone (n * 3 + 1) in succ x
                | Some m . hailstone m) (div2 n))
    -> hailstonerel
         n
         (outpar
            (if n <=? 1
             then 0
             else (fnind option_fn : forall (v0 : option [nat]) . partial nat of
                   | None . seq x = hailstone (n * 3 + 1) in succ x
                   | Some m . hailstone m) (div2 n)))

Now we want to proceed by cases on whether `n` is at least 2.  The
small `n` case is easily dispensed with, leaving us with:

    f : partial (nat -> partial nat)
    IH : forall (n : nat) .
           halts (f n)
           -> halts (hailstone n)
           -> hailstonerel n (outpar (hailstone n))
    n : nat
    Hstop : not (n <= 1)
    |-
    halts ((fnind option_fn : forall (v0 : option [nat]) . partial nat of
            | None . seq x = f (n * 3 + 1) in succ x
            | Some m . f m) (div2 n))
    -> halts ((fnind option_fn : forall (v0 : option [nat]) . partial nat of
               | None . seq x = hailstone (n * 3 + 1) in succ x
               | Some m . hailstone m) (div2 n))
    -> hailstonerel
         n
         (outpar ((fnind option_fn : forall (v0 : option [nat]) . partial nat of
                   | None . seq x = hailstone (n * 3 + 1) in succ x
                   | Some m . hailstone m) (div2 n)))

Now we want to proceed by cases on whether `n` is even or odd.  We do
this by generalizing over `div2 n` and with a little bit of processing
we obtain:

    [goal 1]
    ...
    m : nat
    Heq : div2 n = Some m : option nat
    |-
    halts (f m) -> halts (hailstone m) -> hailstonerel n (outpar (hailstone m))
    
    [goal 0]
    ...
    Heq : div2 n = None : option nat
    |-
    halts (seq x = f (n * 3 + 1) in succ x)
    -> halts (seq x = hailstone (n * 3 + 1) in succ x)
    -> hailstonerel n (outpar (seq x = hailstone (n * 3 + 1) in succ x))

Reading from bottom to top, these are the odd case and the even case.
We will examine the odd case (goal 0).  The even case is similar, but
simpler.  In the odd case, after introducing hypotheses we have:

    ...
    Hhalt : halts (seq x = f (n * 3 + 1) in succ x)
    Hhalthail : halts (seq x = hailstone (n * 3 + 1) in succ x)
    |-
    hailstonerel n (outpar (seq x = hailstone (n * 3 + 1) in succ x))

From the former we can deduce `halts (f (n * 3 + 1))` using
`termination /Hhalt/`, and from the latter we can deduce 
`halts (hailstone (n * 3 + 1))`, using `termination /Hhalthail/`.
After giving the resulting hypotheses names, we have:

    ...
    Hhalt' : halts (f (n * 3 + 1))
    Hhalthail' : halts (hailstone (n * 3 + 1))
    |-
    hailstonerel n (outpar (seq x = hailstone (n * 3 + 1) in succ x))

Since `hailstone (n * 3 + 1)` terminates, we can reduce the `seq` in
the conclusion using `reduceSeq /concl/ >> auto`, obtaining:

    hailstonerel n (outpar (succ (hailstone (n * 3 + 1))))

Since `succ : nat -> nat`, we should move the conclusion's `outpar`
inward (using fold and unfold), making the conclusion:

    hailstonerel n (succ (outpar (hailstone (n * 3 + 1))))

Applying the `Up` constructor leaves two uninteresting goals, and:

    hailstonerel (n * 3 + 1) (outpar (hailstone (n * 3 + 1)))

We can finish using the induction hypothesis, the antecedents of which
(*i.e.,* `halts (f (n * 3 + 1))` and `halts (hailstone (n * 3 + 1))`)
are already known.


#### Admissibility

We can only take the fixpoint of a function 
`f : partial A -> partial A` if `A` is **admissible**.
Three concepts are relevant to establishing admissibility:

- A type *A* is **admissible** provided that if *A* contains a chain
  of finite approximations of some term *M*, then *A* also contains
  *M*.

- A type *A* is **upward closed** (a.k.a. is an **uptype**) provided
  that if *A* contains *M*, and *M* approximates *N*, then *M* and *N*
  are equal at *A*.

- A type *P* that depends on *x* : *T* is **predicate-admissible**
  provided that if *A1*, ..., *An* are substitution instances of *P*
  that form a chain of finite approximations of some type *A*, and
  each *Ai* contains *Mi* where *M1*, ..., *Mn* are a chain of finite
  approximations of some term *M*, then *A* contains *M*.

The semantic concept of approximation is not available in the Istari
logic.  As a result, none of these can be proven in Istari from first
principles.  Instead, Istari provides a variety of rules for
establishing admissibility, upward closure, and predicate
admissibility.  (Note that many more rules are semantically valid than
the implementation currently provides.)

The rules of admissibility can be summarized by the grammar:

    (admissible types)
    Aa ::= Au
         | partial Aa
         | forall (x : T) . Aa
         | forallfut (x : T) . Aa
         | T -> Aa
         | intersect (x : T) . Aa
         | intersectfut (x : T) . Aa
         | exists (x : Au) . Aa
         | exists (x : Aa) . Ap
         | Aa & Aa
         | Au &d Aa
         | Aa % Aa
         | future Aa
         | { x : Aa | Ap }      (with proviso)
         | iset (x : Aa) . Ap   (with proviso)
         | rec t . At           (t is assumed to be admissible)

    (upward-closed types, a.k.a. uptypes)
    Au ::= void
         | unit
         | bool
         | nat
         | integer
         | symbol
         | forall (x : T) . Au
         | forallfut (x : T) . Au
         | T -> Au
         | intersect (x : T) . Au
         | intersectfut (x : T) . Au
         | exists (x : Au) . Au
         | Au & Au
         | Au &d Au
         | Au % Au
         | future Au
         | M = M : T
         | M : T
         | T = T : type
         | T : type
         | T <: T
         | M <= M
         | M < M
         | halts M
         | { x : Au | Au }
         | iset (x : Au) . Au
         | mu t . Au            (t is assumed to be upward-closed)
         | rec t . Au           (t is assumed to be upward-closed)

    (predicate-admissible types)
    Ap ::= Aa                   (if Aa does not mention the dependency)
         | forall (x : T) . Ap  (if T does not mention the dependency)
         | T -> Ap              (if T does not mention the dependency)
         | halts M -> Ap
         | Ap & Ap
         | M = M : Ap

Most types are upward-closed, with the notable exception of `partial`.
Datatypes that are defined using upward-closed types will also be
upward-closed, but Istari must be
[prompted](#establishing-upward-closure) to recognize that.

A very common pattern for admissible types is something like:

    forall (x : T1) . T2 -> partial Au

Most partial functions fall into this pattern.

To prove a property of a fixpoint using fixpoint induction requires
the property to be predicate-admissible.  (This use of fixpoint
induction arises from ordinary fixpoint formation using an `exists`
type.)  A very common pattern for predicate-admissible types is
something like:

    forall (x : T) . halts M -> Aa

Here `M` can refer to the dependency, but not `T` or `Aa`.  This is
the pattern that arises when proving soundness results as illustrated
above.  For example, the following is predicate-admissible, with a
dependency on `v0 : nat -> partial nat`:

    forall (n : nat) .
      halts (v0 n)
      -> halts (hailstone n)
      -> hailstonerel n (outpar (hailstone n)))


#### Establishing upward closure

To prompt Istari to recognize that a datatype is upwards closed, we
run `establishUptype`.  For example:

    establishUptype /hailstonerel/;

If doing so fails, one can diagnose the problem by attempting manually
to prove the lemma:

    forall m n . uptype (hailstonerel m n)

Once `m` and `n` are introduced, we apply the lemma
`hailstonerel_uptype_condition`, which Istari generated automatically
when `hailstonerel` was defined.  That leaves us the goal:

    uptype (exists (v0 : nat) (v1 : v0 <= 1) . unit)
    & uptype
        (exists
           (v0 v1 v2 : nat)
           (v3 : 1 < v0)
           (v4 : div2 v0 = Some v1 : option nat) .
           unit)
    & uptype
        (exists (v0 v1 : nat) (v2 : 1 < v0) (v3 : div2 v0 = None : option nat) .
           unit)
    & unit

We can break this up into pieces, using the tactic
`Partiality.proveAdmiss` on each piece until we find the one that
fails.  (In this case, none of them will.)
