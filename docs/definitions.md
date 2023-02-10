# Definitions

### Basic definitions

To define a constant, one may use the `define` command:

    define /double/
    / fn x . x + x /
    / nat -> nat /;

The first argument is the constant being defined, the second gives the
definition, and the third gives its type.  Istari will then begin a
proof wherein you can prove that `double` has the type `nat -> nat`.

You can also define a constant that takes arguments.  For example, the
same definition could be written:

    define /double x/
    / x + x /
    / nat -> nat /;

Note that the type argument is unchanged from before; it is the type
of `double`, not the type of `double x`.


##### Implicit arguments

A definition can also take **implicit arguments**, such as:

    define /double_list {a} l/
    / ` append a l l /
    / intersect (i : level) . forall (a : U i) . list a -> list a /;

Here `a` is an implicit argument.  Whenever `double_list` is used, the
parser will insert evars for each implicit argument.  One can suppress
the insertion of implicit arguments using the tick symbol (`` ` ``).

In the example, tick is used to suppress the implicit argument of
`append`, allowing us to specify it explicitly.


##### Raw definitions

One can also define a constant without a type, using the command
`defineRaw`.  Then, if desired, one can attach a type to the constant
after the fact using by proving a typing lemma and attaching it using
`recordTyping`:

    lemma "double_type"
    / double : nat -> nat /;

    ... do the proof ...

    qed ();
    recordTyping "double_type";

There is a hazard to using raw definitions: Constant definitions are
not permitted to contain evars.  With an ordinary definition, any
evars (such as those arising from calling functions with implicit
arguments) would typically be instantiated in the course of
establishing the constant's type.  But in a raw definition one must be
sure to avoid creating evars.



### Recursive definitions

One can define a recursive function using a regular definition and
`fix`, but Istari offers a more convenient syntax:

    definerec /length {a} l/
    / list_case l 0 (fn h t . succ (length a t)) /
    / intersect (i : level) . forall (a : U i) . list a -> nat /;

Note that `length`'s implicit argument `a` is still explicit during
the definition.

A recursive definition not only creates the constant, it also creates
an unrolling rewrite.  If one uses the `unfold` rewrite on (say)
`` ` length a l``, one gets the underlying fixpoint term:

    fix (fn length1 a l . list_case l 0 (fn h t . succ (length1 a t))) a l

but using `unroll` results in a much cleaner term:

    list_case l 0 (fn h t . succ (` length a t))

One can also make recursive definitions without a type using the
command `definerecRaw`, subject to the same hazard discussed above.



### Datatypes

One defines datatypes with the `typedef` command.  For example:

    typedef
    /
      datatype
        intersect (i : level) .
        forall (a : U i) .
        U i
      of
        tree : nat -> type =
        | Empty : tree 0
        | Node : forall (n : nat) . a -> forest n -> tree (succ n)
        and
        forest : nat -> type =
        | Nil : forest 0
        | Cons : forall (m n : nat) . tree m -> forest n -> forest (m + n)
    /;

A datatype definition begins with "invisible" pervasive arguments
preceded by the `intersect` keyword.  They are `intersect`-bound in
the types of the datatypes and constructors.  (This is typically used
for level variables.)  Next are the visible pervasive arguments,
preceded by the `forall` keyword.  They are arguments to all the
datatypes and constructors.  Next is the universe to which the
datatypes belong.  In the example, the datatypes belong to the same
universe (`U i`) to which the type argument `a` belongs.

Next are the datatype and their constructors.  Each datatype can take
additional "index" arguments.  In the example, both datatypes take
`nat`.  Thus, they each have the type:

    intersect (i : level) . forall (a : U i) . nat -> U i

The constructors can take "external" and "internal" arguments.  The
external argument's types are unrestricted, except they cannot mention
the datatypes being defined.  The internal argument's types must be
the datatypes being defined.  External arguments can be dependent (as
in `m` and `n` in the example), but internal arguments must be
non-dependent.

In the example, the constructors have type:

    Empty : intersect (i : level) . forall (a : U i) . tree a 0
    Node  : intersect (i : level) . forall (a : U i) (n : nat) . a -> forest a n -> tree a (succ n)
    Nil   : intersect (i : level) . forall (a : U i) . forest a 0
    Cons  : intersect (i : level) . forall (a : U i) (m n : nat) . tree a m -> forest a n -> forest a (m + n)

Defining a datatype incurs several typing obligations.  With
`typedef`, those obligations are discharged automatically by the
typechecker if possible.  With `typedefRaw` they are all handed over
to the user.


##### Iteration

In addition to the datatypes and constructors, a datatype definition
also creates several constants that are useful for induction.  For
each datatype it creates an iterator whose name is the datatype's name
prepended to `_iter`.  For example, `tree_iter` has the type:

    intersect (i : level) .
    forall 
      (a : U i)
      (P : forall (n : nat) . tree a n -> U i)
      (Q : forall (n : nat) . forest a n -> U i) .
        P 0 (Empty a)
        -> (forall (n : nat) .
              forall (x : a) .
              forall (f : forest a n) . Q n f 
              -> P (succ n) (Node a n x f))
        -> Q 0 (Nil a)
        -> (forall (m n : nat) .
              forall (t : tree a m) . P m t
              -> forall (f : forest a n) . Q n f
              -> Q (m + n) (Cons a m n t f))
        -> forall (n : nat) (t : tree a n) . P n t

Iterators such as this are used by the [`iterate` tactic](tactics.html#induction).

It also creates a joint iterator who names is the first datatype's
name prepended to `_iter_joint`.  For example, `tree_iter_joint` has a
type that is similar to `tree_iter` except at the end:

    intersect (i : level) .
    forall 
      (a : U i)
      (P : forall (n : nat) . tree a n -> U i)
      (Q : forall (n : nat) . forest a n -> U i) .
        P 0 (Empty a)
        -> (forall (n : nat) .
              forall (x : a) .
              forall (f : forest a n) . Q n f 
              -> P (succ n) (Node a n x f))
        -> Q 0 (Nil a)
        -> (forall (m n : nat) .
              forall (t : tree a m) . P m t
              -> forall (f : forest a n) . Q n f
              -> Q (m + n) (Cons a m n t f))
        -> (forall (n : nat) (t : tree a n) . P n t)
           & (forall (n : nat) (t : forest a n) . Q n t)
           & unit


##### Iterator reduction

A datatype definition also creates a number of reductions involving the
iterator.  For example:

    tree_iter a P Q empcase nodecase nilcase conscase _ (Node a n x f)

reduces to:

    nodecase n x f (forest_iter a P Q empcase nodecase nilcase conscase n f)

These reductions are registered with the normalization engine and
applied automatically.  In addition they are placed in the registry so
that users can obtain them for writing tactics.  The name is the
iterator's name prepended to the constructor's name.  For example, the
preceding reduction would be written under the name `tree_iter_Node`.


##### Strong induction

The iteration constants are useful only when the proposition being
proved is already known to be well-typed (specifically, to have type
`U i`).  Also, they provide the induction hypothesis only on immediate
subterms.  For more general induction, datatype definitions also
create a subterm orderings.

We want to have a single subterm ordering for the whole datatype
bundle, and not have n^2 orderings for n datatypes (*e.g.,* trees in
trees, trees in forests, forests in forests, forests in trees).  We
also want the subterm ordering to be insensitive to index arguments.
Thus, we define a *skeleton* type that represents the gross structure
of elements of any datatype in the bundle (using the first datatype for
the name):

    tree_skel    : intersect (i : level) . forall (a : U i) . U i

Thus the skeleton for a `tree a 3` and a `forest a 10` both have type
`tree_skel a`.

Next, the definition provides a transitive and well-founded subterm
order over skeletons:

    tree_subterm : intersect (i : level) . forall (a : U i) . tree_skel a -> tree_skel a -> U i

    tree_subterm_trans 
      : forall (i : level) (a : U i) (x y z : tree_skel a) .
          tree_subterm a x y -> tree_subterm a y z -> tree_subterm a x z

    tree_subterm_well_founded
      : forall (i : level) (a : U i) (x : tree_skel a) . Acc (tree_skel a) (tree_subterm a) x

(See the [`Acc` library module](lib/acc.html) for a discussion of the
`Acc` type.)

For each datatype there is a *strip* function that strips a datatype
down to its skeleton, such as:

    forest_strip : intersect (i : level) . forall (a : U i) (n : nat) . forest a n -> tree_skel a

Finally, for each constructor there is a subterm lemma, such as:

    Cons_subterm
      : forall (i : level) (a : U i) (m n : nat) (t : tree a m) (f : forest a n) .
          tree_subterm a (tree_strip a m t) (forest_strip (Cons a m n t f))
          & tree_subterm a (forest_strip a n f) (forest_strip (Cons a m n t f))
          & unit

For maximum clarity, the types are given above with all implicit
arguments shown.  In fact, the subterm predicate takes all pervasive
arguments (`a`, in the example) implicitly, and the strip functions
take all but the last argument implicitly.

To perform strong induction over the subterm order using these tools:

1. strip the induction variable, obtaining a skeleton,

2. use the well-foundedness lemma to show that induction variable's
   skeleton is *accessible*,

3. do induction over the accessibility hypothesis, and

4. invoke the induction hypothesis as needed, using the subterm lemmas
   to show that a subterm's skeleton is smaller than the current
   term's skeleton.

A worked example appears [here](datatype-induction.ist).  Note that
this process is usually not necessary.  In the common case in which
the conclusion is known *a priori* to be well-typed, and strong
induction is not needed, the `iterate` tactic is sufficient and much
simpler.  When the datatype definition is not mutually dependent, the
`induct` tactic automates this process.  Thus, the long form is
necessary only for mutually dependent datatypes when the conclusion is
not yet known to be well-typed or strong induction is required.



### Reductions

To define new reductions to be used automatically by the normalization
engine, one may use the `reductions` command:

    reductions
    /
      length _ (nil _) --> 0 ;
      length a (cons _ h t) --> succ (length a t) ;
      unrolling length
    /;

To establish that the specified reductions are correct, the prover
places the left- and right-hand-side into normal form and compares
them.  The `unrolling` clause indicates that, while normalizing, the
prover should unroll `length`.  One can also employ an `unfolding`
clause to indicate that the prover should unfold certain identifiers.
An `unrolling` clause will be applied only once (to avoid looping),
and only on the left-hand-side.  In contrast, an `unfolding` clause
will be applied at every opportunity.

The left-hand-sides of reductions take a special syntax: they must
consist of a constant followed by a list of arguments.  Amidst the
arguments is exactly one *principal* argument (`nil _` and `cons _ h
t` in the example).  The principal argument must be parenthesized,
even if it takes no arguments.

The right-hand-side uses the ordinary term syntax, except that
implicit arguments are not inserted.  (An evar on the right-hand-side
would never be correct.)

Note that the process of verifying reductions is purely syntactic, so
it can be sensitive to subtle changes.  For example, this variation on
the second reduction, though deceptively similar, is incorrect:

      length _ (cons a h t) --> succ (length a t) ;  (* incorrect *)

The right-hand-side of a reduction should not contain an instance of
the left-hand-side (even beneath a lambda).  Such a reduction (if
valid) *will* be accepted, but it will result in normalization
looping.  Since unification tries to avoid normalizing, the
non-terminating behavior might not arise for some time, making its
cause not obvious when it finally does.