# Datatypes

### Datatype definitions

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
for level variables.)  Next are intermediate pervasive arguments,
preceded by the `intermediate` keyword.  (There are none in the
example.)  Next are the visible pervasive arguments,
preceded by the `forall` keyword.  They are arguments to all the
datatypes and constructors.  Next is the universe to which the
datatypes belong.  In the example, the datatypes belong to the same
universe (`U i`) to which the type argument `a` belongs.

Invisible arguments are bound in both types and constructors by
`intersect`, and visible arguments are bound in both by `forall`.
Intermediate arguments are bound in types by `forall` but in
constructors by `intersect`.

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



### The iterator

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

Iterators such as this are used by the [`induction`
tactic](tactics.html#induction), which provides a simple treatment of
structural induction suitable for most (but not all) purposes.

Note that the level of the iterator's result (`U i` above) is given by
the universe in the datatype declaration.  For this reason, it is
often a good idea to define a datatype in `U i` even if the datatype
could be defined in a fixed universe such as `U 0`.  Doing the latter
would prevent using the iterator with a result type in any universe
larger than `U 0`.

The datatype definition also creates a joint iterator who names is the
first datatype's name prepended to `_iter_joint`.  For example,
`tree_iter_joint` has a type that is similar to `tree_iter` except at
the end:

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

The joint iterator gives the result of the induction for all the
datatypes, not just one of them.  This is frequently much more
useful in proofs.



### Iterator reduction

A datatype definition also creates a number of reductions involving the
iterator.  For example:

    tree_iter a P Q empcase nodecase nilcase conscase _ (Node a n x f)

reduces to:

    nodecase n x f (forest_iter a P Q empcase nodecase nilcase conscase n f)

These reductions are registered with the normalization engine and
applied automatically.  In addition, they are placed in the registry
so that users can obtain them for writing tactics.  The name is
`reduce` followed by the iterator's name, followed by the constructor's
name.  For example, the preceding reduction would be written under the
name `reduce_tree_iter_Node`.



### Strong induction and the subterm ordering

The iterators are useful only when the proposition being proved is
already known to be well-typed (specifically, to have type `U i`).
Also, they provide the induction hypothesis only on immediate
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
induction is not needed, the `induction` tactic is sufficient and much
simpler.  When the datatype definition is not mutually dependent, the
`sinduction` tactic automates this process.  Thus, the long form is
necessary only for mutually dependent datatypes when the conclusion is
not yet known to be well-typed or strong induction is required.



### Inductive functions

Calls to the datatype iterators can be difficult to read, and to write
correctly by hand.  Consider this function (from the strong induction
example) to count the number of nodes in a tree:

    tree_iter a
      (fn _ _ . nat)
      (fn _ _ . nat)
      0
      (fn _ _ _ m . (succ m))
      0
      (fn _ _ _ m1 _ m2 . Nat.plus m1 m2)

Writing this requires one to remember the order of the datatype and
the constructors, and requires one to remember that a constructor's
recursive arguments become two arguments to that constructor's
iterator arm.  To simplify reading and writing such inductive
functions, Istari provides syntactic sugar in which an inductive
function is presented as a recursive function with pattern matching:

    fnind treesize : tree [a] _ -> nat of
    | Empty . 0
    | Node _ _ f . succ (forestsize f))

    and forestsize : forest _ -> nat of
    | Nil . 0
    | Cons _ _ h t . Nat.plus (treesize h) (forestsize t)

Once elaborated, this inductive function is identical to the call to
`tree_iter` above.  Observe that the function that is defined is the
first one to appear, `treesize`.  If we wanted `forestsize` instead,
we would need give it first.

Note that this is an *inductive* function, not a recursive function.
The recursive functions `treesize` and `forestsize` can be called only
on the term's immediate subterms (`f` in the `Node` case; `h` and `t`
in the `Cons` case).  Any other use will result in an error.

The inductive function must cover every constructor, but it may do so
using wildcards, so the following is equivalent:

    fnind treesize : tree [a] _ -> nat of
    | Node _ _ f . succ (forestsize f))
    | _ . 0

    and forestsize : forest _ -> nat of
    | Cons _ _ h t . Nat.plus (treesize h) (forestsize t)
    | _ . 0

However, the inductive function need not cover every datatype in the
mutually inductive bundle.  Datatypes that are not needed can be left
out and the elaborator will fill them in with unit.

##### The type specification

In general, the type specification (*e.g.,* `tree [a] _ -> nat`
or `forest _ -> nat`) takes the form:

    forall (x : dtconst [M1 ... Mk] y1 ... ym) . T

or

    dtconst [M1 ... Mk] y1 ... ym -> T
    
The `[M1 ... Mk]` gives the iterator's visible pervasive arguments.
Since the pervasive arguments must be the same for each of the
inductive functions being defined simultaneously, they can given only
once.  They can also be left out entirely, in which case the
elaborator fills them in with evars.

The variables `x` and `yi` are bound in `T`.  The `x` binding
represents the term itself (that is, the one being iterated over).
When that binding is not needed (often it is not), the arrow form can
be used.  The `yi` bindings represent the datatype's index arguments.
The index arguments that are not needed can be replaced by underscores
(as in the `treesize` example) Moreover, the entire `y1 ... ym` can be
replaced by `__`, in which case the elaborator inserts the correct
number of underscores.

##### Pretty-printing

Calls to the iterators are rendered by the pretty-printer as inductive
functions.  This behavior can be disabled by setting `Show.sugarFnind`
to false.



### Case analyses

A particularly simple use of the datatype iterator is when no arm of
the iteration uses the inductively computed result.  This is referred
to a case analysis.  Consider this function to determine whether a
`t : tree a n` is empty:

    tree_iter a
      (fn _ _ . bool)
      (fn _ _ . unit)
      true
      (fn _ _ _ _ . false)
      ()
      (fn _ _ _ _ _ _ . ())
      n t

This can be written as an inductive function call as:

    (fnind isempty : tree __ -> bool of
     | Empty . true
     | Node _ _ _ . false)
    n t

But Istari offers an even-more-succinct syntactic sugar for case
analyses:

    case t : tree of
    | Empty . true
    | Node _ _ _ . false
