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
arguments) would typically (although [not
necessarily](theorem-infirmity.html)) be instantiated in the course of
establishing the constant's type.  But in a raw definition one must be
sure to avoid creating evars.


##### Varying the name

When defining a constant using `define`, the typing proof has access
to the definition using the same name.  For example:

    double = fn x . x + x
    |-
    double : nat -> nat

If `double` happens to be in scope, but it is not defined in the
current module, it is legal to shadow it.  However, it is not legal to
create a hypothesis with that name.  The form `defineVary` allows one
to use a different name within the typing proof than the one that will
be defined.  Thus:

    defineVary /double x/ /double'/
    / x + x /
    / nat -> nat /;

produces:

    double' = fn x . x + x
    |-
    double' : nat -> nat

but still defines the constant `double`.



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
command `definerecRaw`, subject to the same free evar hazard discussed
above.



### Mutually recursive definitions

One can define mutually recursive definitions using a recursive
definition of a tuple, but again Istari offers a more convenient
syntax:

    definemutrecRaw /x/
    /
      snork1 y =
        if Nat.eqb y 0 then
          x
        else
          snork2 y
    
      and
      snork2 y = snork1 (y - 1) * 2
    /;

Here, `x` is a pervasive argument that is available to all of the
mutually defined functions.  Thus `snork1` and `snork2` have the type
`nat -> nat -> nat` (although this has to be proven, of course).

The definition also creates an appropriate unrolling rewrite.  If one
uses `unroll /snork2/` on the goal:

    snork2 4 2 = 16 : nat

one obtains:

    snork1 4 (2 - 1) * 2 = 16 : nat

For mutually recursive definitions, there is only the raw version.  To
give mutually recursive definitions a type, one must prove a typing
lemma and then install it using `recordTyping`.  Again, this is
subject to the free evar hazard.


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

For more discussion of how datatypes are used, see the [datatypes page](datatypes.html).


### Reductions

To define new reductions to be used automatically by the normalization
engine, one may use the `reductions` command:

    reductions
    /
      length _ (nil) --> 0 ;
      length a (cons h t) --> succ (length a t) ;
      unrolling length
    /;

To establish that the specified reductions are correct, the prover
places the left- and right-hand-side into normal form and compares
them.  The `unrolling` clause indicates that, while normalizing, the
prover should unroll `length`.  One can also employ an `unfolding`
clause to indicate that the prover should unfold certain identifiers.
An unfolding clause will be applied at every opportunity.  In
contrast, to avoid looping, an unrolling clause will be applied only
once on any path through the syntax, and then only on the
left-hand-side.  For example, if `f` unrolls to `g`, then:

    f (f x) (f y) --> g (f x) (f y)

But:

    h (f x) (f y) --> h (g x) (g y)

(A failed use of an unrolling still counts as a use, so if `f x y`
unrolls to `g x y`, then `f (f x y)` reduces to itself, not to 
`f (g x y)`, because of the outer appearance of `f`.)

The left-hand-sides of reductions take a special syntax: they must
consist of a constant followed by a list of arguments.  Amidst the
arguments are *principal* arguments (`nil` and 
`cons h t` in the example).  The principal argument(s) must be
parenthesized, even if they take no arguments (*e.g.,* `nil`).

The right-hand-side uses the ordinary term syntax, except that
implicit arguments are not inserted.  (An evar on the right-hand-side
would never be correct.)

The right-hand-side of a reduction should not contain an instance of
the left-hand-side (even beneath a lambda).  Such a reduction (if
valid) *will* be accepted, but it will result in normalization
looping.  Since unification tries to avoid normalizing, the
non-terminating behavior might not arise for some time, making its
cause not obvious when it finally does.

##### A subtlety

Note that the process of verifying reductions is purely syntactic, so
it can be sensitive to subtle changes.  For example, consider the
correct reduction for `tree_iter` on `Node`:

    tree_iter a P Q hemp hnode hnil hcons _ (Node a' n x f) --> 
      hnode n x f (forest_iter a P Q hemp hnode hnil hcons n f)

This variation, though deceptively similar, is incorrect:

    (* incorrect *)
    tree_iter a P Q hemp hnode hnil hcons _ (Node a' n x f) --> 
      hnode n x f (forest_iter a' P Q hemp hnode hnil hcons n f)

Assuming the term is well-typed, we know that `a` and `a'` must be the
same type, but syntactically it is `a`, not `a'`, that finds its way to
the call to `forest_iter`.

##### Multiple active arguments

A reduction can more than one active argument.  For example, consider
the reductions for `leqb`, the boolean-valued less-or-equal test on
natural numbers:

    leqb (zero) _ --> true
    leqb (succ _) (zero) --> false
    leqb (succ m) (succ n) --> leqb m n

If the first argument is `zero`, the test always reduces to true.
However, if the first argument is `succ`, a second argument must be
considered.  The first active argument must be in the same position
across all `leqb`'s reductions.  The second active argument must be in
the same position across all reductions that agree on the first one,
and so on.

In this example, since the first reduction differs from the other two
in the first active argument (`zero` versus `succ`), they are not
required to agree on the location or existence of the second.
However, since the second and third reductions agree on the first
active argument, they must agree on the position (and existence) of
the second active argument.  (Internally, Istari builds a decision
tree.)


### Inductive function definitions

To define an inductive function, one can make an ordinary definition
using a [datatype iterator](datatypes.html#the-iterator).  However,
Istari provides a command to streamline the process:

    defineInd /a/
    /
      treesize : tree [a] __ -> nat of
      | Empty . 0
      | Node _ x f . succ (forestsize f)
      
      and
      forestsize : forest __ -> nat of
      | Nil . 0
      | Cons _ _ t f . treesize t + forestsize f
    /
    /
      intersect i . forall (a : U i) n . tree a n -> nat
      and
      intersect i . forall (a : U i) n . forest a n -> nat
    /;

This defines multiple inductive functions simultaneously, installs the
appropriate [reductions](#reductions), and attempts to prove the
typing lemmas.  The syntax of the inductive functions is discussed
[here](datatypes.html#inductive-functions).  (Note that the keyword
`fnind` is dropped.)

The first argument to `defInd` (in the example, `a`) gives a list of
arguments that each inductive function should take.  Those arguments
are available to the pervasive arguments (`[a]`), and to the arms of
the inductive functions (not used in this example).  The second
argument gives the inductive functions, and the third argument gives
their types, as a list separated by `and`.

In addition to installing the appropriate reductions, it writes them to
the registry.  For example:

    treesize _ _ (Empty _) --> 0

is written using the name `treesize_Empty`.
