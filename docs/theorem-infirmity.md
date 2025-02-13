# Theorem statement infirmity

A completed Istari proof never fails due to any problem in the proof
[1].  However, one *can* encounter a problem due to an infirmity in the
original theorem statement.  The only sort of infirmity that can
happen in normal use is unresolved evars.

Suppose `list_branch` has the type:

    intersect (i : level) . forall (a b : U i) . list a -> b -> (a -> list a -> b) -> b

and the first two arguments (`a` and `b`) are implicit.  Now consider
the definition:

    define /isnil {a} l/
    /
      list_branch l true (fn _ _ . false)
    //
      intersect i . forall (a : U i) . list a -> bool
    /;

Since the constant `list_branch` takes implicit arguments, the
definition really is something like:

    `list_branch E1 E0 l true (fn _ _ . false)

Ordinarily the evars are resolved in the process of proving `isnil`
has a type, but it is possible for them not to be.  We develop a proof
of the typing lemma with display of implicit arguments enabled to make
clear what is happening.

Our initial goal is:

    isnil = fn a l . list_branch E1 E0 l true (fn v0 v1 . false)
    |-
    isnil : intersect (i : E2) . forall (a : U i) . list a -> bool

We might start with `inference`.  This resolves evars in the goal as
best as it can, resulting in:

    isnil = fn a l . list_branch E1 E0 l true (fn v0 v1 . false)
    |-
    isnil : intersect (i : level) . forall (a : U i) . list a -> bool

Observe that `E2` has become `level`, but `E0` and `E1` do not appear
in the goal so they are unaffected.  Now we `unfold /isnil/`,
obtaining:

    isnil = fn a l . list_branch E1 E0 l true (fn v0 v1 . false)
    |-
    (fn a l . list_branch E1 E0 l true (fn v0 v1 . false))
      : intersect (i : level) . forall (a : U i) . list a -> bool

At this point we could simply run `typecheck`.  It would solve the
goal, resolving the evars in the process, leaving us with no problems.
However, suppose instead we proved the goal manually:

    introOf /i a l/.
    reduce //.

This gives us:

    isnil = fn a l . list_branch E1 E0 l true (fn v0 v1 . false)
    i : level
    a : U i
    l : list a
    |-
    list_branch E1 E0 l true (fn v0 v1 . false) : bool

At this point we can still run `typecheck` and have no problems.  But
suppose instead we proceed by cases on `l`.  There is no need to do
so in this proof, but in other situations there can be.

    destruct /l/ /| h t/.    

This gives us something like:

    [goal 1]
    list_branch E132 E131 (h :: t) true (fn v0 v1 . false) : bool
    
    [goal 0]
    isnil = fn a l . list_branch E132 E131 l true (fn v0 v1 . false)
    i : level
    a : U i
    |-
    list_branch E132 E131 (nil a) true (fn v0 v1 . false) : bool

Due to the vagaries of unification, the evars have been replaced by
new evars, but they are still unresolved.  Let's continue into the
first subgoal:

    isnil = fn a l . list_branch E132 E131 l true (fn v0 v1 . false)
    i : level
    a : U i
    |-
    list_branch E132 E131 (nil a) true (fn v0 v1 . false) : bool

At this point, we can reduce the goal:

    reduce //.

This is the key point that causes the problem.  It results in:

    isnil = fn a l . list_branch E132 E131 l true (fn v0 v1 . false)
    i : level
    a : U i
    |-
    true : bool

Observe that we have reduced the evars away.  If we now run the
typechecker, we still discharge the goal, but the evars in `isnil` are
unaffected!

We can prove the second goal in a similar manner and complete the
proof.  But we when enter `qed`, we get:

    Error: the term contains unresolved evars:
    
    fn a l . list_branch E132 E131 l true (fn v0 v1 . false)

    Unresolved evars: E132 E131

The evars remained unresolved at the end of the proof because we
constructed a proof in which it never mattered what those types were.
Nevertheless, before Istari will make the definition, it insists on
seeing the evars filled in [2].

In this development we had some awareness of what was happening
because we had display of implicit arguments enabled, but if they were
disabled as usual, this problem could come as a surprise.  Also, note
that the problem is *not* that we chose a bad proof strategy.  This
sort of strategy is sometimes necessary, such as for proving typing
lemmas for recursive functions.

Fortunately, solving the problem is easy.  The error message always
shows implicit arguments, even when display of implicit arguments is
disabled.  Thus, we can cut-and-paste the definition from the error
message and fill in the evars.  We wrap that with `` explicit` `` so
that implicit arguments are suppressed, then we return to the
definition and replace it with the new version:

    define /isnil {a} l/
    /
      explicit` (fn a l . list_branch a bool l true (fn v0 v1 . false))
    //
      intersect i . forall (a : U i) . list a -> bool
    /;

---

[1] Users who try to craft validations directly, instead of using
tactics, could encounter validation errors, but this cannot happen in
normal use.

[2] To avoid unsoundness, evars must be filled in before the prover
state is ever written to a file, but there is no other occasion on
which it seems reasonable to do it.
