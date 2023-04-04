# Theorems

One begins an Istari theorem using the `lemma` command:

    lemma "my_theorem"
    /
      forall (i : level) (a b : U i) . a -> b -> a & b
    /;

This initiates a lemma and presents the user with a goal:

    |-
    forall (i : level) (a : U i) (b : U i) . a -> b -> a & b

    1 goal (depth 0)

The current goal is just the theorem statement.  There is currently
just one goal, and are still at the top level (depth 0).

When we are presented with a single goal, we can run a tactic:

    intro /i a b x y/.

This tactic introduces five hypotheses, producing:

    i : level
    a : U i
    b : U i
    x : a
    y : b
    |-
    a & b

    1 goal (depth 0)

We still have a single goal, so we can run another tactic:

    split.

This splits the conjunction in the conclusion into two disjuncts:

    [goal 1]
    b
    
    [goal 0]
    i : level
    a : U i
    b : U i
    x : a
    y : b
    |-
    a

    2 goals (depth 0)

Now there are two goals.  The first goal (goal 0) is given in its
entirety; any remaining goals (goal 1, in this case) are abbreviated.
(One can get the all the goals unabbreviated by entering `C-c S`.)

With two goals active, we cannot apply a tactic.  First we must enter
one of the goals.  To enter the first goal, we run:

    {

(If we wanted to take the goals out of order, we could instead say
`1:{` to enter the second goal.)

Now we have one goal, with the other pushed onto the stack:

    i : level
    a : U i
    b : U i
    x : a
    y : b
    |-
    a

    1 goal (depth 1)

Observe the depth is now 1.  We can complete this goal with:

    hyp /x/.

Now we get:

    no goals (depth 1)

With no remaining goals at this level, we exit:

    }

Obtaining:

    i : level
    a : U i
    b : U i
    x : a
    y : b
    |-
    b

    1 goal (depth 0)

We can enter this goal using `{` (which we might prefer for symmetry's
sake), or we can just solve it here:

    hyp /y/.

Obtaining:

    no goals (depth 0)

With no goals at depth 0, our proof is done.  We complete the proof
using `qed`:

    qed ();

Istari replies:

    Lemma my_theorem defined.

In unusual circumstances, a qed can fail due to an infirmity in the
original lemma statement.  A discussion of how this can happen, and
how it is easily corrected appears [here](theorem-infirmity.html).



### Rationale

Istari is stricter in its goal management than some other proof
assistants.  In those, one can apply a tactic whenever there is at
least one goal.  If there are more than one, the tactic is applied to
the first goal.

The looser approach in other proof assistants means less overhead in
goal management.  In the limit, one never needs to use `{` or `}`.
However, it makes proof maintenance more difficult:

Suppose something changes, and as a result a tactic fails to discharge
all the obligations it used to discharge.  Thus, the tactic generates
an extra subgoal.  At some later point in the proof script, a tactic
is applied to that goal that was intended for some different goal, and
presumably fails.  Worse, if the extra goal is not first, the tactic
failure is much later than the problem that caused it.

Istari's goal management keeps tactic code better correlated with the
subgoals.  A tactic that generates two goals where it should generate
one, or one where it should generate zero, will result in an
error almost immediately.



### Other prover utilities

- `Prover.abandon : unit -> unit`

  Abandon a proof.

- `Prover.pull : int -> unit`

  Make goal n into the first goal.

- `Prover.push : int -> unit`

  Make the first goal into goal n.

- `Prover.reorder : Message.label Reorder.reordering -> unit`

  [Reorder](reordering.html) the goals.

- `Prover.show : unit -> unit`

  Redisplay the current goals.

- `Prover.showFull : unit -> unit`

  Redisplay the current goals, all unabbreviated.

- `Prover.alwaysShowFull : bool ref`

  When true, `Prover.show` acts as `Prover.showFull`.

- `Prover.showLiteral : unit -> unit`

  Show the current goals with all pretty-printing disabled, including
  the rendering of de Bruijn indices as names.

- `Prover.parseCurr : ETerm.eterm -> Term.term`

  Parse the term using the current context to resolve free variables.

  + `parseCurr /[term]/`

    As above.

- `Prover.showCurr : Term.term -> unit`

  Display the term, using the current context to name variables.

