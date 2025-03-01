# Rewriting

### Targets

A target indicates where a rewrite is to be applied.  Targets are
given by the grammar:

    [target]      ::= in [hyp] at [occurrences]
                      in [hyp]                   (shorthand for: in hyp at 0)

    [targets]     ::= [target] ...
                      [epsilon]                  (shorthand for: in concl at 0)
                      at [occurrences]           (shorthand for: in concl at [occurrences])

    [occurrences] ::= [numbers]                  (rewrite the indicated hit numbers)
                      pos [numbers]              (rewrite the indicated term positions)
                      all                        (rewrite all hits)

In a `[short-target]` (as in reduce) the `in` can be omitted.

Hit numbers are counted in a pre-order, left-to-right traversal
starting at 0.  Hits are counted anew for each application, so if a
rewrite eliminates a hit, then using that rewrite on the first two
hits would be occurrences `0 0` (not `0 1`).  The `testRewrite`
[tool](#rewriting-tools) can assist in counting hits.

Term positions are also counted in a pre-order, left-to-right
traversal starting at 0.  Position counts are affected by the fact
that paths are stored in spinal notation, so in `x y z`, position 0 is
`x y z`, position 1 is `y`, and position 2 is `z`.  There is no
specific position for `x` or `x y`, but all rewrites will act on the
prefix of a path so 0 will do.  The `showPosition`
[tool](#rewriting-tools) can assist in counting positions.

When a hypothesis is rewritten, only earlier hypotheses are available
to the rewrite.  Thus, for example, a hypothetical equality can only
be used to rewrite a **later** hypothesis.  Similarly, any hypotheses
used to satisfy typing obligations that are incurred by a rewrite must
appear before the hypothesis being rewritten.



### Capturing bindings

Some rewrites take a set of binders using the syntax `within
[captures]`.  These binders are used when rewriting beneath bindings.
If n binders are supplied, the innermost n bindings are captured at
the site of a prospective rewrite, and are given the supplied names.
Those names can be used in terms that are supplied to the rewrite.

If the `within [captures]` syntax is omitted, the captures list is taken
to be empty.



### Rewrites

- `-> [equation] within [captures]`

  The equation is a term (usually a hypothesis or lemma name) which,
  after exploitation (see [eexploit](tactics.html#chaining)), has type
  `R M N` where R is a relation.  (Often R is equality.)  Replaces M
  with N.  [Intermediate matching](#matching).

  + `--> [equation] within [captures]`

    As above, but uses [strict matching](#matching).

- `<- [equation] within [captures]`

  As above but replaces N with M.  [Intermediate matching](#matching).

  + `<-- [equation] within [captures]`

    As above, but uses [strict matching](#matching).

- `[term M] = [term N] : [term A] within [captures]`

  Replaces M with N.  Generates a subgoal to establish that 
  `M = N : A`.  [Strict matching](#matching).

In the above rewrites, the term being replaced cannot have an evar
head.  That is, it must not be an evar, nor an elim starting from an
evar.

Relations supported by unaugmented Istari include `eq` (`_ = _ : _`),
`eqtp` (`_ = _ : type`), `eeqtp` (`<:>`), `subtype` (`<:`), `iff`
(`<->`), and `arrow`.  Note that arrows in an equation are interpreted
as antecedents for the relation, not as the relation itself.  Thus, to
rewrite using arrow, one should use the synonym `implies`, which
unfolds to `arrow`.  Other relations can be supported by adding to the
rewriter's weakening and compatibility tables.



## Rewriting tactics

- `rewrite /[rewrite] [targets]/`

  Applies the rewrite to the indicated targets.

  + `rewriteRaw /[rewrite] [targets]/`

    As `rewrite` but do not run the type checker.

  + `rewriteThen /[rewrite] [targets]/ [tac]`

    As `rewrite` but then run `tac` on the first subgoal.  Intended for use
    with rewrites using the equation form.


- `convert /[term M] within [captures] [targets]/`

  Replaces the target term with `M`, if they are beta-equivalent.
  (Finding hit numbers may be slow.)

  + `convertHead /[constant c] -> [term M] within [captures] [targets]/`

    Replaces the target term (having head constant `c`) with `M`, if
    they are beta-equivalent.  (Cheaper than convert.)

  + `convertIrr /[term M] within [captures] [targets]/`

    The term `M` and the target term must begin with the same
    constant.  Replaces the target term with `M` if they are
    beta-equivalent, except that the two terms can differ in the
    constant's irrelevant arguments.


- `fold /[term M] within [captures] [targets]/`

  Folds the target term to become `M`.  The outermost form of the
  target term must match precisely the outermost form of the normal
  form of the unfolding of `M`.

  + `convertFold /[term M] within [captures] [targets]/`

    Folds the target term to become `M`.  (Finding hit numbers may be
    slow.)

  + `folds [number n] /[term M] within [captures] [targets]/`

    Folds the target term `n` times to become `M`.  The outermost form
    of the target term must match precisely the outermost form of the
    normal form of the `n`th unfolding of `M`.  Useful for adding
    multiple `ap` annotations at once.  (Not very useful with multiple
    terms at once, since each use must be folded *exactly* `n` times.)


- `unfold /[constant/variable] [targets]/`

  Unfolds a target term with the specified head constant or variable,
  and then weak-head-normalizes the result.

  + `unfoldHead /[constant/variable] [targets]/`

    Unfolds a target term with the specified head constant or
    variable, but does not weak-head-normalize the result.  Thus, if
    the head takes arguments, unfoldHead will leave a beta redex.


- `roll /[term M] within [captures] [targets]/`

  Rolls the target term to become `M`, using (in reverse) the
  unrolling reduction given for the term's head constant.  The
  outermost form of the target term must match precisely the outermost
  form of the normal form of the unrolling of the specified term.

  Unrolling reductions are defined automatically for recursive
  functions defined by `definerec`.  One can establish unrolling
  reductions for other constants using:

      Database.setUnroll : constant -> Reduction.reduction -> unit

  + `convertRoll /[term M] within [captures] [targets]/`

    Rolls the target term to become `M`, using (in reverse) the
    unrolling reduction given for the term's head constant.  (Finding
    hit numbers may be slow.)


- `unroll /[constant c] [targets]/`

  Unrolls a target term with head constant `c`, using the unrolling
  reduction given for `c`.


- `unrollType /[constant c] [targets]/`

  Unrolls a type with head constant `c`, where `c` is `mu` or `rec`,
  or is defined using `mu` or `rec`.

  + `unrollTypeUniv /[constant c] with [term i] within [captures] [targets]/`

    Unrolls a type with head constant `c`, where `c` is `mu` or `rec`
    or is defined using `mu` or `rec`.  Uses `i` as the level for the
    inductive variable's universe.


- `reduceUsing /[reduction] [targets]/`

  Applies the specified reduction.  There is no syntax for reductions;
  they must be embedded using antiquotes.  (Finding hit numbers may be
  slow.)


- `unreduceUsing /[reduction] with [term M] within [captures] [targets]/`

  Applies the reduction to `M` to obtain a goal term.  Replaces a
  target term that is equivalent to the goal term with `M`.  The
  outermost form of the target term must match precisely the outermost
  form of the normal form of the goal term.

  + `convertUnreduceUsing /[reduction] with [term M] within [captures] [targets]/`

    Applies the reduction to `M` to obtain a goal term.  Replaces a
    target term that is equivalent to the goal term with `M`.
    (Finding hit numbers may be slow.)


- `reduce /[short-targets]/`

  Puts the target term into normal form.

  + `reduceParam /[hyps]/`

    Like `reduce`, but also reduces parametric application.


- `whreduce /[short-targets]/`

  Puts the target term into weak-head-normal form.


- `reduceHard /[short-targets]/`

  Puts the target term into normal form, unfolding soft, firm, and
  soft-strict constants.


- `whreduceHard /[short-targets]/`

  Puts the target term into weak-head-normal form, unfolding soft,
  firm, and soft-strict constants.


- `reduceSeq /[short-targets]/`

  Contracts occurrences of `seq x = M in N` or `seqt x = M in N` into
  `N [M / x]`.  If `M` is not valuable, the rewrite generates subgoals
  `M : E` and `total E` (where `E` is a fresh evar) for the
  typechecker to solve.
  



### Rewriting tools

- `testRewrite /[rewrite] [targets]/`

  As `rewrite`, but shows what is to be done without doing it.  Note
  that since the rewrite is not actually performed, a target like `at
  0 0` will always show the same rewrite twice.


- `showPosition /[short-targets]/`

  Displays the indicated term positions.


- `Rewrite.trace : bool ref`

  When set to true, the rewriter traces the process of propagating a
  relation through the goal.



### Matching

When the rewriter searches for terms matching its target, it employs
one of three levels of strictness:

- *Strict:* the term must match the target precisely.

- *Beta:* the term must match the target up to beta-equivalence.

- *Intermediate:* like beta, except the term and target must have the
  same head.  This cuts the search space dramatically, making
  rewriting much faster.

Rewrites using `->` and `<-` use intermediate matching, while the
variants `-->` and `<--` use strict matching.  Intermediate matching
is normally preferred because of its better flexibility, but sometimes
strict matching is preferable.  Consider the goal:

    P (0 + 1 + x)

Rewriting this goal with `-> Nat.plus_assoc` will fail, because its
target is `E1 + E2 + E3` while the goal, up to beta equivalence, is 
`P (1 + x)`.  Unification cannot uniquely solve the constraint 
`E1 + E2 = 1`.  One can resolve this by giving the arguments
explicitly, as in `-> Nat.plus_assoc 0 1 x`, but that is more verbose.

Alternatively, `--> Nat.plus_assoc` works without explicit arguments.
That is because it does not respect beta-equivalence, so each evar's
binding is uniquely determined.


### Delayed typechecking

Note that rewriting takes place before typechecking.  This can affect
what hits the rewriter finds.  For example, consider the lemma:

    min_eq_l : forall (m n : nat) . m <= n -> min m n = m : nat

Suppose `H : (x <= y)` and one rewrites using `-> min_eq_l _ _ H`.
Istari generates evars to fill in the underscores, say `E1` and `E2`.
Since typechecking has not taken place yet when the rewriter runs,
those evars have not yet unified with `x` and `y`.  Thus, the rewriter
looks for terms it can unify with `min E1 E2`, not with `min x y`.
The former could easily hit more often than the latter.

The user can account for this behavior by choosing an appropriate hit
number, or by rewriting using `-> min_eq_l x y H`.

(This behavior is intended because the user always has the option to
deal with typechecking subgoals manually, using `rewriteRaw` for
example.  It would be confusing if the rewriter behaved differently
when doing so.)
