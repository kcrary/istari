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
hits would be occurrences `0 0` (not `0 1`).  The `testRewrite` tool
(see below) can assist in counting hits.

Term positions are also counted in a pre-order, left-to-right
traversal starting at 0.  Position counts are affected by the fact
that paths are stored in spinal notation, so in `x y z`, position 0 is
`x y z`, position 1 is `y`, and position 2 is `z`.  There is no
specific position for `x` or `x y`, but all rewrites will act on the
prefix of a path so 0 will do.  The `showPosition` tool (see below)
can assist in counting positions.

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
  after exploitation (see eexploit), has type `R M N` where R is a
  relation.  (Often R is equality.)  Replaces M with N.

- `<- [equation] within [captures]`

  As above but replaces N with M.

- `[term M] = [term N] : [term A] within [captures]`

  Replaces M with N.  Generates a subgoal to establish that `M = N : A`.

In the above rewrites, the term being replaced cannot have an evar
head.  That is, it must not be an evar, nor an elim starting from an
evar.



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


- `fold /[term M] within [captures] [targets]/`

  Folds the target term to become `M`.  The outermost form of the
  target term must match precisely the outermost form of the normal
  form of the unfolding of `M`.

  + `convertFold /[term M] within [captures] [targets]/`

    Folds the target term to become `M`.  (Finding hit numbers may be
    slow.)


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


- `whreduce /[short-targets]/`

  Puts the target term into weak-head-normal form.


- `reduceHard /[short-targets]/`

  Puts the target term into normal form, unfolding soft and firm constants.


- `whreduceHard /[short-targets]/`

  Puts the target term into weak-head-normal form, unfolding soft and firm constants.



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
