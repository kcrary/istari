# Rewriting

### Targets

A target indicates where a rewrite is to be applied.  Targets are
given by the grammar:

    [target]      ::= in [hyp] at [occurrences]
                      in [hyp]                   (shorthand: in hyp at 0)

    [targets]     ::= [target] ...
                      [epsilon]                  (shorthand: in concl at 0)
                      at [occurrences]           (shorthand: in concl at [occurrences])

    [occurrences] ::= [numbers]                  (rewrite indicated hit numbers)
                      pos [numbers]              (rewrite indicated term positions)
                      all                        (rewrite all hits)

In a `[short-target]` (as in reduce) the `in` can be omitted.



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

- `[M] = [N] : [A] within [captures]`

    Replace M with N.  Generate a subgoal to establish that `M = N : A`.



## Rewriting tactics

- `rewrite /[rewrite] [targets]/`

    Apply the rewrite to the indicated targets.


- `rewriteRaw /[rewrite] [targets]/`

    As `rewrite` but do not run the type checker.


- `convert [term] within [captures] [targets]`

    Replaces the target term with the specified term, if they are
    beta-equivalent.  (Finding hit numbers may be slow.)


- `convertHead [constant] -> [term] within [captures] [targets]`

    Replaces the target term (having the indicated head constant)
    with the specified term, if they are beta-equivalent.  (Cheaper
    than convert.)


- `fold [term] within [captures] [targets]`

    Folds the target term to become the specified term.  The outermost
    form of the target term must match the unfolding of the specified
    term precisely.


- `convertFold within [captures] [targets]`

    Folds the target term to become the specified term.
    (Finding hit numbers may be slow.)


- `unfold [constant/variable] [targets]`

    Unfolds a target term with the specified head constant or
    variable.


- `unfoldHead [constant/variable] [targets]`

    Unfolds the specified constant or variable.  If it is a constant,
    it ignores the constant's arity so it can be used on an incomplete
    application.  However, if the arity is nonzero the constant will
    unfold to a lambda, so it may leave beta redices if the constant
    is given any arguments.


- `roll [term] within [captures] [targets]`

    Rolls the target term to become the specified term, using (in
    reverse) the unrolling reduction given for the term's head
    constant.  The outermost form of the target term must match the
    unrolling of the specified term precisely.


- `convertRoll [term] within [captures] [targets]`

    Rolls the target term to become the specified term, using (in
    reverse) the unrolling reduction given for the term's head
    constant.  (Finding hit numbers may be slow.)


- `unroll [constant] [targets]`

    Unrolls a target term with the specified head constant, using the
    unrolling reduction given for the constant.


- `unrollType [constant] [targets]`

    Unrolls a type with the specified head constant, where that
    constant is `mu` or `rec`, or is defined using `mu` or `rec`.


- `unrollTypeUniv [constant] with [term] within [captures] [targets]`

    Unrolls a type with the specified head constant, where that
    constant is `mu` or is defined using `mu`.  Uses the given term
    as the level for the inductive variable's universe.


- `reduceUsing [reduction] [targets]`

    Applies the specified reduction.  (Finding hit numbers may be slow.)


- `unreduceUsing [reduction] with [term] within [captures] [targets]`

    Applies the reduction to the specified term to obtain a goal term.
    Replaces the goal term with the specified term.  The outermost
    form of the target term must match the goal term precisely.


- `convertUnreduceUsing [reduction] with [term] within [captures] [targets]`

    Applies the reduction to the specified term to obtain a goal term.
    Replaces the goal term with the specified term.  (Finding hit
    numbers may be slow.)


- `reduce [short-targets]`

    Put the target term into normal form.


- `whreduce [short-targets]`

    Put the target term into weak-head-normal form.



### Rewriting tools

- `testRewrite [rewrite] [targets]`

    As `rewrite`, but shows what is to be done without doing it.  Note
    that since the rewrite is not actually performed, a target like
    `at 0 0` will show the same rewrite twice.

- `showPosition [short-targets]`

    Displays the indicated term positions.
