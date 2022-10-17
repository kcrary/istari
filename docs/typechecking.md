# Typechecking

Typechecking for the Istari logic is undecidable, so typechecking is
necessarily *best effort*.  The typechecker should generally work
well, provided the terms:

1. use only constants whose types are known,

2. are kept in beta-normal form,

3. do not require establishing non-trivial facts (including
equalities) to typecheck, and

4. do not entail ambiguous typing constraints.


##### Ambiguous constraints

Proviso #4 requires some elaboration.  Ambiguous typing constraints
will be avoided if all type arguments are supplied.  When type
arguments are omitted, Istari will create evars for those arguments,
and resolve them using higher-order unification.  To make higher-order
unification practical, Istari employs the *pattern fragment*.  An evar
is in the pattern fragment when it is applied to (or substituted into
using) distinct variables.  For example, `E x y` is in the pattern
fragment, but `E x x`, `E x (f x)` and `E x E'` are not.

Non-pattern evars arise most frequently when one substitutes into an
evar.  For example, suppose `f : forall (x : A) . E` and `f M` is used
where a `B` is expected.  This creates a constraint equating `[M / x]
E` with `B`, but the former is not in the pattern fragment.  In such a
case, the typechecker defers the constraint, in hopes that some other
constraint will resolve `E`.  If that does not happen, an ambiguous
constraint is reported.


##### Coping strategies

When typechecking fails, there are some strategies that can be
employed.

- In the difficulty results from a recalcitrant subterm, one can
  establish its type manually, and leave it as a hypothesis.  The
  typechecker will use that hypothesis when the term arises.  One can
  even use a hypothesis that itself has subterms, such as:

      forall (x : A) . (f x : B)

- If a fact needed for typechecking is available in a current
  hypothesis, it will similarly be used.

- Another way to deal with a recalcitrant subterm is to make it for
  manual typechecking.  The constant `manual` is the identity (*i.e.,*
  `manual M` = `M`), but the typechecker sets aside any typechecking
  obligation for a manual term.  Thus, if one wishes to leave `M` out
  of typechecking, one can first run:

      fold /manual M/

- To avoid ambiguous typing constraints, one sometimes needs to supply
  explicit arguments.  If the argument is explicit, this is just a
  matter of supplying it instead of using `_`.  If the argument is
  implicit, one must precede the function with a tick (`` ` ``) to
  make its arguments explicit.

  If the argument is not just implicit but **invisible** (*i.e.,*
  arising from `intersect`, `foralltp`, or `guard`), it cannot be made
  explicit using a tick.  In such cases, one can supply the argument
  using *visibilized application*.  For example, if:

      f : intersect (i : level) . A

  and it is necessary to give `f`'s level explicitly, one can say:

      f ap lev

  which will have type `[lev / i] A`.  The term `f ap lev` unfolds to
  just `f`, so `ap` can be folded into existence like `manual`.

- One can annotate a path (say `f x y`) with an explicit type by
  writing:

      f x y :> A

  Like `ap`, this unfolds to just `f x y`, so an annotation can be
  folded into existence.




### The algorithm

A typecheckable proposition has one of the following forms:

- `M : C`

- `C : type`

- `C <: C'`

- `C = C' : type`

- `C = C' : U i`

- `C = C' : K i`

The typecheck seeks to prove typecheckable propositions.  In addition,
the typechecker will attempt to discharge level constraints (`i <l=
j`), and positivity requirements for inductive types (`positive (fn t
. M)`).

The algorithm proceeds as follows:

##### Typing

For goals of the form `M : A`, put `M` in basic whnf, and put `A` in
hard whnf.  (See below.)  Then:

1. If `A` is `level` and `M` is an evar, set the goal aside for the level solver.

2. If `M` is unknown, defer.

3. If `M` has the form `manual M'`, generate a subgoal and stop.

4. If the goal matches a hypothesis, use it.

5. If `M` is a variable, attempt to unify its type with `A`, unless
   its type is a universe.  (This is not quite a special case of 8,
   since `A` might be intersect, etc.)

6. If `A` is known, use any applicable intro or formation rule.

7. If `M` is `let`, use the let rule.  (We don't treat this as a
   normal constant because we don't want to require that the bound
   term's type belongs to a universe.)

   If M is `letnext`, use the nondependent letnext rule.  (The special
   typing aspects of letnext mean that we cannot handle it the same
   way as other open-scope elim forms.)

8. If `M` is a path then:

   a. Infer the natural type for `M`, say `B`.

   b. If `M`'s natural type cannot be inferred because a prefix of
      its type is an evar, defer.

   c. If `B` is not of the form `U i`, attempt to unify `A` and `B`.
      (Special case of d, but avoids extra subgoals.)

   d. Prove `B` <: `A`.

9. Reject


##### Type formation

For goals of the form `A : type`, put `A` in basic whnf.  Then:

1. If `A` is unknown, defer.

2. If `A` has the form `manual A'`, generate a subgoal and stop.

3. If the goal matches a hypothesis, use it.

4. If `A` is a variable and its sort is type or `U i` then accept.

5. If `A` is known, use any applicable formation rule.

6. Prove `A : U i` for fresh `i`.


##### Subtyping

For goals of the form `A <: B`, put `A` and `B` in hard whnf.  Then:

1. If `B` is `U i`, then:

   a. Attempt to unify `A` with `U j`, for fresh `j`.
      
   b. Prove `j <l= i` and `i, j : level`.

2. Unify `A` and `B` if possible.  If successful, prove `A : type`.

   **Note:** This means subtyping is resolved using the "greedy
   algorithm" when possible.  This usually performs well in practice,
   but occasionally it can have unpredictable results.

3. If the goal matches a hypothesis, use it.

4. Use any applicable subtyping rule.

5. Prove `A = B : type`.


##### Type equivalence

For goals of the form `A = B : type`, put `A` and `B` in hard whnf.  Then:

1. Unify `A` and `B` if possible.  If successful, prove `A : type`.

2. If the goal matches a hypothesis, use it.

3. Use any applicable type equality rule.

4. Prove `A = B : U i` for unknown `i`.


##### Equality at a universe

For goals of the form `A = B : U i` or `A = B : K i`, put `A` and `B`
in hard whnf.  Then:

1. Unify `A` and `B` if possible.  If successful, prove `A : U i` or
`A : K i`.

2. If the goal matches a hypothesis, use it.

3. Use any applicable type equality rule.

4. Try compatibility.

5. Reject.


##### Reduction strategies

Three strategies are used for normalization, depending on the context:

1. Standard reduction (used by unification)

   - Utilizes user-defined reductions.
   - Never unfolds soft or firm constants.

2. Hard reduction (used in some typechecking circumstances, and many tactics)

   - Utilizes user-defined reductions.
   - Always unfolds soft or firm constants.

3. Basic reduction (used in some typchecking circumstances)

   - Never utilizes user-defined reductions.
   - Always unfolds soft constants.
   - Never unfolds firm constants.

   In other words, basic reduction unfolds soft head constants, but
   otherwise does only the minimum to put a term into whnf.  To do
   more might remove vital type annotations expressed using firm
   constants.
