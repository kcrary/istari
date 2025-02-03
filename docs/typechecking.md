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
unification practical, Istari employs the *relaxed pattern fragment*.
An evar is in the pattern fragment when it is applied to (or is
substituted into by) distinct variables.  For example, `E x y` is in
the pattern fragment, but `E x x`, `E x (f x)` and `E x E'` are not.
In the *relaxed* pattern fragment, evars with non-variable
arguments/substitutends are permitted, but those
arguments/substitutends are ignored.  Thus `E x (f x)` and `E x E'`
are permitted, but the solution for `E` will never use its second
argument.

Non-pattern evars arise most frequently when one substitutes into an
evar.  For example, suppose `f : forall (x : A) . E` and `f M` is used
where a `B` is expected.  This creates a constraint equating 
`[M / x] E` with `B`, but the former is not in the pattern fragment.
In such a situation, the typechecker may (depending on exactly what
`M` is) ignore the dependency on `M`, or it may defer the entire
constraint, in the hope that some other constraint will resolve `E`.
In the latter case, if no other constraint resolves `E`, an ambiguous
constraint is reported.

Additional discussion of unification can be found
[here](unification.html).


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

- Another way to deal with a recalcitrant subterm is to mark it for
  manual typechecking.  The constant `manual` is the identity (*i.e.,*
  `manual M` = `M`), but the typechecker sets aside any typechecking
  obligation for a manual expression.  Thus, if one wishes to leave
  `M` out of typechecking, one can first run:

      fold /manual M/

  Note that `manual` is a [hard](terms.html#opacity) constant, which
  means that it survives basic and hard reduction ([see
  below](#reduction-strategies)).  In some cases the
  [firm](terms.html#opacity) variant `manualf` is preferred, which
  survives basic but not hard reduction.  For example, when a manual
  subterm propagates into a type, we might not want the occurrence in
  the type to be marked manual.  (A [soft](terms.html#opacity) variant
  also exists, but it is not useful in typechecking since typechecking
  always unfolds soft constants.)

- To avoid ambiguous typing constraints, one sometimes needs to supply
  explicit arguments.  If the argument is explicit, this is just a
  matter of supplying it instead of using `_`.  If the argument is
  implicit, one must precede the function with a tick (`` ` ``) to
  make its arguments explicit.

  If the argument is not just implicit but **invisible** (*i.e.,*
  arising from [`intersect`](type-theory.html#intersection-types),
  [`iforall`](type-theory.html#impredicative-quantification),
  [`foralltp`](type-theory.html#impredicative-quantification), or
  [`guard`](type-theory.html#guarded-types), it cannot be made
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

- One can give a type for the argument of a function by writing:

      fn (x : A) . M

  This unfolds to just `fn x . M`.



### The algorithm

A typecheckable proposition has one of the following forms:

- `M : C`

- `C : type`

- `C <: C'`

- `C = C' : type`

- `C = C' : U i`

- `C = C' : K i`

The typechecker seeks to prove typecheckable propositions.  In
addition, the typechecker will attempt to discharge level constraints
(`i <l= j`), positivity requirements for inductive types 
(`positive (fn t . A)`), and totality requirements for partial types
(`total A`).

The algorithm proceeds as follows:

##### Typing

For goals of the form `M : A`, put `M` in [basic whnf](#reduction-strategies),
and put `A` in [hard whnf](#reduction-strategies).  Then:

1. If `A` is `level` and `M` is an evar, set the goal aside for the level solver.

2. If `M` is unknown, defer.

3. If `M` or `A` is marked manual, generate a subgoal and stop.
   (We say a term is marked manual when it has the form `manual _` or
   `manualf _`.)

4. If the goal is an instance of a hypothesis, use it.

5. If `M` is a variable, attempt to unify its type with `A`, unless
   its type is a universe.  (This is not quite a special case of 8,
   since `A` might be `intersect`, etc.)

6. If `A` is known, use any applicable intro or formation rule.
   Destruct any future hypotheses that come into scope.

   If `A` = `partial A'`, use any applicable intro rule for `A'` and check that
   `A' <: partial A'`.

7. If `M` is `let`, use the let rule.  (We don't treat this as a
   normal constant because we don't want to require that the bound
   term's type belongs to a universe.)

   If M is `letnext`, use the nondependent letnext rule.  (The special
   typing aspects of letnext mean that we cannot handle it the same
   way as other open-scope elim forms.)

8. If `M` is a path then:

   a. Infer the natural type for `M`, say `B`.

   b. If `M`'s natural type cannot be inferred because a prefix of `M`
      has an evar type, suspend this goal, but process any subgoals
      that came from inferring that prefix's type.

   c. If `B` is not of the form `U i`, attempt to unify `A` and `B`.
      (Special case of d, but avoids extra subgoals.)

      **Note:** This comports with the use of the "greedy algorithm"
      to resolve subtyping.

   d. Prove `B` <: `A`.

9. Reject


##### Type formation

For goals of the form `A : type`, put `A` in 
[basic whnf](#reduction-strategies).  Then:

1. If `A` is unknown, defer.

2. If `A` is marked manual, generate a subgoal and stop.

3. If the goal is an instance of a hypothesis, use it.

4. If `A` is a variable and its sort is type or `U i` then accept.

5. If `A` is known, use any applicable formation rule.  Destruct any
   future hypotheses that come into scope.

6. Prove `A : U i` for fresh `i`.


##### Subtyping

For goals of the form `A <: B`, put `A` and `B` in 
[hard whnf](#reduction-strategies).  Then:

1. If `A` or `B` is marked manual, generate a subgoal and stop.

2. If `B` is `U i`, then:

   a. Attempt to unify `A` with `U j`, for fresh `j`.  If successful,
      prove `j <l= i` and `i, j : level`.

   b. Attempt to unify `A` with `K j`, for fresh `j`.  If successful,
      prove `1 + j <l= i` and `i, j : level`.

   c. Reject

3. Attempt to unify `A` and `B`.  If successful, prove `A : type`.

   **Note:** This means subtyping is resolved using the "greedy
   algorithm" when possible.  This usually performs well in practice,
   but occasionally it can have unpredictable results.

4. Attempt to unify B with partial A.  If successful, prove
   `A <: partial A` using a strictness rule.

5. If the goal is an instance of a hypothesis, use it.

6. Use any applicable subtyping rule.  Destruct any future
   hypotheses that come into scope.

7. Prove `A = B : type`.


##### Type equivalence

For goals of the form `A = B : type`, put `A` and `B` in 
[hard whnf](#reduction-strategies).  Then:

1. If `A` or `B` is marked manual, generate a subgoal and stop.

2. Attempt to unify `A` and `B`.  If successful, prove `A : type`.

3. If the goal is an instance of a hypothesis, use it.

4. Use any applicable type equality rule.  Destruct any future
   hypotheses that come into scope.

5. Prove `A = B : U i` for unknown `i`.


##### Equality at a universe

For goals of the form `A = B : U i` or `A = B : K i`, put `A` and `B`
in [hard whnf](#reduction-strategies).  Then:

1. If `A` or `B` is marked manual, generate a subgoal and stop.

2. Attempt to unify `A` and `B`.  If successful, prove `A : U i` or 
   `A : K i`.

3. If the goal is an instance of a hypothesis, use it.

4. Use any applicable type equality rule.  Destruct any future
   hypotheses that come into scope.

5. Try compatibility.

6. Reject.



##### Reduction strategies

Three strategies are used for normalization, depending on the context:

1. Standard reduction (used by unification)

   - Utilizes user-defined reductions.
   - Never unfolds soft, firm, or soft-strict constants.

2. Hard reduction (used in some typechecking circumstances, and many tactics)

   - Utilizes user-defined reductions.
   - Always unfolds soft, firm, and soft-strict constants.

3. Basic reduction (used in some typchecking circumstances)

   - Never utilizes user-defined reductions.
   - Always unfolds soft and soft-strict constants.
   - Never unfolds firm constants.

   In other words, basic reduction unfolds soft/soft-strict head
   constants, but otherwise does only the minimum necessary to put a
   term into whnf.  To do more might remove vital type annotations
   expressed using firm constants.


### The typechecker interface

There are six main entry points to the typechecker:

- `typecheck : tactic`

  Runs the typechecker on the current goal.

- `withTypecheck : tactic -> tactic`

  Runs the given tactic, then runs the typechecker on its subgoals.

- `withTypecheckSnd : priority tacticm -> tactic`

  Runs the given tactic, then runs the typechecker on its subgoals
  marked secondary.

- `typecheck1 : tactic`

  Runs the typechecker on the current goal, but one layer deep only.

- `inference : tactic`

  Runs the typechecker for its side-effects (to instantiate evars).
  Does not solve any goals.

- `typechecker : unit -> unit`

  Runs the typechecker on all of the current goals.


When typechecking fails to discharge a goal, it attaches a short
message (*e.g.,* `undischarged typing obligation`).  One can obtain
further information on what went wrong by asking for detail (by
calling `Prover.detail : unit -> unit` or just entering `C-c C-d` in
the UI.)

For example, if typechecker is invoked on the goal `true + 1 : nat`,
one gets back the subgoal:

    [undischarged typing obligation]
    |-
    bool = nat : U E6

    1 goal (depth 0)

Additional detail provides:

    Type error: incompatible type paths
     first: bool
    second: nat
    
    
    with history:
    [  0]  bool = nat : U E6
    [  1]  bool = nat : type
    [  2]  bool <: nat
    [  3]  true : nat
    [  4]  true + 1 : nat

First it explains where it got stuck (`bool` and `nat` don't seem to
be equal).  Then it gives a trace of the typechecker's efforts that
led to that point.  At the end of the trace (goal 4 in this case) is
the initial goal.

One can get a detailed trace of everything the typechecker does by
calling `Typecheck.trace true`.


### Old typecheckers

Improvements to the typechecker can break code.  In order to more
easily migrate to new versions of Istari, one can instruct Istari to
revert to an old version of the typechecker.  This will affect not
only the `typecheck` tactic, but every tactic that invokes the
typechecker.

The code for old typecheckers resides in `library/typecheck`.  To
select the typechecker for, say, version 1.0.1, execute:

    File.import "typecheck/1.0.1-load.iml";
    Typecheck_1_0_1.select ();

To reselect the current typechecker, execute:

    TypecheckDefault.select ();
