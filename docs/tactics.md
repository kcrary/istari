# Tactics

Istari tactics have the type `tactic`; they operate on the current
goal, generating zero or more subgoals.



### Combinators

- `idtac : tactic`

  Does nothing.


- `fail : string -> tactic`

  Fails, inducing backtracking.  Takes a error string that is
  displayed to the user if it backtracks all the way to the top
  level.

  + `done : tactic`

    Like `fail` but without the stigma.  Intended for marking points where
    no subgoals are expected.


- `cut : tactic -> tactic`

  Runs the argument tactic, then prunes any backtracking points it
  creates so subsequent tactics will not backtrack into the argument
  tactic.


- `lift : (unit -> tactic) -> tactic`

  Determines the tactic only when it is time to use it.


- `andthen : tactic -> tactic -> tactic`

  The tactic `andthen tac1 tac2` runs `tac1`, then runs `tac2` on all
  its subgoals.

  A synonym is the infix operator `>>`.

  + `andthen1 : tactic -> tactic -> tactic`

    Like `andthen` but generates an error if the first tactic does not
    return exactly one subgoal.

    A synonym is the infix operator `>>+`.


- `andthenl : tactic -> tactic list -> tactic`

  The tactic `andthenl tac [tac1, ..., tacn]` runs `tac`, then runs
  `tac1` on the first subgoal, `tac2` on the second, etc.  The initial
  tactic `tac` must produce exactly n subgoals.

  A synonym is the infix operator `>>>`.

  + `andthenlPad : tactic -> tactic list -> tactic -> tactic`

    Like `andthenl` except the final tactic argument is run on all
    subgoals beyond the nth.  The initial tactic must produce at least
    n subgoals.

  + `andThenOn : int -> tactic -> tactic -> tactic`

    The tactic `andthenOn n tac1 tac2` runs `tac1`, then runs `tac2` on
    the nth subgoal.


- `andthenSeq : tactic list -> tactic`

  Runs each of the tactics in the list in sequence, combined by `andthen`.
  Similar to `foldr andthen idtac` but lazier.


- `attempt : tactic -> tactic`

  The tactic `attempt tac` applies `tac`.  If `tac` fails, the tactic
  does nothing (but succeeds).  Equivalent to `first [tac, idtac]`.


- `first : tactic list -> tactic`

  Applies each tactic in turn, until one succeeds.  If none of them
  succeed, the failure message from the last tactic is used as the
  failure message.


- `repeat : tactic -> tactic`

  The tactic `repeat tac` repeatedly applies `tac` (recursively on all
  subgoals) until it fails.


- `repeatn : int -> tactic -> tactic`

  The tactic `repeatn n tac` repeatedly applies `tac` (recursively on
  all subgoals) n times.


- `orthen : tactic -> (unit -> tactic) -> tactic`

  The tactic `orthen tac1 thunk2` applies `tac1`.  If it fails, it
  calls `thunk2` to obtain a second tactic that it then applies.
  Equivalent to `first [tac1, lift thunk2]`.  Designed to work in
  conjunction with [`do` notation](iml.html#do-bindings).


- `ifthen : tactic -> tactic -> tactic -> tactic`

  The tactic `ifthen tac1 tac2 tac3` applies `tac1`.  If it succeeds,
  it calls `tac2` on its subgoals.  If it fails, it calls `tac3`.  The
  combininator commits to its choice: `tac2` will not backtrack into
  `tac1` or `tac3`, and `tac3` will not backtrack into `tac1`.  This
  distinguishes it from `first [andthen tac1 tac2, tac3]`.



### Hypotheses

Many tactics take a hypothesis or a list of hypotheses as an argument.
Hypotheses are given by the grammar:

    Hypothesis ::= [name]
                   [number]
                   # [number]
                   \ ... antiquoted name ... \
                   # \ ... antiquoted number ... \

Hypothesis numbers count backward from the end of the context,
starting with 0.  The `#` to indicate a number is optional for literal
numbers, but it is required for antiquoted numbers.

In IML hypotheses are given by the datatype:

    datatype hypothesis = NAME of symbol | NUMBER of int

which appears in the `Hyp` structure.



### Introduction tactics

- `intro /[ipattern] ... [ipattern]/`

  Introduces the conclusion type, generating hypotheses.  Typically a
  pattern will be a simple name, but more expressive patterns are
  possible.  (See [Destruction](#destruction).)  Can introduce
  function-like types (`forall`, `->`, `-t>`, `-k>`, `intersect`,
  `iforall`, `-g>`, `foralltp`), subtypes, and let bindings.

  + `introRaw /[ipattern] ... [ipattern]/`
  
    As `intro` but does not invoke the typechecker.

  + `intros`

    Repeatedly introduces the conclusion type, generating names as
    needed.  Similar to `repeat (intro /?/)`.

  + `introsRaw`

    As `intros` but does not invoke the typechecker.


- `split`

  Introduces the conclusion type, when doing so requires no choices
  and generates no hypotheses.  Can introduce products, unit, future,
  and squash.

  + `splitn [n]`

    Calls `split` `n` times, continuing into the right-hand subgoal each time.


- `left`

  Introduces a sum in the conclusion, selecting the first disjunct.

  + `leftRaw`

    As `left` but does not invoke the typechecker.


- `right`

  Introduces a sum in the conclusion, selecting the second disjunct.

  + `rightRaw`

    As `right` but does not invoke the typechecker.


- `exists /[term]/`

  Introduces an existential in the conclusion, using the term as the
  witness.

  + `existsRaw /[term]/`

    As `exists` but does not invoke the typechecker.

  + `existses [/[term]/, ..., /[term]/]`

    Introduces several existentials in sequence, using the terms as
    the witnesses.

  + `existsesRaw [/[term]/, ..., /[term]/]`

    As `existses` but does not invoke the typechecker.


- `exact /[term M]/`

  Proves the conclusion using `M`.

  + `exactRaw /[term M]/`

    As `exact` but does not invoke the typechecker.


- `unhide`

  Unhides hidden hypotheses, when the conclusion or any hypotheses are
  computationally trivial.

  + `unhideRaw`

    As `unhide` but does not invoke the typechecker.


- `contrapositive /[hyp h]/`

  If `h`'s type is `A -> C` and the conclusion is `B -> C`, replaces `h`
  with `B` and the conclusion with `A`.  This is particularly useful
  when `C` is `void`; that is, when `h`'s type is `not A` and the
  conclusion is `not B`.

  - `contrapositiveRaw /[hyp h]/`

    As `contrapositive` but does not invoke the typechecker.


- `introOf /[ipattern] ... [ipattern]/`

  Proves a goal of the form `M : A`, where `A` is a function type
  taking at least the given number of arguments.  Typically a pattern
  will be a simple name, but more expressive patterns are possible.
  (See [Destruction](#destruction).)

  - `introOfRaw /[ipattern] ... [ipattern]/`

    As `introOf` but does not invoke the typechecker.


- `existsOf /[term M]/`

  Proves a goal of the form `N : A` where `A` is either a `union` or
  `iexists`, using `M` as the witness.
  
  + `existsOfRaw /[term M]/`

    As `existsOf` but does not invoke the typechecker.


- `splitOf`

  Proves a goal of the form `M : A` where `A` is either a `set`,
  `iset`, or `quotient`.  A little more streamlined than the action of
  `typecheck1` on such a goal.

  + `splitOfRaw`

    As `splitOf` but does not invoke the typechecker.

- `introForm /[ipattern] ... [ipattern]/`

  Proves a goal of the form `A : type` or `A : U i`, where `A`
  consists of a nested dependent type with depth at least as long as
  the given number of arguments.  (For example, 
  `forall (x : B) . exists (y : C x) . D x y` has depth 2.)
  Typically a pattern will be a simple name, but more expressive
  patterns are possible.  (See [Destruction](#destruction).)

  + `introFormRaw /[ipattern] ... [ipattern]/`

    As `introForm` but does not invoke the typechecker.



### Hypothesis tactics

- `hyp /[hyp x]/`

  Proves the current goal if `x`'s type matches the conclusion.

  + `assumption`

    Proves the current goal if any hypothesis's type matches the
    conclusion.


- `hypof`

  Proves a goal of the form `x : A`, if `x`'s type is `A`.

  + `eassumption`

    Proves a goal of the form `[evar] : A` if there exists a
    hypothesis with type `A`.

    This behavior is usually not desired if the evar is used
    elsewhere, so this is not part of the autotactic.  It is intended
    for situations in which a lemma has just been applied that has a
    non-dependent antecedent represented using `forall` instead of
    `->`.  (For example, a datatype iterator when the predicate does
    not depend on the identity of the iterated term.)


- `rename /[hyp]/ /[name]/`

  Renames the indicated hypothesis to use the indicated name.


- `reintro /[ipattern] ... [ipattern]/`

  Each pattern must be a name, `?`, or `_`.  Renames the last
  hypotheses in the context so that each hypothesis uses the supplied
  name, retains the old name if the `?` pattern is supplied, or is
  cleared if the `_` pattern is supplied.

  + `renameBefore /[ipattern] ... [ipattern]/ /[hyp x]/`

    As `reintro` except it operates on the last hypotheses that precede `x`.

  + `renameBefore /[ipattern] ... [ipattern]/ /concl/`

    Equivalent to `reintro /[ipattern] ... [ipattern]/`.

  + `renameAfter /[ipattern] ... [ipattern]/ /[hyp x]/`

    As `reintro` except it operates on the hypotheses immediately
    following `x`.


- `clear /[hyp] ... [hyp]/`

  Deletes the indicated hypotheses.

  + `weaken [m] [n]`

    Deletes hypotheses numbered `m` through `m+n-1` (counting backward from 0).

  + `clearAll`

    Deletes all hypotheses.

  + `renameOver [hyp x] [hyp y]`

    Deletes `y` and renames `x` to `y`.


- `moveBefore /[hyp] ... [hyp]/ /[target hyp]/`

  Moves the indicated hypotheses immediately before the target
  hypothesis.

  + `moveBefore /[hyp] ... [hyp]/ /concl/`

     Moves the indicated hypotheses to the end.

  + `moveBeforeDeps /[hyp] ... [hyp]/ /[target hyp]/`

    Moves the indicated hypotheses, and any hypotheses they depend on,
    immediately before the target hypothesis.  The moved hypotheses
    will appear in the same order they appeared in originally.

  + `exchange [m] [n] [p]`

    Swaps hypotheses numbered `m` through `m+n-1` with `m+n` through
    `m+n+p-1` (counting backward from 0).

  + `movePos /[hyp] ... [hyp]/ [n]`

    Moves the indicated hypotheses to position `n` (counting backward
    from 0).


- `moveAfter /[hyp] ... [hyp]/ /[target hyp]/`

  Moves the indicated hypotheses immediately after the target
  hypothesis.


- `copy /[hyp]/ /[name]/`

  Creates a copy of `hyp` using the indicated name.


- `revert /[hyp] ... [hyp]/`

  Moves the indicated hypotheses into the conclusion.

  + `revertDep /[hyp] ... [hyp]/`

    As `revert` except it uses `forall` in cases when an arrow
    would suffice.

  + `revert0 [bool]`

    Moves the last hypothesis into the conclusion.  If `bool` is true,
    then it uses `forall` when an arrow would suffice.


- `set /[name x]/ /[term M]/`

  Creates a binding of `x = M`.

  + `setFold /[name x]/ /[term M]/ /[short-targets]/`

    As `set` but also folds `M` into `x` at the indicated
    [targets](rewriting.html).  The new binding will appear
    immediately before the earliest targeted hypothesis.


- `squashHidden /[hyp] ... [hyp]/`

  Turns hidden hypotheses of `A` into an unhidden hypotheses of 
  `{ A }`.  There must be no dependencies on the hypotheses.



### Equality tactics

- `reflexivity`

  Proves a reflexivity goal, such as `M = M : A`.

  + `reflexivityRaw`

    As `reflexivity` but does not invoke the typechecker.


- `symmetry`

  Applies symmetry to the conclusion.  For example, proves `M = N : A`
  generating subgoal `N = M : A`.

  + `symmetryRaw`

    As `symmetry` but does not invoke the typechecker.


- `symmetryIn /[hyp x]/`

  Applies symmetry to the type of hypothesis `x`.

  + `symmetryInRaw /[hyp x]/`

    As `symmetry` but does not invoke the typechecker.


- `transitivity /[term M]/`

  Applies symmetry to the conclusion, using `M` as the mediating term.

  + `transitivityRaw /[term M]/`

    As `transitivity` but does not invoke the typechecker.

  + `etransitivity`

    As `transitivity` but uses an evar as the mediating term.


- `compat`

  Proves a goal of the form `h M1 ... Mn = h N1 ... Nn : A`, where `h`
  is a constant or variable, generating subgoals of the form 
  `Mi = Ni : Bi`.

  If the head `h` takes [invisible
  arguments](typechecking.html#coping-strategies), they can be
  supplied using `ap` just as in typechecking, but only in the first
  equand.

  + `compatRaw`

    As `compat` but does not invoke the typechecker.


- `injection /[hyp x]/`

  Uses injectivity on an equality in the type of `x`.  For
  example, if `x` has type `inl M = inl N : A % B`, it
  would generate the hypothesis `M = N : A`.  If the equality is
  impossible (*e.g.,* `inl M = inr N : A % B`) then it discharges the
  goal.

  + `injectionRaw /[hyp x]/`

    As `injection` but does not invoke the typechecker.


- `decompEq [n] /[term A]/`

  Proves a goal of the form `M ..spine.. = N ..spine.. : B`, where
  both spines have length `n`, generating the subgoal `M = N : A`.
  The type `B` must be appropriate to `A` and `spine`.


- `applyEq /[term F]/ /[term B]/ /[hyp x]/ /[name option y]/`

  If `x` has type `M = N : A` and `F` has type `A -> B`, generates a
  hypothesis `y` with type `F M = F N : B`.  (A name is invented if no
  name is supplied.)  If `F` is a path, `B` can usually be omitted.

  + `applyEqRaw /[term F]/ /[term B]/ /[hyp x]/ /[name option y]/`

    As `applyEq` but does not invoke the typechecker.


- `introEq /[name option] ... [name option]/`

  Proves a goal of the form `M = N : A`, decomposing one layer of `A`
  for each argument given, when `A` is `forall`, `->`, `-t>`,
  `-k>`, or `intersect`.

  The tactic first establishes `M : A` and `N : A` and preserves that
  fact throughout the process.  This can greatly reduce the number of
  secondary subgoals.  However, if `M`, `N`, or `A` is not already
  known to be well-formed, the `extensionality` tactic may be better
  suited.

  + `introEqRaw /[name option] ... [name option]/`

    As `introEq` but does not invoke the typechecker.


- `extensionalityAuto`

  Proves a goal of the form `M = N : A`, repeatedly decomposing `A` as
  long as it is `forall`, `->`, `-t>`, `-k>`, `intersect`, `exists`,
  `&`, `set`, `iset`, or various flavors of unit.  The tactic stops
  when it reaches an unsupported type, or when it reaches a type
  marked manual.  (A type is marked manual when it has the form
  `manuals _`.  The [other
  variants](typechecking.html#coping-strategies) of manual can also be
  used, but they are less useful here.)

  In addition to automating extensionality, `extensionalityAuto` first
  establishes `M : A` and `N : A` and preserves that fact throughout
  the process.  This can greatly reduce the number of secondary
  subgoals.  However, if `M`, `N`, or `A` is not already known to be
  well-formed, the `extensionality` tactic may be better suited.

  + `extensionalityAutoRaw`

     As `extensionalityAuto` but does not invoke the typechecker.


- `extensionality`

   Proves a goal of the form `M = N : A`, for many primitive types
   `A`.  Unlike `introEq` or `extensionalityAuto`, it does not
   establish `M : A` and `N : A` first, which may result in fewer or
   better subgoals if those typings are not already known.

   For equality at `union` or `iexists`, use `existsEq` instead.

   + `extensionalityRaw`

     As `extensionality` but does not invoke the typechecker.


- `existsEq /[term M]/`

  Proves a goal of the form `N = P : A` where `A` is either a `union`
  or `iexists`, using `M` as the witness.

  + `existsEqRaw /[term M]/`

     As `existsEq` but does not invoke the typechecker.   


- `univIntroEqtype`

  Proves a goal of the form `A = B : U i`, generating subgoals 
  `A = B : type`, `A : U i`, and `B : U i`.


- `ofEquands /[hyp h]/ /[name] [name]/`

  If `h` has the type `M = N : A`, generates hypotheses with the types
  `M : A` and `N : A` using the supplied names.  The second argument
  is an intro pattern, so either name can be replaced with `_` or `?`.



### Substitution

- `substitution /[hyp x]/ /[term M]/`

  Replaces occurrences of `x` with `M`.  Note that `M` must not refer
  to hypotheses after `x`.

  + `substitutionRaw /[hyp x]/ /[term M]/`

    As `substitution` but does not invoke the typechecker.


- `subst /[hyps]/`

  For each hypothesis `x` in the list: finds another hypothesis with
  type `x = M : A` or `M = x : A`, and replaces occurrences of `x`
  with `M`.

  + `substRaw /[hyps]/`

    As `subst` but does not invoke the typechecker.

  + `substStrict /[hyps]/`

    As `subst` but will not move hypotheses to make substitution
    possible.  Thus when substituting `M` for `x`, `M` must not refer
    to hypotheses after `x`.

    On rare occasions `substStrict` might work when `subst` fails,
    because `subst` might fail due to a spurious cyclic dependency
    (one that could be eliminated pruning an evar dependency).

  + `substStrictRaw /[hyps]/`

    As `substStrict` but does not invoke the typechecker.

  + `substAll`

    Carry out all available substitutions, using `subst`.  Prefers
    left-to-right when either direction is possible.

  + `substCautious /[hyps]/`

    As `subst` but will not substitute into the conclusion, and will
    never generate a proof obligation that the conclusion is
    well-formed.

  + `substCautiousRaw /[hyps]/`

    As `substCautious` but will not invoke the typechecker.

  + `substCautiousStrict /[hyps]/`

    As `substStrict` but will not substitute into the conclusion.

  + `substCautiousStrictRaw /[hyps]/`

    As `substCautiousStrict` but will not invoke the typechecker.


The substitution tactics above first attempt to use a substitution
rule that does not allow the substitution variable (*i.e.,* the
variable being substituted for) to appear in the conclusion.  If that
fails, they use a more general rule that allows it.  The former rule
is preferable, because it does not generate a proof obligation that
the conclusion is well-formed.  However, in unusual circumstances this
can result in a surprising behavior: if the conclusion mentions an
evar that might or might not depend on the substitution variable, that
possible dependency is pruned out.  More predictable behavior can be
obtained using `substCautious`, which will always prune out any
possible dependency in the conclusion.



### Type equality and subtyping tactics

- `subsume /[term A]/`

  If the conclusion is `M : B`, replaces it with `M : A`.  If the
  conclusion is `M = N : B`, replaces it with `M = N : A`.  Otherwise,
  if the conclusion is `B`, replaces it with `A`.  In any case,
  generates the subgoal `A <: B`.

  + `esubsume`

    As `subsume` but uses an evar in place of `A`.

  + `eqtp /[term A]/`

    As `subsume` but generates the subgoal `A = B : type`.

  + `eeqtp`

    As `eqtp` but uses an evar in place of `A`.


- `forceExact /[term M]/`

  If `M : A` and the conclusion is `B`, generates the subgoal `A = B :
  type`.

  + `forceExactRaw /[term M]/`

    As `forceExact` but does not invoke the typechecker to prove `M : A`.

- `tighten /[hyp x]/ /[term A]/`

  If `x` is bound with type `B`, changes its binding to `A`, provided
  `A <: B` and `x : A`.  Invokes the typechecker on the `A <: B`
  subgoal.

  + `tightenRaw /[hyp x]/ /[term A]/`

    As `tighten` but does not invoke the typechecker.



### Destruction

Destruction and other tactics use **intro patterns**, defined by the
datatype:

    datatype ipattern =
       Wild
     | Ident of Symbol.symbol option
     | And of ipattern list
     | Or of ipattern list

`Wild` discards the term being matched.  `Ident` creates a hypothesis
for the term being matched, using the indicated name (if `SOME`) or
inventing a new name (if `NONE`).  `And` breaks a conjunctive term
into component parts, matching a pattern against each of them.  `Or`
case-analyses a disjunctive term, generating a subgoal for each case,
and matching a pattern against the disjunct in each case.

The syntax for intro patterns is:

    PatternAtom ::= 0                                  (Or [])
                    _                                  (Wild)
                    ?                                  (Ident NONE)
                    [name]                             (Ident (SOME name))
                    (Pattern)
                    [PatternAtom ... PatternAtom]      (And [p1, ..., pn])
                    {PatternArm | ... | PatternArm}    (Or [p1, ..., pn])

    PatternArm  ::= PatternAtom ... PatternAtom        (And [p1, ..., pn])

    PatternSeq  ::= PatternAtom
                    PatternAtom PatternSeq             (And [p1, p2])

    Pattern     ::= PatternSeq
                    PatternSeq | Pattern               (Or [p1, p2])
                    [epsilon]                          (And [])
                    [epsilon] | Pattern                (Or [And [], p])

For example:

| Syntax              | Parses to:                              |
| ------------------- | --------------------------------------- |
| `p1 p2 p3`          | `And [p1, And [p2, p3]]`                |
| `[p1 p2 p3]`        | `And [p1, p2, p3]`                      |
| <code>p1 p2 p3 &#124; p4 &#124; p5</code>  | `Or [And [p1, And [p2, p3]], Or [p4, p5]]`        |
| <code>{p1 p2 p3 &#124; p4 &#124; p5}</code> | `Or [And [p1, p2, p3], And [p4], And [p5]]` |

The effect of the pattern match depends on the type being matched:

- Matching on a product, existential type, or set type using `p1 p2`
  (*i.e.,* `And [p1, p2]`) will split the term into its two
  components.

- Matching on a sum using `p1 | p2` (*i.e.,* `Or [p1, p2]`) will
  generate a subgoal for each disjunct.

- Matching on void using `0` (*i.e.,* `Or []`) will discharge the
  goal.

- Matching on unit (or other computationally trivial types such as
  equality) using `()` (*i.e.,* `And []`) will replace the term with
  `()`.

- Matching on future or squash using `[p]` (*i.e.,* `And [p]`) will
  match `p` against the underlying term.

- Matching on bool using `|` (*i.e.,* `Or [And [], And []]`) will
  generate subgoals for true and false.

- Matching on nat using `| p` (*i.e.,* `Or [And [], p]`) will generate
  subgoals for zero and successor.

- Matching on a list using `| p1 p2` (*i.e.,* `Or [And [], And [p1,
  p2]]`) will generate subgoals for nil and cons.  (This is a special
  case of matching on datatypes.)

- Matching on a datatype with a sum-of-products pattern `{... | ... |
  ...}` will generate a subgoal for each datatype constructor, and in
  each goal it will split the datatype construct into its arguments,
  matching on each of them.

  In addition, in each goal additional names will be bound to
  equalities that result from matching the datatype's index terms
  against its type.

- Matching against a quotient using `[p1]` or `[p1 p2]` (*i.e.,* `And
  [p1]` or `And [p1, p2]`) will match `p1` against a term of the
  underlying type, and match `p2` (if supplied) against a hypothesis
  stating that term is equivalent to itself.

- Matching against a quotient using `[p1 p2 p3]` (*i.e.,* 
  `And [p1, p2, p3]`) will match `p1` and `p2` against two terms of
  the underlying type, and match `p3` against a hypothesis stating
  that they are equivalent.  The conclusion must have the form 
  `M : A`, `M = N : A`, `A : type`, or `A = B : type`.  The resulting
  conclusion will be an equality in which the two equands refer to the
  respective equivalent terms.

The destruction tactics are:

- `destruct /[hyp x]/ /[ipattern]/`

  Destructs `x` using the intro pattern.

  + `destructRaw /[hyp x]/ /[ipattern]/`

    As `destruct` but does not invoke the typechecker.


- `assert /[term A]/ /[ipattern]/`

  Generates a subgoal to prove `A`, creates a hypothesis of type `A`,
  and matches the intro pattern against it.

  + `assertRaw /[term A]/ /[ipattern]/`

    As `assert` but does not invoke the typechecker.

  + `assertThen /[term A]/ /[ipattern]/ [tac]`

    As `assert` but then run `tac` on the first subgoal.

  + See also [`assertLater`](#miscellaneous-tactics).


- `destructSet /[hyp x]/ /[name]/`

  If `x` has type `M : { y : A | B(y) }`, replaces `x` by `M : A` and
  creates a new hypothesis (using the given name) with the type
  `B(M)`.

  + `destructSetRaw /[hyp x]/ /[name]/`

    As `destructSet` but does not invoke the typechecker.


- `destructThin /[hyp x]/ /[ipattern]/`

  Destructs `x`, discharging impossible cases and simplifying the
  resulting equations.  The pattern must be a sum of products (*i.e.,*
  `{ ... | ... }`) containing only identifers and `?`.

  The tactic can work poorly when (1) `x` is mentioned in the
  conclusion, (2) destruction generates equations that involve a
  variable, and (3) the conclusion is not already known to be
  well-formed.

  (When destruction results in `M` being substituted for `x`, and the
  simplified equations include `y = N : A` where `y` is part of `M`,
  `destructThin` invokes substitution to resolve the equation.  If `x`
  was mentioned in the original conclusion, then `y` will be mentioned
  in the post-destruction conclusion, and invoking substitution on a
  variable mentioned in the conclusion generates a proof obligation
  that the conclusion is well-formed.  Often this is fine, but it can
  be unfortunate when one cannot yet show that the conclusion is
  well-formed, such as when one is proving a typing lemma.  This
  behavior can be prevented using `destructThinCautious`, which will
  leave such equations unresolved instead.)

  + `destructThinRaw /[hyp x]/ /[ipattern]/`

    As `destructThin` but does not invoke the typechecker.

  + `destructThinCautious /[hyp x]/ /[ipattern]/`

    As `destructThin` but will not substitute into the conclusion in
    the course of resolving index equations, and will never generate a
    proof obligation that the conclusion is well-formed.  (The
    replacement of `x` by its various cases still takes place, of
    course.)

  + `destructThinCautiousRaw /[hyp x]/ /[ipattern]/`

    As `destructThinCautious` but does not invoke the typechecker.


- `inversion /[hyp x]/`

  As `destructThin` but it copies `x` and destructs the copy.  The new
  hypothesis being destructed will not appear in the conclusion, no
  hypotheses will be disturbed, and any resulting hypotheses will
  appear at the bottom.

  + `inversionRaw /[hyp x]/`

    As `inversion` but does not invoke the typechecker.


- `mimic /[hyp h]/ /[names]/`

  An ersatz substitution tactic suitable for when the conclusion is
  not yet known to be well-formed.  If `h`'s type is `x = M : A` or 
  `M = x : A` where `M`'s head is a constructor, the tactic makes `x`
  look like `M` by destructing `x` and discharging all the
  possibilities that don't look like `M`.  Will generate new variables
  for the subterms of `x`, and new equations relating those new
  variables to `M`'s subterms.  The subterm variables will be named
  using the supplied names (additional names will be invented if not
  enough are supplied) and will appear in the context where `x` was.
  The equations' names will be invented, and will appear at the
  bottom.

  Mimic will never substitute for any variable that appears in the
  conclusion.  Thus, it is suitable for situations in which the
  conclusion is not yet known to be well-formed.  If the conclusion
  *is* known to be well-formed, `subst` is always preferable.

  + `mimicRaw /[hyp]/ /[names]/`

    As `mimic` but does not invoke the typechecker.


### Chaining

- `so /[term M]/ /[ipattern]/`

  If `M` has type `A`, creates a hypothesis of type `A`, and matches
  it against the indicated pattern.  (See [Destruction](#destruction).)

  The term `M` can contain placeholders, written with two underscores
  (`__`).  Placeholder subterms result in additional subgoals.

  + `soRaw /[term M]/ /[ipattern]/`

    As `so` but does not invoke the typechecker.


- `apply /[term M]/`

  Proves the goal by backchaining through `M`.  The term may contain
  placeholders as in `so`.  Often `M` is just the name of a lemma or
  hypothesis.

  + `applyRaw /[term M]/`

    As `apply` but does not invoke the typechecker.


- `exploit /[term M]/ /[ipattern]/`

  If `M` has type `A1 -> ... -> An -> B`, generates subgoals for `A1`
  through `An`, and matches the result (of type `B`) against the
  pattern.  The term `M` may contain placeholders as in `so`.

  + `exploitRaw /[term M]/ /[ipattern]/`

    As `exploit` but does not invoke the typechecker.

  + `eexploit /[term M]/ /[ipattern]/`

    As exploit but will also proceed through `forall` quantifiers,
    instantiating them with evars.

  + `eexploitRaw /[term M]/ /[ipattern]/`

    As `eexploit` but does not invoke the typechecker.


- `witness /[term M]/`

  Proves the conclusion using `M`.  Unlike `exact`, `M` may contain
  placeholders as in `so`.

  + `witnessRaw /[term M]/`

    As `witness` but does not invoke the typechecker.



### Generalization

- `generalize /[term M]/ /[term A]/ /[name option x]/`

  If `M : A`, replaces all occurrences of `M` in the conclusion with
  a new hypothesis `x`.  (A name is invented if no name is supplied.)

  + `generalizeRaw /[term M]/ /[term A]/ /[name option x]/`

    As `generalize` but does not invoke the typechecker.

  + `generalizeAt /[term M]/ /[term A]/ /[numbers]/ /[name option x]/`

    As `generalize`, but only replaces the indicated appearances of
    `M`.  For example, if `[numbers]` is `0 2` then the first and
    third appearances of `M` are replaced.

  + `generalizeAtRaw /[term M]/ /[term A]/ /[numbers]/ /[name option x]/`

    As `generalizeAt` but does not invoke the typechecker.


- `remember /[term M]/ /[term A]/ /[name option x]/ /[name option H]/`

  If `M : A`, replaces all occurrences of `M` in the conclusion with a
  new hypothesis with `x`.  Also creates `H : (x = M : A)`.  (Names are
  invented if not supplied.)

  + `rememberRaw /[term M]/ /[term A]/ /[name option x]/ /[name option H]/`

    As `remember` but does not invoke the typechecker.

  + `rememberAt /[term M]/ /[term A]/ /[numbers]/ /[name option x]/ /[name option H]/`

    As `remember`, but only replaces the indicated appearances of
    `M`.  For example, if `[numbers]` is `0 2` then the first and
    third appearances of `M` are replaced.

  + `rememberAtRaw /[term M]/ /[term A]/ /[numbers]/ /[name option x]/ /[name option H]/`

    As `rememberAt` but does not invoke the typechecker.

  + `remember' /[term M]/ /[term A]/ /[name option x]/ /[name option H]/`

    As `remember` but reverses the direction of the equality.

  + `rememberRaw' /[term M]/ /[term A]/ /[name option x]/ /[name option H]/`

    As `rememberRaw` but reverses the direction of the equality.


- `setEq /[name x]/ /[term M]/ /[term A]/ /[name option H]/`

  If `M : A`, creates new hypotheses `x : A` and `H : (x = M : A)`.
  (The name H is invented if not supplied.)

  + `setEqRaw /[name x]/ /[term M]/ /[term A]/ /[name option H]/`

    As `setEq` but does not invoke the typechecker.

  + `setEq' /[name x]/ /[term M]/ /[term A]/ /[name option H]/`

    As `setEq` but reverses the direction of the equality.

  + `setEqRaw' /[name x]/ /[term M]/ /[term A]/ /[name option H]/`

    As `setEqRaw` but reverses the direction of the equality.


- `boolCase /[term M]/ /[name option H]/`

  If `M : bool`, replaces all occurrences of `M` in the conclusion
  with a new variable, then splits that variable into true and false
  cases.  Also creates `H : istrue M` and `H : not (istrue M)` in the
  branches and attempts to rewrite them into a useful form.  (The name
  H is invented if not supplied.)

  + `boolCaseRaw /[term M]/ /[name option H]/`

    As `boolCase` but does not invoke the typechecker.


- `boolEq [bool b] /[term M]/`

  If `M : bool`, replaces all occurences of `M` in the conclusion with
  `true` (if `b`) or `false` (if not `b`).  Generates the additional
  subgoal `istrue M` (if `b`) or `not (istrue M)` (if not `b`) and
  attempts to rewrite it into a useful form.

  + `boolEqRaw [bool b] /[term M]/`

    As `boolEq` but does not invoke the typechecker.



### Induction

- `sinduction /[hyp x]/`

  Invokes induction on `x`.  The form of the subgoals generated
  depends on `x`'s type.  This induction tactic is suitable when the
  conclusion is not already known to be a well-formed type.  For most
  types it provides strong induction (a.k.a. course-of-values
  induction), and in any case it provides the strongest induction
  available for that type.  (The strong induction on datatypes employs
  the [subterm order](datatypes.html#strong-induction-and-the-subterm-ordering).)

  + `sinductionRaw /[hyp x]/`

    As `sinduction` but does not invoke the typechecker.


- `induction /[hyp x]/`

  Invokes induction on `x` by utilizing the iterator for `x`'s type.
  The form of the subgoals generated thus depends on `x`'s type.  This
  induction tactic generally produces simpler goals than `sinduction`,
  but it is not suitable unless the typechecker can establish that the
  conclusion is a well-formed type.  In particular, it is not suitable
  for typing lemmas.

  + `inductionRaw /[hyp x]/`

    As `induction` but does not invoke the typechecker.


- `muUnivInduction /[hyp x]/ /[level i]/`

  When `x`'s type is an inductive type (*i.e.,* a `mu` type), invokes
  induction on `x`.  Unlike how `sinduction` would behave,
  `muUnivInduction` assumes that `x`'s type belongs to `U i`.  It
  generates a stronger hypothesis, but also a stronger conclusion.
  (This is useful only in unusual circumstances.)

  + `muUnivInductionRaw /[hyp x]/ /[level i]/`

    As `muUnivInduction` but does not invoke the typechecker.



### Typechecking

- `typecheck`

  If the conclusion is a typechecking goal, attempts to prove it.

  When the typechecker generates subgoals, the subgoals have
  information attached.  That information can be displayed using
  `Prover.detail ();` or using `C-c C-d` in the UI.


- `withTypecheck [tac]`

  Runs the tactic `tac`, then runs the typechecker on all resulting
  subgoals.

  + `withTypecheckSnd [tac]`

    The tactic `tac` must have type `Typecheck.priority tacticm`.
    Runs `tac`, then runs the typechecker on all resulting subgoals
    that are passed `Secondary`.

        datatype priority = Primary | Secondary


- `typecheck1`

  Runs the typechecker on the current goal for one layer only.


- `inference`

  Runs the typechecker on the current goal for its side-effects only.
  Used to instantiate evars.


- `infer /[term M]/ /[name option]/`

  If `M` is a path, proves `M : A` and creates a new hypothesis of
  that type with the given name.  (A name is invented if no name is
  supplied.)

  + `inferRaw /[term M]/ /[name option]/`

    As `infer` but does not invoke the typechecker on the path's
    arguments.

  + `inferSpine /[hyp]/ /[term N]/ /[name option]/`

    The hypothesis must have type `M : A` and `N` must have the form
    `__ [spine]`.  Proves `M spine : B` starting from `M : A`, and
    creates a new hypothesis of that type with the given name.  (A
    name is invented if no name is supplied.)  For example, if `h` has
    type `M : A & B` then `inferSpine /h/ /__ #1/ /h'/` will create a
    hypothesis `h'` with type `M #1 : A`.

  + `inferSpineRaw /[hyp]/ /[term N]/ /[name option]/`

    As `inferSpine` but does not invoke the typechecker on the spine's
    arguments.


- `typecheckLet /[hyp x]/ /[term A]/ /[name option]/`

  If `x` is a let-bound variable that unfolds to `M`, runs the
  typechecker to prove `M : A`, and creates a new hypothesis of type
  `x : A` with the given name.  (A name is invented if no name is
  supplied.)  If `M` is a path, an underscore will usually suffice for
  `A`.


- `typechecker : unit -> unit`

  Runs the typechecker on all of the current goals.

  Note that this is not a tactic, so it is invoked `typechecker ();`, not `typechecker.`


- `trivialize`

  When the conclusion is computationally trivial, sets the extract to
  some standard, closed term, usually `()`.  Leaves the goal unchanged
  except hidden hypotheses are unhidden.

  + `trivializeRaw`

    As `trivialize` but does not invoke the typechecker.


- `Typecheck.trace : bool -> unit`

  When set to true, the typechecker traces its process.



### Autotactic

- `auto`

  Attempts to prove the goal using a variety of elementary tactics,
  including backchaining through the hypotheses.  Will continue on any
  subgoals until reaching the default maximum depth (5).  If `auto`
  cannot prove the goal completely, it does nothing.

  + `nauto [n]`

    As `auto` but uses `n` as the maximum depth.

  + `autoWith /[lemma name] ... [lemma name]/`

    As `auto` but also backchains using the indicated lemmas.  If a
    "lemma" is a datatype, it backchains with all the datatype's
    constructors.

  + `nautoWith [n] /[lemma name] ... [lemma name]/`

    Combines `nauto` and `autoWith`.

  + `nautoWithRaw [n] /[lemma name] ... [lemma name]/`

    As `nautoWith` except that typechecking subgoals are set aside.
    The tactic succeds if only typechecking goals remain.  If
    primary goals would remain, the tactic does nothing.


- `existsAuto`

  Similar to `auto` but instantiates existentials with evars.

  + `existsAutoRaw`

    As `existsAuto` but does not invoke the typechecker.

  + `existsAutoWith /[lemma name] ... [lemma name]/`

    As `existsAuto` but also backchains using the indicated lemmas.
    If a "lemma" is a datatype, it backchains with all the datatype's
    constructors.

  + `existsAutoWithRaw /[lemma name] ... [lemma name]/`

    As `existsAutoWith` but does not invoke the typechecker.
  

- `autoTool /[lemma name] ... [lemma name]/`

  Backchain once, using one of the indicated lemmas.  The lemmas are
  utilized in the same fashion as `auto`.  Fails if no lemma applies.

  + `autoToolRaw /[lemma name] ... [lemma name]/`

    As `autoTool` but does not invoke the typechecker.



### Arithmetic

- `omega`

  Solves arithmetic goals using the Omega decision procedure.
  (William Pugh.  The Omega Test: a fast and practical integer
  programming algorithm for dependence analysis.  *Communications of
  the ACM,* August 1992.)

  + `omegaRaw`

    As `omega` but does not run the typechecker.

- `Omega.counterexample : unit -> unit`

  Prints a counterexample for the last invocation of Omega to fail.


Omega understands the following constants in arithmetic expressions:

- nat and integer literals (integer literals also serve as the
  literals for [natural](lib/natural.html)),

- linear arithmetic (`succ`, `plus`, `pred`, `minus`, `plusz`, `negz`,
  `minusz`, `succn`, `plusn`, `predn`, `minusn`),

- multiplication (`times`, `timesz`, `timesn`) in which at least one operand is
  a literal,

- minimum and maximum (`min`, `max`, `minz`, `maxz`, `minn`, `maxn`),

- conversions between `nat`, `integer`, and `natural`
  (`nat_to_integer`, `integer_to_nat`, `nat_to_natural`,
  `natural_to_nat`, `natural_to_integer`, `integer_to_nat`).

Other expressions are uninterpreted and taken as additional variables.

In propositions Omega understands:

- equal and not-equal at `nat`, `integer`, or `natural`,

- nat, integer, and natural inequalities (`leq`, `lt`, `leqz`, `ltz`,
  `leqn`, `ltn`),

- the propositional connectives (`prod`, `sum`, `arrow`, `unit`,
  `void`).

Other propositions are treated as `void` in positive positions, and as
`unit` in negative positions.

Note that quantified propositions are not understood.  For example,
`forall x . x <= x` in a positive position (such as the conclusion) is
treated as `void`.  Consequently it fails with an empty
counterexample, which may be surprising.

Terms must be identical to be taken as the *same* uninterpreted
variable.  This can be surprising, particularly with terms that
mention evars.  For example, the terms `` `length nat L `` and ``
`length E1 L `` are taken as two different terms -- even though they
display the same way -- which will very likely cause Omega to fail.
To lessen the likelihood of this, `omega` (but not `omegaRaw`) runs
the `inference` tactic first to attempt to resolve evars.
Nevertheless, it is possible for evars to leak through inference.

Some forms require Omega to search multiple possibilities.  This
includes `prod` in a positive position, `sum` or `arrow` in a negative
position, and any function that is defined by cases (*e.g.,* `minus`,
`pred`, `min`, `max`, or `integer_to_nat`).  Each appearance of such
a form doubles the effective size of the constraint, which will affect
performance.  However, multiple occurrences of the same expression
will not double the size multiple times.



### Miscellaneous tactics

Rewriting, reordering, and case analysis are documented on their own
pages.

- `change /[hyp x]/ /[term A]/`

  Replaces `x`'s type with `A`, which must be equivalent.

  + `change /concl/ /[term A]/`

    As above but replaces the conclusion.


- `assertLater /[term A]/ /[name option]/`

  Generates a subgoal to prove `A` with all later hypotheses promoted
  to the present.  Create a new **later** hypothesis of type `A` using
  the given name.  (Since the new hypothesis is later, one cannot
  match an intro pattern against it yet.)

  This is similar to asserting `future A` and immediately decomposing
  the new hypothesis, but doing it that way generates an additional
  typing goal that `assertLater` does not generate.


- `squashConcl`

  Attempts to replace the conclusion `C` with `{ C }` by proving and
  then using [squash stability](lib/sqstable.html).

  + `squashConclRaw`

    As `squashConcl` but does not invoke the typechecker.

  + `proveSqstable`

    Attempts to prove a goal of the form `sqstable P`.

  + `proveSqstableRaw`

    As `proveSqstable` but does not invoke the typechecker.


- `exfalso`

  Replaces the current goal with `void`.  Also unhides any hidden hypotheses.


- `Tactic.sideEffect : (unit -> unit) -> tactic`

  Execute the function argument for its side effects, and do nothing.

  + `displayTac : string -> tactic`

    Print the string and do nothing.


- `trustme`

  Discharges the current goal.  Can only be used if unsafe mode has
  been activated by running `Unsafe.allow ();`.




### The tactic monad

The tactic type is a special case of the tactic monad type `'a
tacticm`, which is like an ordinary tactic except it passes a value of
type `'a` to each subgoal.  Ordinary tactics are then defined:

    type tactic = Message.label tacticm

The label contains information that is attached to the subgoal when it
is displayed for the user.  Most tactics leave it empty.

Most of the tactic combinators actually have more general types than
given above, using the tactic monad:

    fail        : string -> 'a tacticm
    cut         : 'a tacticm -> 'a tacticm
    lift        : (unit -> 'a tacticm) -> 'a tacticm
    done        : 'a tacticm
    andthen     : 'a tacticm -> 'b tacticm -> 'b tacticm
    andthenl    : 'a tacticm -> 'b tacticm list -> 'b tacticm
    andthenlPad : 'a tacticm -> 'b tacticm list -> 'b tacticm -> 'b tacticm
    andthenOn   : int -> 'a tacticm -> 'a tacticm -> 'a tacticm
    first       : 'a tacticm list -> 'a tacticm
    orthen      : 'a tacticm -> (unit -> 'a tacticm) -> 'a tacticm
    ifthen      : 'a tacticm -> 'b tacticm -> 'b tacticm -> 'b tacticm

Several of the combinators also have monadic versions that serve as
the monad's unit and various flavors of bind:

    idtacM       : 'a -> 'a tacticm
    andthenM     : 'a tacticm -> ('a -> 'b tacticm) -> 'b tacticm
    andthenlM    : 'a tacticm -> ('a -> 'b tacticm) list -> 'b tacticm
    andthenlPadM : 'a tacticm -> ('a -> 'b tacticm) list -> ('a -> 'b tacticm) -> 'b tacticm
    andthenOnM   : int -> 'a tacticm -> ('a -> 'a tacticm) -> 'a tacticm
    ifthenM      : 'a tacticm -> ('a -> 'b tacticm) -> 'b tacticm -> 'b tacticm

The monadic operations `andthenM` and `andthenlM` have the infix
operators `>>=` and `>>>=` as synonyms.

The most general flavor of bind is:

    andthenFoldM :
       'a tacticm 
       -> ('a -> 'b -> 'c tacticm * 'b)
       -> ('b -> string option)
       -> 'b
       -> 'c tacticm

The tactic `andthenFoldM tac1 tacfn finish x` first runs `tac1`.  It
then folds `tacfn` left-to-right over the subgoals.  Each invocation
is passed (1) the monadic argument of type `'a` that was passed to
that subgoal, and (2) a current value of type `'b`; and returns a `'c
tacticm` (which is used on that subgoal) and a new value of type `'b`
that will be used with the next subgoal.  The initial `'b` value is
`x`.  Suppose the final `'b` value is `y`.  Then `finish y` is
evaluated and if the result is `SOME msg`, the entire tactic fails
using error message `msg`.



### Exceptions

Exceptions tend to work clumsily with continuation-passing style.  The
`tryf` function mediates the interface between them:

    exception Tactic.Tryf of string
    Tactic.tryf : (unit -> 'a) -> ('a -> 'b tacticm) -> 'b tacticm

The tactic `tryf f tac` will call `f ()` to obtain `x : 'a`, and then
execute `tac x`.  But if `f ()` raises `Tryf msg`, the combinator
calls `fail msg` instead.



### Low-level tactics

These tactics are primarily used to implement other tactics:

- `Tactic.replaceJudgement : Judgement.judgement -> tactic`

  Replaces the `judgement` portion of the current goal, leaving the
  directory unchanged.

  + `Tactic.replaceHyp : int -> Judgement.hyp -> tactic`

    Replaces a particular hypothesis (counting backward from 0).

  + `Tactic.replaceConcl : Term.term -> tactic`

    Replaces the conclusion.

- `Tactic.withgoal : (goal -> 'a tacticm) -> 'a tacticm`

  Invokes its argument tactic, passing the current goal to that
  tactic.

  + `Tactic.withdir : (Directory.directory -> 'a tacticm) -> 'a tacticm`

    Invokes its argument tactic, passing the current
    [`directory`](sig/directory.html) (the part of the goal used to
    relate names to de Bruijn indices) to that tactic.

  + `Tactic.withidir : (Directory.idirectory -> 'a tacticm) -> 'a tacticm`

    Invokes its argument tactic, passing the current
    [`idirectory`](sig/directory.html) (the part of the goal used to
    turn names into de Bruijn indices) to that tactic.

  + `Tactic.withterm : ETerm.eterm -> (Term.term -> 'a tacticm) -> 'a tacticm`

    Invokes its argument tactic, passing the internal version of its
    first argument to that tactic.

    * Available as `withterm /[term]/ [tactic function]`.

  + `Tactic.withHeadConst : string -> (Constant.constant -> 'a tacticm) -> 'a tacticm`

    Invokes its argument tactic, passing it the head constant of the
    current conclusion as its argument.  If the conclusion does not
    have a head constant, it fails using the string argument as the
    error message.  If the head constant is soft and the argument
    tactic fails, it tries again with the head constant of the
    conclusion's unfolding.

- `Tactic.transformFailure : (string -> string) -> 'a tacticm -> 'a tacticm`

  Invokes its argument tactic.  In the event that tactic fails, it
  alters the error message using the supplied function.

  It is generally a good idea to combine this with a cut.  Otherwise
  when a subsequent tactic fails it will backtrack through the
  `transformFailure` and get its error message altered.

  + `Tactic.setFailure : string -> 'a tacticm -> 'a tacticm`

    As `transformFailure` but it simply replaces the error message.

- These primitive operations are discussed as part of [primitive
  tactics](primitive-tactics.html):

      Tactic.chdir : Directory.directory -> tactic
      Tactic.cast : Judgement.djudgement -> Refine.validation -> tactic
      Tactic.execute : judgement -> tactic -> (Refine.validation, string) Sum.sum

      RefineTactic.refine : Rule.rule -> tactic
