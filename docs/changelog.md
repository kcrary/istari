# Change log

#### Development version

- One can now destruct a hidden future hypothesis.  The result will be
  a hypothesis that is both later and hidden.

- Tactic changes:

  + The behavior of `revert` on hidden hypotheses has changed; it now
    generates an `intersect` conclusion, rather than a squash under an
    arrow.  The old behavior can be obtained by using `squashHidden`
    first.

  + `revert` now works on later and later-hidden hypotheses.

- Library changes:

  + `Bar` has additional lemmas.

- Added rules `intersectfutIntro`, `futureLeftHidden`, and
  `parametricElim'`. Also added rules governing `parametricfut`; and
  totality, strictness, uptype, and admissibility rules for
  `forallfut`, `intersectfut`, `parametric`, and `parametricfut`.

- Fixed an unsound bug in the letIntro rule that allowed the creation
  of let hypotheses using hidden variables.  Also changed the extract
  of the letIntro rule to use a let term.


#### 1.1

- The typechecker deals better with the future modality, and with type
  inference for polymorphic, higher-order functions.

- Old versions of the typechecker can be loaded from
  `library/typecheck`.

- `File.import` uses the search path to find files that are not in the
  current directory.

- Proof irrelevance is implemented.

  + Type `parametric` added.

  + `Weaksum` provides an improved interface for union-like types.

  + The new `reduceParam` rewrite is like `reduce`, but also reduces
    parametric application.

  + The new `convertIrr` rewrite replaces a constant's irrelevant
    arguments.

  + The chaining tactics `so`, `apply`, `exploit`, and `witness`
    (often) permit using hidden variables in irrelevant arguments.

  + The definition of `abort` has been changed to make it proof
    irrelevant.

- The `forallfut` and `intersectfut` types have been added.

- New tactics:

  + `assertLater` is like `assert`, but asserts a "later" fact.

  + `setEq'` is like `setEq` but reverses the direction of the
    equality.

- Rewriting changes:

  + `eqtp` can be rewritten through `eq`.

  + `eeqtp` can be rewritten through `bar`, `eq`, `eeqtp`, `option`, 
    `letnext`, `list`, and `weaksum`.

- Library changes:

  + The `GirardParadox` and `SmithParadox` libraries are no longer
    pre-loaded.

  + `Weaksum`, `Irrelevant`, and `Quotient` added.

  + The `Union` library has been deleted, as `Weaksum` accomplishes
    its purposes better.  (Union types still exist.)

  + In `Nat`, the boolean tests `eqb`, `leqb`, `ltb`, and `neqb` now
    reduce automatically.

  + `Miscellaneous` has been renamed to `Misc`.

  + Other minor additions.

- Basis changes:

  + Added `Path` and `FileSystem` modules.

  + Use Unix paths consistently.

- Added rules `assertLater`, `assertLater'`, `coguardSubIntro`,
  `eeqEeq`, `eqEeq`, `guardSubElim`, `letnextEeq`, and
  `sequalCompatLam`.  Also added rules governing parametric functions,
  irrelevance, and future functions and intersects, and rules
  commuting squash and intensional squash with future.

- Bug fixes.


#### 1.0.1

- New tactics:

  + `remember'` is like `remember` but reverses the direction of the
    equality.

- Tactic changes:

  + `extensionality` on set and iset types now produces a squashed
     goal.

  + `intro` supports the `dprod` type.

  + Better error messages from ambiguous inference.

- Library changes:

  + `Kindlike` added.

  + `FiniteMap` library is reorganized and the `finite_map` type's
    implementation is changed.

  + `Function` has changed extensively.

  + Kind-like lemmas added to `FiniteMap`, `List`, and `Option`.

- New operation `Namespace.hide` prevents constants from being
  exported.

- Builds on SML/NJ 110.99.7.1.

- Added rules `setIntroEqSquash` and `isetIntroEqSquash`.


#### 1.0b

- First official release.
