# Change log

#### Development version

- The typechecker deals better with the future modality, and with type
  inference for higher-order functions.

- Old versions of the typechecker can be loaded from
  `library/typecheck`.

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
