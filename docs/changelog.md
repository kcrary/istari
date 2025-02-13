# Change log

#### Development version

- The typechecker deals better with the future modality, and with type
  inference for polymorphic, higher-order functions.

- Old versions of the typechecker can be loaded from
  `library/typecheck`.

- `File.import` uses the search path to find files that are not in the
  current directory.

- New tactics:

  + `assertLater` is like `assert`, but asserts a "later" fact.

  + `setEq'` is like `setEq` but reverses the direction of the
    equality.

- Rewriting changes:

  + `eqtp` can be rewritten through `eq`.

  + `eeqtp` can be rewritten through `letnext`, `eq`, and `eeqtp`.

- Library changes:

  + The `GirardParadox`, `SmithParadox`, and `Union` libraries are no
    longer pre-loaded.

  + `Weaksum` added.

  + `Miscellaneous` has been renamed to `Misc`.

- Basis changes:

  + Added `Path` and `FileSystem` modules.

  + Use Unix paths consistently.

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
