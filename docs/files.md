# Files

Checking an Istari file (`.ist` by convention) in batch mode
automatically generates an Istari library file (`.isto` by
convention).  Istari library files contain constants definitions,
lemmas, reductions, and whatever else the user puts into the registry.
However, library files **do not** contain IML code, such as tactics.

Thus IML code and Istari content must be loaded separately:

- To read, compile, and execute an IML file:

      Ctrl.use "[filename]";

  Alternatively:

      Ctrl.import "[filename]";

  Import is like use, except that the same file can only be imported
  once.  Subsequent imports of the same file have no effect.

- To load an Istari file:

      File.load "[filename]";

  A file can be loaded only once; subsequent loads of the same file
  have no effect.  Often an Istari file is loaded indirectly by IML
  code (such as `nat-deps.iml` below).



### Naming conventions

The Istari library adopts a naming convention for the various files
that attend an Istari file.  We use `Nat` as an example:

- `nat.ist`: The actual Istari file, containing definitions,
  lemmas, reductions, and registered objects.

- `nat.isto`: The compiled version of `nat.ist`.

- `nat-aux.iml`: An IML source file that implements tactics, parsing
  and unparsing rules, etc.

- `nat-deps.iml`: An IML source file that imports `Nat`'s dependencies,
  then loads `nat.isto`.

- `nat-load.iml`: An IML source file that does everything necessary to
  prepare `Nat` for use.  It imports `nat-deps.iml` and `nat-aux.iml`,
  and may take other necessary actions such as calling functors (see
  below).

In order to avoid code duplication, most of the code in `nat-aux.iml`
appears in functors, so that `nat.ist` can use the code at the
appropriate time.  (Code that deals with a constant should not be
executed until that constant exists.)  In `nat-load.iml` all the
functors are called at once, after `nat.isto` is loaded.
