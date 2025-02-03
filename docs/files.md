# Files

Checking an Istari file (`.ist` by convention) in batch mode
automatically generates an Istari library file (`.isto` by
convention).  Istari library files contain constants definitions,
lemmas, reductions, and whatever else the user puts into the registry.
However, library files **do not** contain IML code, such as tactics.

Thus Istari content and IML code must be loaded separately:

- To load an Istari file:

      File.load "[filename]";

  A file can be loaded only once; subsequent loads of the same file
  have no effect.

  When X loads the Istari file Y, Istari records Y among X's
  dependencies.  Later, when X is loaded, Y is also loaded
  automatically.  This behavior can be defeated by
  `File.loadWithoutDependencies` which neither records dependencies
  nor loads them.  Also note that `.isto` files should not be moved if
  automatic dependency management is used.


- To read, compile, and execute an IML file:

      File.import "[filename]";

  Like load, a file can only be imported once.  Subsequent imports
  of the same file have no effect.  If the file cannot be found in the
  current directory, it will then try each directory in the search
  path.

  Alternatively, one can load an IML file unconditionally and without
  using the search path using the primitive operation:

      Ctrl.use "[filename]";

  In either version, the current directory is temporarily set to the
  directory containing the file being imported or used.



### Library naming conventions

The Istari library adopts a naming convention for the various files
that attend an Istari file.  We use `Nat` as an example:

- `nat.ist`: The actual Istari file, containing definitions,
  lemmas, reductions, and registered objects.

- `nat.isto`: The compiled version of `nat.ist`.

- `nat-aux.iml`: An IML source file that implements tactics, parsing
  and unparsing rules, etc.

- `nat-load.iml`: An IML source file that prepares `Nat` for use.  If
  `nat-aux.iml` it loads it, and then runs startup code such as
  calling functors (see below).

If `nat.ist` has IML code that is only needed locally, not by clients,
then that code can appear directly in `nat.ist`.  However, such code
does not get written into `nat.isto`.  If Nat's clients also need
access to the code, the code should be put into `nat-aux.iml`, so it
is available to both `nat.ist` and its clients.

If each such piece of code were put into a separate file, it would
lead to a proliferation of numerous `-aux` files.  To avoid this, it
is helpful to put all such code into functors.  Then all the code can
be grouped into a single `nat-aux.iml` file, but since the code is
within functors, nothing is executed prematurely.  Then `nat.ist` can
call each functor at the appropriate time.  A client could also call
each functor if it wants, but it is usually more useful just to have
the `nat-load.iml` file call all the functors.


### Constant names in moving code

When writing `nat-aux.iml`, one should be aware of a subtle issue.
The dynamic environment in which its functors are called often differ
between `nat.ist` and its clients.  Within `nat.ist`, a functor is
typically called while the `Nat` module is still open, but when the
functor is called by the clients `Nat` is certainly closed.  Thus, a
constant can go by two different names, for example `plus_commute` and
`Nat.plus_commute`, and neither name is usable in both places.  Thus,
if the code needs to resolve a constant that resides in a module that
might or might not still be open, it should use
`Namespace.resolveGlobal`, which looks up a constant by the name that
it will have once all modules have been closed.


### The search path

By default, the search path contains only Istari's library, whose
location is given by the `ISTARILIB` environment variable.  If the
variable is not defined, the `library` subdirectory of the Istari
distribution is used.

Additional directories can be added in batch mode using the `-L
<directory>` flag.  Additional directories are searched before the
Istari library.

In either mode, the search path can be viewed or altered by reading or
writing:

    File.libraryPath : string list ref

The search path generally should contain only absolute path names.
