# Files

Checking an Istari file (`.ist` by convention) in batch mode
automatically generates an Istari library file (`.isto` by
convention).  Istari library files contain constants definitions,
lemmas, reductions, and whatever else the user puts into the registry.
However, library files **do not** contain IML code, such as tactics.

Thus IML code and Istari content must be loaded separately:

- To read, compile, and execute an IML file:

      Ctrl.use "[filename]";

- To load an Istari library:

      File.load "[filename]";
