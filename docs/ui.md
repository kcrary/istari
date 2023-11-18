# The User Interface

The Istari UI is implemented as an Emacs extension.  Istari mode
should start automatically whenever a file with an `.ist` extension is
opened.  The Istari server itself will start when the user begins
processing the file, by calling `istari-start` or just by beginning to
navigate the file.

A listing of all the key commands discussed below appears at the end
of this page.  A similar listing can also be obtained in Emacs using 
`C-h m`.


### Navigation

One can move Istari one line forward using `C-c C-n` or `[F4]`.  One
can move backwards one line using `C-c C-p` or `[F5]`.  (For
compatibility with ProofGeneral muscle memory, `C-c C-u` is also
accepted.)  One can move Istari to a particular line by placing the
cursor on the line and entering `C-c [return]` or `C-return`.

A triangle in Emacs's margin indicates Istari's current position in
the file.  (On consoles that cannot support the triangle, a more
obtrusive marker is used.)  When Istari has read some incomplete
input, the triangle reverses direction.  When Istari is busy, the
triangle turns into a square.

One can interrupt Istari using `C-c C-c`.  One can terminate Istari
using `C-c p t`.

One can move the cursor to Istari's current position using `C-c .`.

One can interject code (*i.e.,* execute code that does not appear in
the file) using `C-c x`.



### An important caveat

When one moves Istari backwards, Istari rewinds the prover state.
This includes the current position in a proof, definitions, and
(almost) everything else under the control of Istari.  However, it
cannot rewind the IML environment.  Thus, if one executes:

    val x = 1;
    val x = 2;

and then rewinds one line, `x` will still be `2`, not `1`.

(A few of Istari's internal data structures are not rewound because
doing so could cause unsoundness, but they should never be noticed by
the user.)



### Obtaining information

One can re-show the current goals using `C-c s`.  This abbreviates all
the goals except the first.  To obtain a full listing of all current
goals use `C-c S`.

Some tactics (notably the typechecker) may generate more detailed
information on subgoals than what is displayed by default.  That
detail can be displayed using `C-c C-d`.

The Report module provides various information on the Istari
environment:

- `C-c r t` will give the type of a constant.

- `C-c r s` will give the definition and type of a constant.

- `C-c r m` will list all the constants in an Istari module.

- `C-c r a` will list all the constants currently loaded.

- `C-c r f` will find every constant whose type mentions
  every constant in a list of targets, and give their types.

By default, Istari will suppress displaying implicit arguments, and it
will suppress displaying substitutions attached to evars.  These can
be toggled using `C-c c i` and `C-c c s`, respectively.



### Reindentation

Since Istari uses a user-customizable parser, it isn't easy to
implement a smart indenter.  To reindent a block of code, place the
cursor at the beginning of the first line, enter `C-c C-l` to set the
initial indentation, adjust that first line to its desired column,
then enter `M-i` to repeat that adjustment on subsequent lines.



### Protection of executed code

By default, code above Istari's current line is set to read only.  The
user can toggle this using `C-c C-r`.  Use caution when editing code
already-executed code.  If you insert or delete newlines above the
current line, Istari's UI will become confused.

Undo can alter the read-only region, because I don't know how to
prevent it from doing so.



### Libraries

By default, Istari auto-loads the Istari libraries.  To suppress this
(such as when one is working on the libraries), use `C-c p l`.  This
must be done before starting the server.



### Key commands

| Key command                      | Function                                   |
| -------------------------------- | ------------------------------------------ |
| `C-c C-n` or `[F4]`              | next line                                  |
| `C-c C-p` or `C-c C-u` or `[F5]` | previous line                              |
| `C-c [return]` or `C-return`     | goto line                                  |
| `C-c .`                          | move cursor to current line                |
|                                  |                                            |
| `C-c l`                          | set initial indentation                    |
| `M-i`                            | reindent next line                         |
| <code>M-&#124</code>             | insert and indent vertical bar             | 
|                                  |                                            |
| `C-c C-c`                        | interrupt                                  |
| `C-c x`                          | interject with IML code                    |
|                                  |                                            |
| `C-c s`                          | show current goals                         |
| `C-c S`                          | show current goals verbosely               |
| `C-c C-d`                        | give detail on current goal                |
|                                  |                                            |
| `C-c r t`                        | give the type of a constant                |
| `C-c r s`                        | give the type and definition of a constant |
| `C-c r m`                        | list all constants in an Istari module     |
| `C-c r a`                        | list all constants                         |
| `C-c r f`                        | find all constants that mention targets    |
|                                  |                                            |
| `C-c i a`                        | insert applications for a constant         |
| `C-c i i`                        | insert introductions for the current goal  |
|                                  |                                            |
| `C-c c i`                        | show implicit arguments                    |
| `C-c c s`                        | show substitutions                         |
| `C-c C-r`                        | toggle read-only above current line        |
|                                  |                                            |
| `C-c p t`                        | terminate Istari                           |
| `C-c p l`                        | toggle loading libraries                   |
