# Primitive tactics

To build a new tactic, one can use the [tactic
combinators](tactics.html).  Alternatively, the `tactic` type is
exposed so one can implement a new tactic natively:

    type goal = Judgement.judgement * Directory.directory
    type validation = Refine.validation
    type validator = validation list -> validation * validation list
    type answer = exn

    type 'a tacticm = 
       goal
       -> (string -> answer)                                              (* failure continuation *)
       -> (('a * goal) list * validator * (string -> answer) -> answer)   (* success continuation *)
       -> answer

    type tactic = Message.label tacticm

Let us unpack this:

- A `goal` consists of a two components: a `judgement`, which is the
  substance of the goal (using de Bruijn indices), and a `directory`,
  which converts between indices and names.

- A `validation` is an abstract type that certifies that a judgement
  has been proved.

  Although one ordinarily has no cause to do it, one can verify that a
  validation validates a particular judgement by calling `Refine.id`
  on the validation and `Judgement.id` on the judgement to obtain two
  judgement identifiers of type `Judgement.id`.  They can then be
  compared using `Judgement.eq`.

  When a trail (see below) is rewound, evars can change, which can
  invalidate a validation.  Although (again) one ordinarily has no
  cause to do it, one can verify that a validation remains valid using
  `Refine.valid`.

- A `validator` is a function that takes a list of validations and
  pulls from the front of the list some (zero or more) validations
  needed to prove a goal, then returns the goal's validation and the
  leftover validations.

  A validator should not assume that its input list contains exactly
  the needed number of validations.  It should always accept extra
  validations and return them.

- Tactics are written in continuation-passing style.  An `answer` is
  the ultimate result of that continuation-passing computation.  It is
  chosen to be `exn`.

- An `'a tacticm` takes a goal, a failure continuation, and a success
  continuation, and returns an answer.

  + The failure continuation is passed a string as an error message.

  + The success continuation is passed:

    * a list of subgoals, with values of type `'a` (the monadic
      argument) attached,

    * a validator to be run on the validations of the subgoals to
      validate the goal, and

    * a new failure continuation for the success continuation to use
      if it needs to backtrack.

- A `tactic` is a `tacticm` that is passed `Message.label` as its
  monadic argument.  Most tactics ignore the label, but labels passed
  to the top-level are displayed to the user.


### Priority

Many tactics generate typing subgoals.  When implementing a tactic, it
is good not to solve those goals eagerly, but to save them all so that
they can all be addressed at once.  (It is not uncommon for one goal
to help in the solution of another.)  However, the proliferation of
typing goals can complicate the assembly of tactics into larger
tactics.

To help manage this, the tactic library defines **priorities**:

    datatype priority = Primary | Secondary

The main goals of interest are considered `Primary`, while typing
obligations are considered `Secondary`.  Every tactic that supports a
`Raw` variant also supports a `Priority` variant, intended for
building larger tactics.  For example, `intro` has an `introRaw`
variant, so it also has an `introPriority` variant:

    val introRaw      : IntroPattern.ipattern list -> tactic
    val introPriority : IntroPattern.ipattern list -> priority tacticm

The priority variant attaches a priority to each subgoal.  This is
available using the monadic bind as usual, but for convenience, the
tactic library also supplies:

    val andthenPri     : priority tacticm -> priority tacticm -> priority tacticm
    val andthenlPri    : priority tacticm -> priority tacticm list -> priority tacticm
    val andthenlPadPri : priority tacticm -> priority tacticm list -> priority tacticm -> priority tacticm

Running `andthenPri tac1 tac2` runs `tac1`, then runs `tac2` on all
its subgoals marked `Primary`.  Running `andthenlPri tac [tac1, ...,
tacn]` runs `tac`, then runs `tac1` on its first primary subgoal,
`tac2` on its second, etc.  These have the infix synonyms `>>!` and
`>>>!`.  The `andthenlPadPri` variant is like `andthenlPri` but it
pads out the list with its third argument if there are too many
primary subgoals.



### Primitives

The [`Tactic`](sig/tactic.html) module provides some primitive actions:

    val chdir : Directory.directory -> tactic
    val cast : Judgement.judgement -> Refine.validation -> tactic
    val execute : goal -> tactic -> (Refine.validation, string) Sum.sum

- `chdir d` replaces the current goal's directory with `d`.

- `cast j v` discharges the current goal, if `v` is a validation of
  `j`, and `j` unifies with the current goal's judgement.  This is how
  lemmas are utilized.

- `execute g tac` runs `tac` on the goal `g`.  If it succeeds, it
  returns the validation, otherwise it returns the error message.

The [`RefineTactic`](sig/refine-tactic.html) module provides:

    val refine : Rule.rule -> tactic

- `refine r` applies the primitive rule `r` to the current goal.  One
  usually does not want to use this in proof scripts directly, because
  it does not alter the directory.  Thus, if the rule changes the
  context (such as by adding a hypothesis), the resulting goal will
  look strange.

Istari's primitive rules are in the `Rule` module, which can be found
in `prover/trusted/rule.iml`.  Most of the rules appear in a somewhat
human-readable form in `prover/trusted/RULES`.  Many of the rules are
repackaged in a more convenient form in `RuleTactic`, which can be
found in `prover/rule-tactic.iml`.


### The internal term representation

The internal term representation appears in the `Term` module and is
given by:

    type binder = Symbol.symbol option

    datatype native =
       Integer of IntInf.int
     | Symbol of Symbol.symbol

    datatype term =
       Var    of int
     | Const  of constant
     | Elim   of term * elim list
     | Lam    of binder * term
     | Pair   of term * term
     | Next   of term
     | Triv
     | Sub    of term * sub
     | Evar   of ebind
     | Native of native

     | Marker of Symbol.symbol

    and elim =
       App    of term
     | Pi1
     | Pi2
     | Prev

    and sub =
       Shift  of int
     | Dot    of term * sub
     | Idot   of int * sub

The `binder` in `Lam` is not significant to the type theory.  The
implementation uses it to suggest a name for the bound variable.  A
`Marker` taking the empty symbol is the internal representation of the
[hole pseudo-term](terms.html#the-term-grammar) (`__`).  (The
datatype also allows distinguished markers in which a nonempty symbol
is used.  Currently no tactics use this form.)



##### Spinal form

Terms are expressed in *spinal form*.  This means that the elimination
forms are expressed as a head followed by a sequence of elims.  The
elims are given innermost first.  Thus, the term `prev (pi1 (a b) c)`
is written in spinal form as `a b #1 c #prev`, and would appear in the
code as:

    Elim (Const a, [App (Const b), Pi1, App (Const c), Prev])


##### Explicit substitutions

Terms also written using explicit substitutions.  The term `m` under
the substitution `s` is written `m[s]` (one only sees this syntax when
working with [literal terms](terms.html#literal-terms)), and would
appear in the code as:

    Sub (m, s)

Explicit substitutions are written using `Shift` and `Dot`.  When the
term in `Dot` is a variable, there is a special case `Idot` for better
performance.  **Note:** de Bruijn indices are counted from 0, which
tends to be atypical for explicit substitutions.

The identity substitution `id` is defined to be `Shift 0`.
Substitution composition is a function rather than a constructor:

    compose : sub -> sub -> sub


##### Evars

Unknown terms are represented by evars (also known as "existential
variables," or as "unification variables"), using the abstract type
`ebind`.  One can read the current value of an evar, if any, using:

    readEbind : ebind -> term option

The primitive operation to write to an ebind is not exposed to the
user because it is not always sound.  (An occurs check must be
performed.)  The user may use:

    Unify.setEbindSub : ebind -> sub -> term -> bool

Calling `setEbindSub e s m` will attempt to set `e[s]` to be equal to
`m`, and returns true if it succeeds.  If `s` is `id`, this will
succeed as long as `e` is not yet bound, and does not appear in `m`.

To unwind an evar assignment, one may use the trail mechanism (see
below).


##### Native terms

Integers are implemented "natively" (meaning: using the language's
built-in bignum implementation) for better performance.  In contrast,
natural numbers are represented in unary, so extremely bad performance
is to be expected on all but the smallest calculations.  The `native`
type is defined to allow room for future expansion to support other
native data types.



### Simplification and normalization

The same term can be represented in multiple ways because of spinal
form, explicit substitutions, and evars.  To obtain the term in a
consistent form, one calls `Normalize.simplify` to put it into *simple
form*, which is given by the grammar:

    (head)
    h  ::= var | const | evar[s]

    (intro)
    Mi ::= fn . M
         | (M, M)
         | next M
         | ()
         | native-term
         | marker

    (simple form)
    Ms ::= h spine
         | Mi
         | Mi nonempty-spine

Simplification resolves substitutions, replaces bound evars, and
combines spines to put terms in a standard form that is suitable for
pattern matching.  (Note that it does so outermost only.)

A stronger condition is weak-head-normal form, which also reduces beta
redices:

    (weak-head-normal form)
    Mn ::= h spine
         | Mi
         | Mi non-matching-spine

In weak-head-normal form, the term normally is either an `Elim`
(possibly with an empty spine) or an intro form.

It is also possible for a weak-head-normal term to be an intro form
applied to a nonempty spine whose first elim does not match the intro.
(For example `(fn . M) #1`).  Such terms are normally ill-typed, so
this case can usually be neglected.

To obtain a weak-head-normal form, one calls `Normalize.whnf`, or,
less commonly, `Normalize.whnfHard` or `Normalize.whnfBasic`.  These
differ according the [reduction
strategy](typechecking.html#reduction-strategies) employed.  One can
also call `Normalize.normalize` or `Normalize.normalizeHard` to reduce
recursively and obtain a fully normal form.
    

### Utilities

- [`Tactic`](sig/tactic.html) provides tactic definition and
  operations shown above, among others.

- [`RefineTactic`](sig/refine-tactic.html) provides the refine tactic.

- [`Trail`](sig/trail.html) establishes a trail of evar bindings that
  can be unwound when necessary.  Its most important operations are:

      type mark
      exception Rewind
      val mark : unit -> mark
      val rewind : mark -> unit

  A `mark` represents a particular point in the trail, and `rewind`
  unbinds any evars that were bound after that `mark` was created.  If
  a rewind is unsuccessful (for example, if a more recent binding has
  been made irreversible), `rewind` raises `Rewind`.

- [`Directory`](sig/directory.html) defines the `directory` type, for maintaining a
  correspondence between de Bruijn indices and names, and gives a
  variety of operations on directories.  It also defines the
  `idirectory` type, a lighter-weight directory that is used only in
  one direction, to convert external terms into internal terms.

- [`Unify`](sig/unify.html) is the unification engine.  Its most
  important operations are:

      val unify : term -> term -> unit
      val solve : unit -> bool
      val unify1 : term -> term -> bool  (* unify followed by solve *)
      val setEbindSub : ebind -> sub -> term -> bool

  The `unify` operation adds a constraint to the queue, and `solve`
  attempts to solve all constraints in the queue.  The `unify1` solves
  one constraint (plus any others that were previously queued).
  Calling `setEbindSub e s m` attemps to assign to `e` in order to
  make `e[s]` equal to `m`, and returns true if it succeeded.
