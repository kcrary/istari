# IML

IML is an ML dialect close to Standard ML.  Most SML code should
require very little modification to serve as IML code.

The IML preprocessor can generate either SML or OCaml.  Compatibility
with OCaml drives many of the differences between IML and SML listed here.


### User-definable parsing

The most visible difference between IML and SML is user-definable
parsing.  For example, to begin a lemma in Istari, one might enter:

    lemma "reflexivity" / forall (n : nat) . n = n : nat /;

Here the `lemma` function has type `string -> ETerm.eterm -> unit`.
The code within the slashes is passed to a user-definable parser, in
this case a parser for terms.  The term parser is the default, but
every (short) identifier can be assigned a different parser for each
of its arguments.  (One can also change the default parser, but that
is not recommended when using Istari.)

For example, the `defineRaw` function takes a "definition pattern" as
its first argument and a term as its second:

    defineRaw /double n/ /n + n/;

##### Antiquote

Many user-definable parsers all you to embed an arbitrary ML term into
the parse.  This is done using an *antiquote* mechanism, where the
embedded term is enclosed by backslashes.  (If the embedded term is
inappropriate, this may result in a type error.)

For example, to write a ML function that turns any Istari term into
its successor, one writes:

    fn t => / succ \t\ /

##### Tokenization

Input code is tokenized before it is passed to a user-definable
parser.  (This means that user-definable parsers need not deal with
lexical analysis or whitespace.)  Tokenization is done in a
simple-minded matter since it does not know anything about the
grammar.

The main rule is that tokens are separated by whitespace.  There are
three exceptions:

- Some characters always form a complete token, even when adjacent to
  other text: `(`, `)`, `,`.

- Some characters always end a token: `[`, `{`, `` ` ``.
  (The tick form is normally used for parsing directives.)

- Some characters always begin a new token: `]`, `}`.

Thus, one should probably not write `(x; y)`, because the `x;` forms a
single token.  Instead write `(x ; y)`.



### Proof management syntax

The second-most visible difference between IML and SML is special
syntax for managing proofs.  One applies a tactic to the current goal
by ending the tactic code with a period, and one can enter and leave
subgoals with curly braces:

| Syntax       | Elaborates to:            |
| ------------ | ------------------------- |
| `[tactic].`  | `Prover.apply [tactic];`  |
| `{`          | `Prover.enter ();`        |
| `}`          | `Prover.leave ();`        |
| `[number]:{` | `Prover.entern [number];` |



### Anonymous multi-argument functions

IML supports syntax for anonymous multi-argument functions.  A curried
function taking three arguments can be written:

    fns x y z => [body]

This is equivalent to:

    fn x => fn y => fn z => [body]

Unlike `fn`, neither `fns` cannot accept multiple clauses.



### Collapsed tuples

A left-associated iterated pair can be written using the
quasi-constructor `Collapse`:

    Collapse (1, 2, 3)

is equivalent to:

    ((((), 1), 2), 3)

This can be used with patterns as well.

There is also special syntax for a function taking a collapsed tuple:

    fnc x y z => [body]

is equivalent to:

    fn (Collapse (x, y, z)) => [body]

which in turns means:

    fn ((((), x), y), z) => [body]

The `fnc` form is mainly used to interact with Istari's case-analysis
module [`Case`](case.html).  Unlike `fn`, `fnc` cannot accept multiple
clauses.



### Exceptions

IML exception handling is written using "try-with" rather than
"handle".  Thus, instead of:

    [term] handle [constructor] => [handler-term]

one writes:

    try [term] with [constructor] => [handler-term]



### Do bindings

An IML `let` binding can employ `do` bindings to sequence operations:

    let
       do x = exp1
    in
       exp2
    end

All of the `let` that follows the `do` is wrapped up as a function and
passed as an additional argument to `exp1`, producing:

    exp1 (fn x => exp2)

One use of this device is for writing monadic code.  For example,
`andthenM` is the bind operation for the `tacticm` monad:

    let
       do x = andthenM tac1
       do y = andthenM tac2
    in
       tac3
    end

This expression is elaborated to:

    andthenM tac1 (fn x => andthenM tac2 (fn y => tac3))

Another use is for writing code in continuation-passing style, such as:

    let
       do m = withterm / [term] /
    in
       tac
    end

This elaborates to:

    withterm / [term] / (fn m => tac)

The Istari tactic library is implemented using continuation-passing
style, so it makes considerable use of `do`.



### Records

In IML, records are permitted only as arguments to datatype constructors.  Thus:

    type point = { x : int, y : int }

is not permitted, but:

    datatype point = Point of { x : int, y : int }

**is** permitted.

Since the fields of a record can always be determined from the
constructor, there is no need for wildcard patterns.  So instead
of:

    val Point { x=horiz, ... } = [term]

one just writes:

    val Point { x=horiz } = [term]



### Datatype patterns

In IML (like OCaml), one cannot match multiple datatype arguments
using a single variable.  Thus:

    datatype exp = App of exp * exp | ...

    fun eval (App e) = ...

is not permitted.  One must write:

    fun eval (App (e1, e2)) = ...

instead.  However, one is permitted to match multiple datatype
arguments with a single wildcard (`_`).




### Record/tuple projection

SML's record and tuple projection syntax (*e.g.,* `#1`) is not
supported.  But for pairs and triples the basis provides substitutes:
`fst`, `snd`, `n1of3`, `n2of3`, `n3of3`.



### Unbounded integer literals

An unbounded integer literal (of type `IntInf.int`) can be written
using an `I` suffix, such as `0I`, `12I`, or `~12I`.



### Suppressing infix

An infix operator can be used as an ordinary function by placing it
within parentheses.  For example, `(+) : int -> int -> int`.  (In SML
this would be written `op +`.)  For operators beginning or ending with
an asterisk, one must add extra space(s) to prevent the parser from
interpreting it as a comment (*e.g.,* `( * )`).



### Strings

IML's string escapes are:

| escape                    | meaning                   |
| ------------------------- | ------------------------- |
| `\n`                      | newline                   |
| `\"`                      | quotation mark            |
| `\\`                      | backslash                 |
| `\x[two hex digits]`      | indicated ASCII character |
| `\[nonempty whitespace]\` | omitted                   |



### Other omissions

Some other features of SML are unsupported:

- Transparent ascription

- `local` and module-level `let`

- Datatype copying

- A `where type` cannot be attached to a datatype field.

- Many built-in exceptions cannot be handled (*e.g.,* `Bind`, `Match`,
  `Overflow`, `Size`)

- Equality types, `abstype`, `while`



### The basis

IML has its own [standard basis](basis.html) (inspired by the [SML
basis](https://smlfamily.github.io/Basis/), but different from it).
