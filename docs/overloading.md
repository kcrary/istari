# Overloading

In Istari, the basic arithmetic primitives (numeric literals, `+`,
`-`, `~`, `*`, and `||`) are overloaded; their meanings are determined
by the current overloading mode.

The arithmetic primitives are overloaded as follows.  The first column
indicates the overloaded syntax for the concept.  The remaining
columns indicate the non-overloaded syntax for the concept in the
indicated type, and the name of constant that is used for the concept.

|                | overloaded | nat               | natural             | integer            | rational                        | real                        |
|----------------|------------|-------------------|---------------------|--------------------|---------------------------------|-----------------------------|
| literal        |            | ``n` `` / *       | ``N` `` / *         | ``z` `` / *        | ``q` `` / `integer_to_rational` | ``r` `` / `integer_to_real` |
| addition       | `+`        | `+n` / `plus`     | `+N` / `plusn`      | `+z` / `plusz`     | `+q` / `plusq`                  | `+r` / `plusr`              |
| negation       | `~`        | n/a               | n/a                 | `~z` / `negz`      | `~q` / `negq`                   | `~r` / `negr`               |
| subtraction    | `-`        | `-n` / `minus`    | `-N` / `minusn`     | `-z` / `minusz`    | `-q` / `minusq`                 | `-r` / `minusr`             |
| multiplication | `*`        | `*n` / `times`    | `*N` / `timesn`     | `*z` / `timesz`    | `*q` / `timesq`                 | `*r` / `timesr`             |
| division       | ``||``     | n/a               | n/a                 | n/a                | ``|q`` / `divq`                 | ``|r`` / `divr`             |
| less-or-equal  | `<=`       | `<n=` / `leq`     | `<N=` / `leqn`      | `<z=` / `leqz`     | `<q=` / `leqq`                  | `<r=` / `leqr`              |
| less-than      | `<`        | `<n` / `lt`       | `<N` / `ltn`        | `<z` / `ltz`       | `<q` / `ltq`                    | `<r` / `ltr`                |
| equality test  | `=?`       | `=n?`             | `=N?`               | `=z?`              | `=q?`                           | n/a                         |
| leq test       | `<=?`      | `<n=?`            | `<N=?`              | `<z=?`             | `<q=?`                          | n/a                         |
| lt test        | `<?`       | `<n?`             | `<N?`               | `<z?`              | `<q?`                           | n/a                         |
| neq test       | `!=?`      | `!n=?`            | `!N=?`              | `!z=?`             | `!q=?`                          | n/a                         |

Notes:

- A nat literal parses as a term of the form `succ (... zero ...)`.

- A integer or natural literal parses as an unadorned native integer.
  Thus ``z` `` and ``N` `` are effectively the same, except that the
  latter generates a syntax error when the number is negative.

- A rational or real literal parses as a conversion function applied
  to a native integer (*e.g.,* ``q`0`` means 
  ``integer_to_rational z`0``).

- Using an overloaded operator that is not meaningful in the current
  mode (*e.g.,* negation in `nat`) results in a syntax error.  The
  same thing happens when using a literal that is outside the range
  that is representable in the current mode.

- Note that overloaded division is written `||`, since `/` and `|`
  have specific meanings already.  The non-overloaded divisions
  dispense with the extra bar.

To activate an overloading mode globally, one calls the global
activation function given below, which has type `unit -> unit`.  To
activate an overloading mode for a specific scope, one wraps with the
local activation syntax below.  For example ``integer`(0 + 0)`` refers
to ``plusz z`0 z`0``.

| mode     | global activation   | local activation   |
|----------|---------------------|--------------------|
| nat      | `setArithNat`       | ``nat`(...)``      |
| natural  | `setArithNatural`   | ``natural`(...)``  |
| integer  | `setArithInteger`   | ``integer`(...)``  |
| rational | `setArithRational`  | ``rational`(...)`` |
| real     | `setArithReal`      | ``real`(...)``     |

The overloading mechanism is *not* used for levels, since level
expressions can always be identified by context.  In a level
expression, literals refer to level literals, while `+` refers to
adding level literal to a level.

The overloading mode is also not used for types.  The product type is
written using `&` (not `*`), and the sum type is written using `%`
(not `+`).
