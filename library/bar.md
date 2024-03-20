open:Bar
# `Bar` (partial types)

Inspired by the partial types ("bar types") of Constable and Smith [1],
but weaker, because we cannot implement the termination predicate.

Pause is just the identity, but we insert it in various places to
break up redices so that accidental ill-typed terms don't result in
runaway reduction:

    pause : type:pause
          = def:pause

The general Y combinator is not well typed (if it were, every
proposition would be provable), but it can be made type correct using
the future modality:

    ffix : type:ffix
         = def:ffix

The reduction for `ffix` is:

    ffix A f --> f (next (ffix A f))

It appears in the registry under the name `Bar.unroll_ffix`.  It can
also be used through the `unroll` tactic.


The partial type `bar A` provides an `A` now, or sometime later:

    bar : type:bar
        = def:bar

    bar_unroll : type:bar_unroll

The partial type acts as a monad.  Its unit is `now`:

    now : type:now
        = def:now
        imp:now

Another intro form is `laterf`:

    laterf : type:laterf
           = def:laterf
           imp:laterf

The `laterf` form is mostly commonly used in a simpler form called
`later`:

    later : type:later
          = def:later
          imp:later

The monadic bind is `bindbar`:

    bindbar : type:bindbar
            imp:bindbar

    bindbar _ _ (now _ x) f --> f x
    bindbar A B (later _ x) f --> later B (` bindbar A B x f)
    bindbar A B (laterf _ x) f --> let next y = x in later B (` bindbar A B y f)

The syntactic sugar `bindbar x = m in n` is accepted for 
`` ` bindbar _ _ m (fn x . n)``.

Observe that `bindbar` always produces an element of some `bar` type.  A
variation on it, `bindbart`, produces a type instead:

    bindbart : type:bindbart
             imp:bindbart

    bindbart _ (now _ x) B --> B x
    bindbart A (later _ x) B --> future (` bindbart A x B)
    bindbart A (laterf _ x) B --> let next y = x in future (` bindbart A y B)

Bar is covariant:

    bar_subtype : type:bar_subtype


Finally we can define a fixpoint operator on partial objects:

    bfix : type:bfix
         = def:bfix
         imp:bfix


At this point we'd like to follow the development in Smith [2] and
define a termination predicate.  Alas, we cannot.  Istari's
step-indexed semantics is unable to express liveness properties such
as termination.  If it could express termination, we would be able to
draw a contradiction, because the type of `bfix` does not have Smith's
admissibility requirement.  (See Smith [2], theorem 60.)

---

[1] Robert L. Constable and Scott Fraser Smith.  Partial Objects in
Constructive Type Theory.  In *Second IEEE Symposium on Logic on
Computer Science,* 1987.

[2] Scott Fraser Smith.  *Partial Objects in Type Theory*, 1988.
