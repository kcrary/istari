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

    ffix f --> f (next (ffix f))

It appears in the registry under the name `Bar.unroll_ffix`.  It can
also be used through the `unroll` tactic.


The partial type `bar A` provides an `A` now, or sometime later:

    bar : type:bar
        = def:bar

    bar_unroll : type:bar_unroll

The partial type acts as a monad.  Its unit is `now`:

    now : type:now
        = def:now

Another intro form is `laterf`:

    laterf : type:laterf
           = def:laterf

The `laterf` form is very often used with `next`, so we define:

    later : type:later
          = def:later

The monadic bind is `bindbar`:

    bindbar : type:bindbar

    bindbar (now x) f --> f x ;
    bindbar (laterf x) f --> let next y = x in later (`bindbar y f)
    bindbar (later x) f --> later (`bindbar x f)

The syntactic sugar `bindbar x = m in n` is accepted for 
`` `bindbar m (fn x . n)``.


Observe that `bindbar` always produces an element of some `bar` type.  A
variation on it, `bindbart`, produces a type instead:

    bindbart : type:bindbart

    bindbart (now x) b --> b x ;
    bindbart (laterf x) b --> let next y = x in future (`bindbart y b) ;
    bindbart (later x) b --> future (`bindbart x b) ;

The syntactic sugar `bindbart x = m in b` is accepted for 
`` `bindbart m (fn x . b)``.


Bar is covariant:

    bar_subtype : type:bar_subtype


Finally we can define a fixpoint operator on partial objects:

    bfix : type:bfix
         = def:bfix

The reduction for `bfix` is:

    bfix f --> f (later (bfix f))

It appears in the registry under the name `Bar.unroll_bfix`.  It can
also be used through the `unroll` tactic.


At this point we'd like to follow the development in Smith [2] and
define a termination predicate.  Alas, we cannot.  Istari's
step-indexed semantics is unable to express liveness properties such
as termination.  If it could express termination, we would be able to
draw a contradiction, because the type of `bfix` does not have Smith's
admissibility requirement.  (See Smith [2], theorem 60.)


We can iterate over partial objects using the `bar_iter` iterator.
The cases are `now` and `later`:

    bar_iter : type:bar_iter

    bar_iter _ hn _ (now x) --> hn x
    bar_iter P hn hl (laterf x) --> let next y = x in hl (next y) (next (bar_iter P hn hl y))
    bar_iter P hn hl (later x) --> hl (next x) (next (bar_iter P hn hl x))

This is employed automatically by the `induction` tactic on hypotheses
of `bar` type.

---

[1] Robert L. Constable and Scott Fraser Smith.  Partial Objects in
Constructive Type Theory.  In *Second IEEE Symposium on Logic on
Computer Science,* 1987.

[2] Scott Fraser Smith.  *Partial Objects in Type Theory*, 1988.
