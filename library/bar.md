open:Bar
# `Bar` (simulated partial types)

This library simulates much of the [partial type
mechanism](../type-theory.html#partial-types) using future and guarded
recursive types.  Partial types over `A` (here called `bar A`) are
simulated by a recursive type that either returns an `A` now or tries
again one step in the future.

The simulated version supports much of the functionality of partial
types, including fixpoint induction, but notably it **cannot** support
a halting predicate.  Since one cannot express halting in the first
place, it is also impossible to convert partial objects that halt into
total objects.

Note that fixpoint induction over simulated partial types does not
have an admissibility requirement, unlike what happens with true
partial types.  It follows that it is fundamentally impossible to
implement a halting predicate; were halting implementable, one could
implement [Smith's paradox](smith-paradox.html) (which requires a
halting predicate) and derive a contradiction.  (One can implement
predicates that may naively appear to be a halting predicate, but they
are true too often.)

Thus there seems to be a tradeoff: simulated partial types avoid the
complication of admissibiity but they cannot talk about termination,
while true partial types provide the opposite.

---

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

Note that `ffix` provides an induction principle over time.  If `a` is
true now assuming `a` is true one step in the future (and therefore one
step closer to the semantics' step-indexed time horizon), then `a` is
true always.

The reduction for `ffix` is:

    ffix f --> f (next (ffix f))

It appears in the registry under the name `Bar.unroll_ffix`.  It can
also be used through the `unroll` tactic.


The simulated partial type `bar A` provides an `A` now, or sometime later:

    bar : type:bar
        = def:bar

    bar_unroll : type:bar_unroll

The type acts as a monad.  Its unit is `now`:

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

    `bindbar (now x) f --> f x ;
    `bindbar (laterf x) f --> let next y = x in later (`bindbar y f)
    `bindbar (later x) f --> later (`bindbar x f)

The syntactic sugar `bindbar x = m in n` is accepted for 
`` `bindbar m (fn x . n)``.

The monad laws are respected:

    bindbar_id_left : type:bindbar_id_left

    bindbar_id_right : type:bindbar_id_right

    bindbar_assoc : type:bindbar_assoc


Observe that `bindbar` always produces an element of some `bar` type.  A
variation on it, `bindbart`, produces a type instead:

    bindbart : type:bindbart

    `bindbart (now x) t --> t x ;
    `bindbart (laterf x) t --> let next y = x in future (`bindbart y t) ;
    `bindbart (later x) t --> future (`bindbart x t) ;

The syntactic sugar `bindbart x = m in b` is accepted for 
`` `bindbart m (fn x . b)``.

The monad laws for `bindbart`:

    bindbart_id_left : type:bindbart_id_left

    bindbart_assoc : type:bindbart_assoc


Bar is covariant:

    bar_subtype : type:bar_subtype


Finally we can define a fixpoint operator on simulated partial objects:

    bfix : type:bfix
         = def:bfix

The reduction for `bfix` is:

    bfix f --> f (later (bfix f))

It appears in the registry under the name `Bar.unroll_bfix`.  It can
also be used through the `unroll` tactic.


We can iterate over simulated partial objects using the `bar_iter` iterator.
The cases are `now` and `later`:

    bar_iter : type:bar_iter

    bar_iter hn _ (now x) --> hn x
    bar_iter hn hl (laterf x) --> let next y = x in hl (next y) (next (bar_iter P hn hl y))
    bar_iter hn hl (later x) --> hl (next x) (next (bar_iter P hn hl x))

This is employed automatically by the `induction` tactic on hypotheses
of `bar` type.

A corollary of induction says we can map a function through `bindbart`:

    bindbart_map : type:bindbart_map
