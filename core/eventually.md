open:Eventually
# `Eventually` (simulated partial types)

This library simulates much of the [partial type
mechanism](../type-theory.html#partial-types) using future and guarded
recursive types.  Partial types over `A` (here called `ev A`) are
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
implement a halting predicate:  Were halting implementable, one could
implement [Smith's paradox](smith-paradox.html) (which requires a
halting predicate) and derive a contradiction.  (One can implement
predicates that may naively appear to be a halting predicate, but they
are true too often.)

Thus there seems to be a tradeoff: simulated partial types avoid the
complication of admissibility but they cannot talk about termination,
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

It appears in the registry under the name `Eventually.unroll_ffix`.  It can
also be used through the `unroll` tactic.


The simulated partial type `ev A` provides an `A` now, or sometime later:

    ev : type:ev
        = def:ev

    ev_unroll : type:ev_unroll

The type acts as a monad.  Its unit is `now`:

    now : type:now
        = def:now

Another intro form is `laterf`:

    laterf : type:laterf
           = def:laterf

The `laterf` form is very often used with `next`, so we define:

    later : type:later
          = def:later

The monadic bind is `bindev`:

    bindev : type:bindev

    `bindev (now x) f --> f x ;
    `bindev (laterf x) f --> let next y = x in later (`bindev y f)
    `bindev (later x) f --> later (`bindev x f)

The syntactic sugar `bindev x = m in n` is accepted for 
`` `bindev m (fn x . n)``.

The monad laws are respected:

    bindev_id_left : type:bindev_id_left

    bindev_id_right : type:bindev_id_right

    bindev_assoc : type:bindev_assoc


Observe that `bindev` always produces an element of some `ev` type.  A
variation on it, `bindevt`, produces a type instead:

    bindevt : type:bindevt

    `bindevt (now x) t --> t x ;
    `bindevt (laterf x) t --> let next y = x in future (`bindevt y t) ;
    `bindevt (later x) t --> future (`bindevt x t) ;

The syntactic sugar `bindevt x = m in b` is accepted for 
`` `bindevt m (fn x . b)``.

The monad laws for `bindevt`:

    bindevt_id_left : type:bindevt_id_left

    bindevt_assoc : type:bindevt_assoc


Ev is covariant and preserves extensional equality:

    ev_subtype : type:ev_subtype

    ev_eeqtp : type:ev_eeqtp


Finally we can define a fixpoint operator on simulated partial objects:

    efix : type:efix
         = def:efix

The reduction for `efix` is:

    efix f --> f (later (efix f))

It appears in the registry under the name `Eventually.unroll_efix`.  It can
also be used through the `unroll` tactic.


We can iterate over simulated partial objects using the `ev_iter` iterator.
The cases are `now` and `later`:

    ev_iter : type:ev_iter

    ev_iter hn _ (now x) --> hn x
    ev_iter hn hl (laterf x) --> let next y = x in hl (next y) (next (ev_iter P hn hl y))
    ev_iter hn hl (later x) --> hl (next x) (next (ev_iter P hn hl x))

This is employed automatically by the `induction` tactic on hypotheses
of `ev` type.

Several corollaries of induction pertaining to `bindevt`:

    bindevt_simple : type:bindevt_simple

    bindevt_map : type:bindevt_map

    bindevt_shift_future_out : type:bindevt_shift_future_out

    bindevt_shift_future_in : type:bindevt_shift_future_in

    bindevt_shift_future_iff : type:bindevt_shift_future_iff

    bindevt_commute : type:bindevt_commute

    bindevt_commute_iff : type:bindevt_commute_iff

    sqstable_bindevt : type:sqstable_bindevt
