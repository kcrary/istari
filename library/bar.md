open:Bar
# `Bar` (partial types)

Inspired by the partial types ("bar types") of Constable and Smith
(*Partial objects in constructive type theory*, 1987), but weaker,
because we cannot implement the termination predicate.

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

Another intro form is `later`:

    later : type:later
          = def:later
          imp:later

The monadic bind is `bindbar`:

    bindbar : type:bindbar
            = def:bindbar
            imp:bindbar

    bindbar _ _ (now _ x) f --> f x
    bindbar A B (later _ x) f --> later B (` bindbar A B x f)

The syntactic sugar `bindbar x = m in n` is accepted for 
`` ` bindbar _ _ m (fn x . n)``.

   

Finally we can define a fixpoint operator on partial objects:

    bfix : type:bfix
         = def:bfix
         imp:bfix


At this point we'd like to follow the development in Smith (*Partial
Objects in Type Theory*, 1988) and define a termination predicate.
Alas, we cannot.  Istari's step-indexed semantics is unable to express
liveness properties such as termination.  If it could express
termination, we would be able to draw a contradiction, because the
type of `bfix` does not have Smith's admissibility requirement.  (See
Smith (1988), theorem 60.)
