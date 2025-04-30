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

    pause : intersect (i : level) (a : U i) . a -> a
          = fn v0 . v0

The general Y combinator is not well typed (if it were, every
proposition would be provable), but it can be made type correct using
the future modality:

    ffix : intersect (i : level) (a : U i) . (future a -> a) -> a
         = fn f .
              pause
                (fn x . f (let next x' = x in next (pause x' x)))
                (next (fn x . f (let next x' = x in next (pause x' x))))

Note that `ffix` provides an induction principle over time.  If `a` is
true now assuming `a` is true one step in the future (and therefore one
step closer to the semantics' step-indexed time horizon), then `a` is
true always.

The reduction for `ffix` is:

    ffix f --> f (next (ffix f))

It appears in the registry under the name `Bar.unroll_ffix`.  It can
also be used through the `unroll` tactic.


The simulated partial type `bar A` provides an `A` now, or sometime later:

    bar : intersect (i : level) . U i -> U i
        = fn a . rec t . a % future t

    bar_unroll : forall (i : level) (a : U i) . bar a = (a % future (bar a)) : type

The type acts as a monad.  Its unit is `now`:

    now : intersect (i : level) (a : U i) . a -> bar a
        = fn x . inl x

Another intro form is `laterf`:

    laterf : intersect (i : level) (a : U i) . future (bar a) -> bar a
           = fn x . inr x

The `laterf` form is very often used with `next`, so we define:

    later : intersect (i : level) (a : U i) . bar a -> bar a
          = fn x . laterf (next x)

The monadic bind is `bindbar`:

    bindbar : intersect (i : level) (a b : U i) . bar a -> (a -> bar b) -> bar b

    `bindbar (now x) f --> f x ;
    `bindbar (laterf x) f --> let next y = x in later (`bindbar y f)
    `bindbar (later x) f --> later (`bindbar x f)

The syntactic sugar `bindbar x = m in n` is accepted for 
`` `bindbar m (fn x . n)``.

The monad laws are respected:

    bindbar_id_left : forall (i : level) (a b : U i) (e : a) (f : a -> bar b) .
                         (bindbar x = now e in f x) = f e : bar b

    bindbar_id_right : forall (i : level) (a : U i) (m : bar a) .
                          (bindbar x = m in now x) = m : bar a

    bindbar_assoc : forall
                       (i : level)
                       (a b c : U i)
                       (e : bar a)
                       (f : a -> bar b)
                       (g : b -> bar c) .
                       (bindbar y = (bindbar x = e in f x) in g y)
                         = (bindbar x = e in bindbar y = f x in g y)
                         : bar c


Observe that `bindbar` always produces an element of some `bar` type.  A
variation on it, `bindbart`, produces a type instead:

    bindbart : intersect (i : level) (a : U i) . bar a -> (a -> U i) -> U i

    `bindbart (now x) t --> t x ;
    `bindbart (laterf x) t --> let next y = x in future (`bindbart y t) ;
    `bindbart (later x) t --> future (`bindbart x t) ;

The syntactic sugar `bindbart x = m in b` is accepted for 
`` `bindbart m (fn x . b)``.

The monad laws for `bindbart`:

    bindbart_id_left : forall (i : level) (a : U i) (e : a) (t : a -> U i) .
                          bindbart x = now e in t x = t e : U i

    bindbart_assoc : forall (i : level) (a b : U i) (e : bar a) (f : a -> bar b) (t : b -> U i) .
                        (bindbart y = (bindbar x = e in f x) in t y)
                          = (bindbart x = e in bindbart y = f x in t y)
                          : U i


Bar is covariant and preserves extensional equality:

    bar_subtype : forall (i : level) (a b : U i) . a <: b -> bar a <: bar b

    bar_eeqtp : forall (i : level) (a b : U i) . a <:> b -> bar a <:> bar b


Finally we can define a fixpoint operator on simulated partial objects:

    bfix : intersect (i : level) (a : U i) . (bar a -> bar a) -> bar a
         = fn f . ffix (fn x . f (laterf x))

The reduction for `bfix` is:

    bfix f --> f (later (bfix f))

It appears in the registry under the name `Bar.unroll_bfix`.  It can
also be used through the `unroll` tactic.


We can iterate over simulated partial objects using the `bar_iter` iterator.
The cases are `now` and `later`:

    bar_iter : intersect (i : level) (a : U i) (P : bar a -> U i) .
                  (forall (x : a) . P (now x))
                  -> (forall (xf : future (bar a)) . let next x = xf in future (P x) -> P (later x))
                  -> forall (x : bar a) . P x

    bar_iter hn _ (now x) --> hn x
    bar_iter hn hl (laterf x) --> let next y = x in hl (next y) (next (bar_iter P hn hl y))
    bar_iter hn hl (later x) --> hl (next x) (next (bar_iter P hn hl x))

This is employed automatically by the `induction` tactic on hypotheses
of `bar` type.

Several corollaries of induction pertaining to `bindbart`:

    bindbart_simple : parametric (i : level) (a : U i) .
                         forall (e : bar a) .
                           parametric (t : a -> U i) .
                             (forall (x : a) . t x) -> bindbart x = e in t x

    bindbart_map : forall (i : level) (a : U i) (b c : a -> U i) (e : bar a) .
                      (forall (x : a) . b x -> c x)
                      -> (bindbart x = e in b x)
                      -> bindbart x = e in c x

    bindbart_shift_future_out : forall (i : level) (a : U i) .
                                   forallfut (b : a -> U i) .
                                     forall (e : bar a) .
                                       (bindbart x = e in future (b x))
                                       -> future (bindbart x = e in b x)

    bindbart_shift_future_in : forall (i : level) (a : U i) .
                                  forallfut (b : a -> U i) .
                                    forall (e : bar a) .
                                      future (bindbart x = e in b x)
                                      -> bindbart x = e in future (b x)

    bindbart_shift_future_iff : forall (i : level) (a : U i) .
                                   forallfut (b : a -> U i) .
                                     forall (e : bar a) .
                                       (bindbart x = e in future (b x))
                                         <-> future (bindbart x = e in b x)

    bindbart_commute : forall
                          (i : level)
                          (a b : U i)
                          (c : a -> b -> U i)
                          (e1 : bar a)
                          (e2 : bar b) .
                          (bindbart x = e1 in bindbart y = e2 in c x y)
                          -> bindbart y = e2 in bindbart x = e1 in c x y

    bindbart_commute_iff : forall
                              (i : level)
                              (a b : U i)
                              (c : a -> b -> U i)
                              (e1 : bar a)
                              (e2 : bar b) .
                              (bindbart x = e1 in bindbart y = e2 in c x y)
                                <-> (bindbart y = e2 in bindbart x = e1 in c x y)

    sqstable_bindbart : intersect (i : level) (a : U i) (b : a -> U i) .
                           forall (e : bar a) .
                             (forall (x : a) . Sqstable.sqstable (b x))
                             -> Sqstable.sqstable (`bindbart e b)
