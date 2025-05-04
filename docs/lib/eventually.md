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

It appears in the registry under the name `Eventually.unroll_ffix`.  It can
also be used through the `unroll` tactic.


The simulated partial type `ev A` provides an `A` now, or sometime later:

    ev : intersect (i : level) . U i -> U i
        = fn a . rec t . a % future t

    ev_unroll : forall (i : level) (a : U i) . ev a = (a % future (ev a)) : type

The type acts as a monad.  Its unit is `now`:

    now : intersect (i : level) (a : U i) . a -> ev a
        = fn x . inl x

Another intro form is `laterf`:

    laterf : intersect (i : level) (a : U i) . future (ev a) -> ev a
           = fn x . inr x

The `laterf` form is very often used with `next`, so we define:

    later : intersect (i : level) (a : U i) . ev a -> ev a
          = fn x . laterf (next x)

The monadic bind is `bindev`:

    bindev : intersect (i : level) (a b : U i) . ev a -> (a -> ev b) -> ev b

    `bindev (now x) f --> f x ;
    `bindev (laterf x) f --> let next y = x in later (`bindev y f)
    `bindev (later x) f --> later (`bindev x f)

The syntactic sugar `bindev x = m in n` is accepted for 
`` `bindev m (fn x . n)``.

The monad laws are respected:

    bindev_id_left : forall (i : level) (a b : U i) (e : a) (f : a -> ev b) .
                        (bindev x = now e in f x) = f e : ev b

    bindev_id_right : forall (i : level) (a : U i) (m : ev a) . (bindev x = m in now x) = m : ev a

    bindev_assoc : forall (i : level) (a b c : U i) (e : ev a) (f : a -> ev b) (g : b -> ev c) .
                      (bindev y = (bindev x = e in f x) in g y)
                        = (bindev x = e in bindev y = f x in g y)
                        : ev c


Observe that `bindev` always produces an element of some `ev` type.  A
variation on it, `bindevt`, produces a type instead:

    bindevt : intersect (i : level) (a : U i) . ev a -> (a -> U i) -> U i

    `bindevt (now x) t --> t x ;
    `bindevt (laterf x) t --> let next y = x in future (`bindevt y t) ;
    `bindevt (later x) t --> future (`bindevt x t) ;

The syntactic sugar `bindevt x = m in b` is accepted for 
`` `bindevt m (fn x . b)``.

The monad laws for `bindevt`:

    bindevt_id_left : forall (i : level) (a : U i) (e : a) (t : a -> U i) .
                         bindevt x = now e in t x = t e : U i

    bindevt_assoc : forall (i : level) (a b : U i) (e : ev a) (f : a -> ev b) (t : b -> U i) .
                       (bindevt y = (bindev x = e in f x) in t y)
                         = (bindevt x = e in bindevt y = f x in t y)
                         : U i


Ev is covariant and preserves extensional equality:

    ev_subtype : forall (i : level) (a b : U i) . a <: b -> ev a <: ev b

    ev_eeqtp : forall (i : level) (a b : U i) . a <:> b -> ev a <:> ev b


Finally we can define a fixpoint operator on simulated partial objects:

    efix : intersect (i : level) (a : U i) . (ev a -> ev a) -> ev a
         = fn f . ffix (fn x . f (laterf x))

The reduction for `efix` is:

    efix f --> f (later (efix f))

It appears in the registry under the name `Eventually.unroll_efix`.  It can
also be used through the `unroll` tactic.


We can iterate over simulated partial objects using the `ev_iter` iterator.
The cases are `now` and `later`:

    ev_iter : intersect (i : level) (a : U i) (P : ev a -> U i) .
                 (forall (x : a) . P (now x))
                 -> (forall (xf : future (ev a)) . let next x = xf in future (P x) -> P (later x))
                 -> forall (x : ev a) . P x

    ev_iter hn _ (now x) --> hn x
    ev_iter hn hl (laterf x) --> let next y = x in hl (next y) (next (ev_iter P hn hl y))
    ev_iter hn hl (later x) --> hl (next x) (next (ev_iter P hn hl x))

This is employed automatically by the `induction` tactic on hypotheses
of `ev` type.

Several corollaries of induction pertaining to `bindevt`:

    bindevt_simple : parametric (i : level) (a : U i) .
                        forall (e : ev a) .
                          parametric (t : a -> U i) .
                            (forall (x : a) . t x) -> bindevt x = e in t x

    bindevt_map : forall (i : level) (a : U i) (b c : a -> U i) (e : ev a) .
                     (forall (x : a) . b x -> c x)
                     -> (bindevt x = e in b x)
                     -> bindevt x = e in c x

    bindevt_shift_future_out : forall (i : level) (a : U i) .
                                  forallfut (b : a -> U i) .
                                    forall (e : ev a) .
                                      (bindevt x = e in future (b x))
                                      -> future (bindevt x = e in b x)

    bindevt_shift_future_in : forall (i : level) (a : U i) .
                                 forallfut (b : a -> U i) .
                                   forall (e : ev a) .
                                     future (bindevt x = e in b x) -> bindevt x = e in future (b x)

    bindevt_shift_future_iff : forall (i : level) (a : U i) .
                                  forallfut (b : a -> U i) .
                                    forall (e : ev a) .
                                      (bindevt x = e in future (b x))
                                        <-> future (bindevt x = e in b x)

    bindevt_commute : forall (i : level) (a b : U i) (c : a -> b -> U i) (e1 : ev a) (e2 : ev b) .
                         (bindevt x = e1 in bindevt y = e2 in c x y)
                         -> bindevt y = e2 in bindevt x = e1 in c x y

    bindevt_commute_iff : forall
                             (i : level)
                             (a b : U i)
                             (c : a -> b -> U i)
                             (e1 : ev a)
                             (e2 : ev b) .
                             (bindevt x = e1 in bindevt y = e2 in c x y)
                               <-> (bindevt y = e2 in bindevt x = e1 in c x y)

    sqstable_bindevt : intersect (i : level) (a : U i) (b : a -> U i) .
                          forall (e : ev a) .
                            (forall (x : a) . Sqstable.sqstable (b x))
                            -> Sqstable.sqstable (`bindevt e b)
