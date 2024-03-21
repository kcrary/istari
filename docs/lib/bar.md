# `Bar` (partial types)

Inspired by the partial types ("bar types") of Constable and Smith [1],
but weaker, because we cannot implement the termination predicate.

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

The reduction for `ffix` is:

    ffix f --> f (next (ffix f))

It appears in the registry under the name `Bar.unroll_ffix`.  It can
also be used through the `unroll` tactic.


The partial type `bar A` provides an `A` now, or sometime later:

    bar : intersect (i : level) . U i -> U i
        = fn a . rec t . a % future t

    bar_unroll : forall (i : level) (a : U i) . bar a = (a % future (bar a)) : type

The partial type acts as a monad.  Its unit is `now`:

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

    bindbar (now x) f --> f x ;
    bindbar (laterf x) f --> let next y = x in later (`bindbar y f)
    bindbar (later x) f --> later (`bindbar x f)

The syntactic sugar `bindbar x = m in n` is accepted for 
`` `bindbar m (fn x . n)``.


Observe that `bindbar` always produces an element of some `bar` type.  A
variation on it, `bindbart`, produces a type instead:

    bindbart : intersect (i : level) (a : U i) . bar a -> (a -> U i) -> U i

    bindbart (now x) b --> b x ;
    bindbart (laterf x) b --> let next y = x in future (`bindbart y b) ;
    bindbart (later x) b --> future (`bindbart x b) ;

The syntactic sugar `bindbart x = m in b` is accepted for 
`` `bindbart m (fn x . b)``.


Bar is covariant:

    bar_subtype : forall (i : level) (a b : U i) . a <: b -> bar a <: bar b


Finally we can define a fixpoint operator on partial objects:

    bfix : intersect (i : level) (a : U i) . (bar a -> bar a) -> bar a
         = fn f . ffix (fn x . f (laterf x))

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

    bar_iter : intersect (i : level) (a : U i) .
                  forall (P : bar a -> U i) .
                    (forall (x : a) . P (now x))
                    -> (forall (xf : future (bar a)) .
                          let next x = xf in future (P x) -> P (later x))
                    -> forall (x : bar a) . P x

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
