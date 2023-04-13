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

    ffix : intersect (i : level) . forall (a : U i) . (future a -> a) -> a
         = fn a f .
              pause
                (fn x . f (let next x' = x in next (pause x' x)))
                (next (fn x . f (let next x' = x in next (pause x' x))))

The reduction for `ffix` is:

    ffix A f --> f (next (ffix A f))

It appears in the registry under the name `Bar.unroll_ffix`.  It can
also be used through the `unroll` tactic.


The partial type `bar A` provides an `A` now, or sometime later:

    bar : intersect (i : level) . U i -> U i
        = fn a . rec t . a % future t

    bar_unroll : forall (i : level) (a : U i) . bar a = (a % future (bar a)) : type

The partial type acts as a monad.  Its unit is `now`:

    now : intersect (i : level) . forall (a : U i) . a -> bar a
        = fn a x . inl x
        (1 implicit argument)

Another intro form is `later`:

    later : intersect (i : level) . forall (a : U i) . bar a -> bar a
          = fn a x . inr (next x)
          (1 implicit argument)

The monadic bind is `bindbar`:

    bindbar : intersect (i : level) . forall (a b : U i) . bar a -> (a -> bar b) -> bar b
            = fn a b x f .
                 ffix
                   (bar a -> bar b)
                   (fn g x1 .
                     (case x1 of
                      | inl y . f y
                      | inr y . let next g' = g in let next y' = y in inr (next (g' y'))))
                   x
            (2 implicit arguments)

    bindbar _ _ (now _ x) f --> f x
    bindbar A B (later _ x) f --> later B (` bindbar A B x f)

The syntactic sugar `bindbar x = m in n` is accepted for 
`` ` bindbar _ _ m (fn x . n)``.

   

Finally we can define a fixpoint operator on partial objects:

    bfix : intersect (i : level) . forall (a : U i) . (bar a -> bar a) -> bar a
         = fn a f . ffix (bar a) (fn x . f (inr x))
         (1 implicit argument)


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
