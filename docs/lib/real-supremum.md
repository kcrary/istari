# `RealSupremum`

Expressions in this file are rendered using the `real`
[overloading mode](../overloading.html).

    supremum : intersect (i : level) . (real -> U i) -> real -> U i
             = fn P b .
                  (forall (x : real) . P x -> x <= b)
                  & (forall (e : real) .
                       0 < e -> Squish.squish (exists (x : real) . P x & b - e < x))

    supremum_ub : forall (i : level) (P : real -> U i) (b x : real) .
                     supremum P b -> P x -> x <= b

The way least-upper-bound is defined in `supremum` is classically
equivalent to the usual definition, but it is stronger constructively.
(Note the not-not in `classical_lub_to_constructive`.)

    constructive_lub_to_classical : forall (i : level) (P : real -> U i) (b : real) .
                                       (forall (e : real) .
                                          0 < e
                                          -> Squish.squish (exists (x : real) . P x & b - e < x))
                                       -> forall (x : real) .
                                            (forall (y : real) . P y -> y <= x) -> b <= x

    classical_lub_to_constructive : forall (i : level) (P : real -> U i) (b : real) .
                                       (forall (x : real) .
                                          (forall (y : real) . P y -> y <= x) -> b <= x)
                                       -> forall (e : real) .
                                            0 < e
                                            -> not (not (exists (x : real) . P x & b - e < x))

    supremum_lub : forall (i : level) (P : real -> U i) (b x : real) .
                      supremum P b -> (forall (y : real) . P y -> y <= x) -> b <= x

    supremum_unique : forall (i : level) (P : real -> U i) (b b' : real) .
                         supremum P b -> supremum P b' -> b = b' : real

    supremum_ext : forall (i : level) (P : real -> U i) (b : real) (h h' : supremum P b) .
                      h = h' : supremum P b

Classically, a supremum exists for every nonempty, bounded set.  We
require an additional condition to make the supremum computable: for
any `x < y`, either `x` is not an upper bound or `y` is an upper
bound.  (Another sufficient condition would be that it is decidable
whether an arbitrary real is an upper bound or not, but that condition
is typically false.)

    supremum_exists : forall (i : level) (P : real -> U i) (a b : real) .
                         (forall (x : real) . Sqstable.sqstable (P x))
                         -> P a
                         -> (forall (x : real) . P x -> x <= b)
                         -> (forall (x y : real) .
                               x < y
                               -> Squish.squish
                                    ((exists (z : real) . P z & x < z)
                                     % (forall (z : real) . P z -> z <= y)))
                         -> exists (c : real) . supremum P c

The above includes the technical condition that the predicate defining
the set be squash-stable.  That requirement can be weakened:

    supremum_exists_sqsq : forall (i : level) (P : real -> U i) (a b : real) .
                              (forall (x : real) . { P x } -> Squish.squish (P x))
                              -> P a
                              -> (forall (x : real) . P x -> x <= b)
                              -> (forall (x y : real) .
                                    x < y
                                    -> Squish.squish
                                         ((exists (z : real) . P z & x < z)
                                          % (forall (z : real) . P z -> z <= y)))
                              -> exists (c : real) . supremum P c

    supremum_exists_symmetrical : forall (i : level) (P : real -> U i) (a b : real) .
                                     (forall (x : real) . Quotient.symmetrical (P x))
                                     -> P a
                                     -> (forall (x : real) . P x -> x <= b)
                                     -> (forall (x y : real) .
                                           x < y
                                           -> Squish.squish
                                                ((exists (z : real) . P z & x < z)
                                                 % (forall (z : real) . P z -> z <= y)))
                                     -> exists (c : real) . supremum P c

In this last and most general version, the predicate is required to be
*symmetrical* in the sense of [`Quotient`](quotient.html).  This
condition holds with considerable generality.  It is required (in
`infinite_sequence_squish`, below) in order to turn a sequence of
squished, qualifying elements into a squished sequence of qualifying
elements.


### Tools for constructing infinite sequences

    infinite_sequence : forall
                           (lv : level)
                           (A : U lv)
                           (P : nat -> A -> U lv)
                           (R : A -> A -> U lv)
                           (a : A) .
                           P n`0 a
                           -> (forall (i : nat) (x : A) .
                                 P i x -> exists (y : A) . P (succ i) y & R x y)
                           -> exists (f : nat -> A) .
                                f n`0 = a : A
                                & (forall (i : nat) . P i (f i) & R (f i) (f (succ i)))

    infinite_sequence_squish : forall
                                  (lv : level)
                                  (A : U lv)
                                  (P : nat -> A -> U lv)
                                  (R : A -> A -> U lv)
                                  (a : A) .
                                  Quotient.symmetrical A
                                  -> (forall (i : nat) (x : A) . Quotient.symmetrical (P i x))
                                  -> (forall (x y : A) . Quotient.symmetrical (R x y))
                                  -> P n`0 a
                                  -> (forall (i : nat) (x : A) .
                                        P i x
                                        -> Squish.squish (exists (y : A) . P (succ i) y & R x y))
                                  -> Squish.squish
                                       (exists (f : nat -> A) .
                                          f n`0 = a : A
                                          & (forall (i : nat) . P i (f i) & R (f i) (f (succ i))))
