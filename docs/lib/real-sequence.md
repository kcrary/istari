# `RealSequence`

Expressions in this file are rendered using the `real`
[overloading mode](../overloading.html).

### Convergence

    converges : intersect (i : level) . (nat -> real) -> real -> U i
              = fn s x .
                   Squish.squish
                     (forall (k : nat) .
                        n`0 <n k
                        -> exists (m : nat) .
                             forall (n : nat) . m <n= n -> absr (s n - x) <= invr (nat_to_real k))

    converges_unique : forall (s : nat -> real) (x y : real) .
                          converges s x -> converges s y -> x = y : real

    converges_equal : forall (s s' : nat -> real) (x : real) .
                         (forall (i : nat) . n`0 <n i -> s i = s' i : real)
                         -> converges s x
                         -> converges s' x

    cauchy : intersect (i : level) . (nat -> real) -> U i
           = fn s .
                Squish.squish
                  (forall (k : nat) .
                     n`0 <n k
                     -> exists (m : nat) .
                          forall (n p : nat) .
                            m <n= n -> m <n= p -> absr (s n - s p) <= invr (nat_to_real k))

    cauchy_impl_converges : forall (s : nat -> real) .
                               cauchy s -> exists (x : real) . converges s x

    converges_impl_cauchy : forall (s : nat -> real) (x : real) . converges s x -> cauchy s

    converges_constant : forall (x : real) . converges (fn v0 . x) x

    converges_plusr : forall (s s' : nat -> real) (x y : real) .
                         converges s x -> converges s' y -> converges (fn i . s i + s' i) (x + y)

    converges_negr : forall (s : nat -> real) (x : real) .
                        converges s x -> converges (fn i . ~ (s i)) (~ x)

    converges_minusr : forall (s s' : nat -> real) (x y : real) .
                          converges s x -> converges s' y -> converges (fn i . s i - s' i) (x - y)

    converges_timesr : forall (s s' : nat -> real) (x y : real) .
                          converges s x -> converges s' y -> converges (fn i . s i * s' i) (x * y)

    converges_invr : forall (s : nat -> nonzero_real) (x : nonzero_real) .
                        converges s x -> converges (fn i . invr (s i)) (invr x)

    converges_maxr : forall (s s' : nat -> real) (x y : real) .
                        converges s x
                        -> converges s' y
                        -> converges (fn i . maxr (s i) (s' i)) (maxr x y)

    converges_minr : forall (s s' : nat -> real) (x y : real) .
                        converges s x
                        -> converges s' y
                        -> converges (fn i . minr (s i) (s' i)) (minr x y)

    converges_leqr : forall (s s' : nat -> real) (x y : real) .
                        converges s x
                        -> converges s' y
                        -> (forall (i : nat) . n`0 <n i -> s i <= s' i)
                        -> x <= y
