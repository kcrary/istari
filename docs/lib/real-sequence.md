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

    converges_equal : forall (s s' : nat -> real) (x : real) (n : nat) .
                         (forall (i : nat) . n <n= i -> s i = s' i : real)
                         -> converges s x
                         -> converges s' x

    converges_from_tail : forall (s : nat -> real) (n : nat) (x : real) .
                             converges (fn i . s (i +n n)) x -> converges s x

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

    cauchy_iff_converges : forall (s : nat -> real) .
                              cauchy s <-> (exists (x : real) . converges s x)

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

    converges_leqr : forall (s s' : nat -> real) (x y : real) (n : nat) .
                        converges s x
                        -> converges s' y
                        -> (forall (i : nat) . n <n= i -> s i <= s' i)
                        -> x <= y

When an increasing sequence and a decreasing sequence, with the
decreasing sequence above the increasing one, and they grow closer at
a steady rate, both sequences converge to the same value.
    
    dual_convergence : forall (s1 s2 : nat -> real) (c : real) .
                          0 < c
                          -> c < 1
                          -> (forall (i : nat) . s1 i <= s2 i)
                          -> (forall (i j : nat) . i <n= j -> s1 i <= s1 j & s2 j <= s2 i)
                          -> (forall (i : nat) . s2 (succ i) - s1 (succ i) <= c * (s2 i - s1 i))
                          -> exists (x : real) . converges s1 x & converges s2 x


### Series

The partial sum operator turns a series into a sequence:

    sums : (nat -> real) -> nat -> real
         = fn s . (fnind nat_fn : forall (v0 : nat) . real of
                    | zero . 0
                    | succ n . s n + nat_fn n)

The segment sum `sums s m n` adds the elements from `s m` (inclusive)
to `s n` (exclusive):

    ssums_all : forall (s : nat -> real) (n : nat) . sums s n = ssums s n`0 n : real

    ssums_split : forall (s : nat -> real) (m k n : nat) .
                     m <n= k -> k <n= n -> ssums s m n = ssums s m k + ssums s k n : real

    sums_split : forall (s : nat -> real) (m n : nat) .
                    m <n= n -> sums s n = sums s m + ssums s m n : real

    sums_difference : forall (s : nat -> real) (m n : nat) .
                         m <n= n -> ssums s m n = sums s n - sums s m : real

    ssums_empty : forall (s : nat -> real) (n : nat) . ssums s n n = 0 : real

    ssums_singleton : forall (s : nat -> real) (n : nat) . ssums s n (succ n) = s n : real

    ssums_left : forall (s : nat -> real) (m n : nat) .
                    m <n n -> ssums s m n = s m + ssums s (succ m) n : real

    ssums_right : forall (s : nat -> real) (m n : nat) .
                     m <n n -> ssums s m n = s (Nat.pred n) + ssums s m (Nat.pred n) : real

    ssums_right_succ : forall (s : nat -> real) (m n : nat) .
                          m <n= n -> ssums s m (succ n) = s n + ssums s m n : real

We use the word "convergent" (as opposed to "converges"), to say that
a series converges.  (More precisely, to say that its partial sums
converge.)  Since we do not define "convergent" formally (we just use
it in names), we can use it loosely to refer both to when a series
converges (at all) and to when it converges to a particular value.

    convergent_absolutely : (nat -> real) -> U 0
                          = fn s . cauchy (sums (fn i . absr (s i)))

    convergent_absolutely_impl_convergent : forall (s : nat -> real) .
                                               convergent_absolutely s -> cauchy (sums s)

    convergent_impl_converges_zero : forall (s : nat -> real) . cauchy (sums s) -> converges s 0

    convergent_plusr : forall (s s' : nat -> real) (x y : real) .
                          converges (sums s) x
                          -> converges (sums s') y
                          -> converges (sums (fn i . s i + s' i)) (x + y)

    convergent_timesr_const : forall (s : nat -> real) (x y : real) .
                                 converges (sums s) y -> converges (sums (fn i . x * s i)) (x * y)

    sums_nexpr_increment : forall (x : real) (n : nat) .
                              x * sums (fn i . RealExponent.nexpr x i) n
                                = sums (fn i . RealExponent.nexpr x i) (succ n) - 1
                                : real

    convergent_nexpr : forall (x : real) .
                          0 < x
                          -> x < 1
                          -> converges (sums (fn i . RealExponent.nexpr x i)) (invr (1 - x))

    comparison_test : forall (s s' : nat -> real) (n : nat) .
                         cauchy (sums s')
                         -> (forall (i : nat) . n <n= i -> absr (s i) <= s' i)
                         -> cauchy (sums s)

    convergent_split : forall (s : nat -> real) (n : nat) (x : real) .
                          converges (sums (fn i . s (i +n n))) x
                          -> converges (sums s) (sums s n + x)

    convergent_from_tail : forall (s : nat -> real) (n : nat) .
                              cauchy (sums (fn i . s (i +n n))) -> cauchy (sums s)

    ratio_test : forall (s : nat -> real) (c : real) (n : nat) .
                    0 < c
                    -> c < 1
                    -> (forall (i : nat) . n <n= i -> absr (s (succ i)) <= c * absr (s i))
                    -> cauchy (sums s)

    convergent_alternation : forall (s : nat -> real) .
                                (forall (i : nat) . 0 <= s i)
                                -> (forall (i : nat) . s (succ i) <= s i)
                                -> converges s 0
                                -> cauchy (sums (fn i . RealExponent.nexpr -1 i * s i))
