# `RealSequence`

Expressions in this file are rendered using the `real`
[overloading mode](../overloading.html).

### Natural-number exponents

    nexpr : real -> nat -> real
          = fn x . (fnind nat_fn : forall (v0 : nat) . real of
                     | zero . 1
                     | succ n . x * nat_fn n)

    nexpr_positive : forall (a : real) (n : nat) . 0 < a -> 0 < nexpr a n

    nexpr_nonnegative : forall (a : real) (n : nat) . 0 <= a -> 0 <= nexpr a n

    nexpr_nonzero : forall (x : real) (n : nat) . x != 0 : real -> nexpr x n != 0 : real

    nexpr_plus : forall (a : real) (m n : nat) . nexpr a (m +n n) = nexpr a m * nexpr a n : real

    nexpr_times : forall (a : real) (m n : nat) . nexpr a (m *n n) = nexpr (nexpr a m) n : real

    nexpr_mono_base : forall (a a' : real) (n : nat) .
                         0 <= a -> a <= a' -> nexpr a n <= nexpr a' n

    nexpr_leqr_one : forall (x : real) (n : nat) . 0 <= x -> x <= 1 -> nexpr x n <= 1

    nexpr_invr : forall (x : nonzero_real) (n : nat) . nexpr (invr x) n = invr (nexpr x n) : real


### Miscellaneous

    bernoullis_inequality : forall (x : real) (n : nat) .
                               -1 <= x -> 1 + nat_to_real n * x <= nexpr (1 + x) n

    exp_to_real : forall (a n : nat) .
                     nat_to_real (Division.exp a n) = nexpr (nat_to_real a) n : real

    logarithm_bound : forall (x y : real) .
                         1 < x -> Squish.squish (exists (n : nat) . y < nexpr x n)


### Prereals

    prenexpr : prereal -> nat -> prereal
             = fn x . (fnind nat_fn : forall (v0 : nat) . prereal of
                        | zero . integer_to_prereal z`1
                        | succ n . pretimesr x (nat_fn n))

    prenexpr_to_real : forall (x : prereal) (n : nat) .
                          realintro (prenexpr x n) = nexpr (realintro x) n : real

    exp_to_prereal : forall (a n : nat) .
                        integer_to_prereal (Integer.nat_to_integer (Division.exp a n))
                          = prenexpr (integer_to_prereal (Integer.nat_to_integer a)) n
                          : prereal

    logarithm_bound_prereal : forall (x y : prereal) .
                                 1 < realintro x
                                 -> exists (n : nat) . realintro y < nexpr (realintro x) n
