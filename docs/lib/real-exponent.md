# `RealExponent`

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

    one_leqr_nexpr : forall (a : real) (n : nat) . 1 <= a -> 1 <= nexpr a n

    nexpr_leqr_one : forall (x : real) (n : nat) . 0 <= x -> x <= 1 -> nexpr x n <= 1

    nexpr_plus_exponent : forall (a : real) (m n : nat) .
                             nexpr a (m +n n) = nexpr a m * nexpr a n : real

    nexpr_times_exponent : forall (a : real) (m n : nat) .
                              nexpr a (m *n n) = nexpr (nexpr a m) n : real

    nexpr_times_base : forall (a b : real) (n : nat) .
                          nexpr (a * b) n = nexpr a n * nexpr b n : real

    nexpr_mono_base : forall (a a' : real) (n : nat) .
                         0 <= a -> a <= a' -> nexpr a n <= nexpr a' n

    nexpr_mono_exponent : forall (a : real) (m n : nat) .
                             1 <= a -> m <n= n -> nexpr a m <= nexpr a n

    nexpr_anti_exponent : forall (a : real) (m n : nat) .
                             0 <= a -> a <= 1 -> m <n= n -> nexpr a n <= nexpr a m

    nexpr_one : forall (n : nat) . nexpr 1 n = 1 : real

    nexpr_minus_one : forall (n : nat) .
                         nexpr -1 n = (if Division.is_even n then 1 else -1) : real

    nexpr_invr : forall (x : nonzero_real) (n : nat) . nexpr (invr x) n = invr (nexpr x n) : real


### Integer exponents

    zexpr : nonzero_real -> integer -> real
          = fn x k .
               if z`0 <z=? k
               then nexpr x (Integer.integer_to_nat k)
               else invr (nexpr x (Integer.integer_to_nat (~z k)))

    zexpr_positive : forall (x : real) (k : integer) . 0 < x -> 0 < zexpr x k

    zexpr_nonzero : forall (x : nonzero_real) (k : integer) . zexpr x k != 0 : real

    nexpr_to_zexpr : forall (x : nonzero_real) (n : nat) .
                        nexpr x n = zexpr x (Integer.nat_to_integer n) : real

    zexpr_nonneg_exponent : forall (x : nonzero_real) (k : integer) .
                               z`0 <z= k -> zexpr x k = nexpr x (Integer.integer_to_nat k) : real

    zexpr_nonpos_exponent : forall (x : nonzero_real) (k : integer) .
                               k <z= z`0
                               -> zexpr x k = invr (nexpr x (Integer.integer_to_nat (~z k))) : real

    zexpr_plus_exponent : forall (a : nonzero_real) (k l : integer) .
                             zexpr a (k +z l) = zexpr a k * zexpr a l : real

    zexpr_negate_exponent : forall (x : nonzero_real) (k : integer) .
                               zexpr x (~z k) = invr (zexpr x k) : real

    zexpr_negate_exponent' : forall (x : nonzero_real) (k : integer) .
                                zexpr x k = invr (zexpr x (~z k)) : real

    zexpr_times_exponent : forall (a : nonzero_real) (k l : integer) .
                              zexpr a (k *z l) = zexpr (zexpr a k) l : real

    zexpr_times_base : forall (a b : nonzero_real) (k : integer) .
                          zexpr (a * b) k = zexpr a k * zexpr b k : real

    zexpr_mono_base : forall (a a' : real) (k : integer) .
                         0 < a -> a <= a' -> z`0 <z= k -> zexpr a k <= zexpr a' k

    zexpr_anti_base : forall (a a' : real) (k : integer) .
                         0 < a -> a <= a' -> k <z= z`0 -> zexpr a' k <= zexpr a k

    zexpr_mono_exponent : forall (a : real) (k l : integer) .
                             1 <= a -> k <z= l -> zexpr a k <= zexpr a l

    zexpr_anti_exponent : forall (a : real) (k l : integer) .
                             0 < a -> a <= 1 -> k <z= l -> zexpr a l <= zexpr a k

    zexpr_one : forall (k : integer) . zexpr 1 k = 1 : real

    zexpr_invr : forall (x : nonzero_real) (k : integer) .
                    zexpr (invr x) k = invr (zexpr x k) : real


### Miscellaneous

    bernoullis_inequality : forall (x : real) (n : nat) .
                               -1 <= x -> 1 + nat_to_real n * x <= nexpr (1 + x) n

    exp_to_real : forall (a n : nat) .
                     nat_to_real (Division.exp a n) = nexpr (nat_to_real a) n : real

    logarithm_bound : forall (x y : real) .
                         1 < x -> Squish.squish (exists (n : nat) . y < nexpr x n)

    absr_nexpr_minus_one : forall (n : nat) . absr (nexpr -1 n) = 1 : real

    nexpr_minus_one_squared : forall (n : nat) . nexpr -1 n * nexpr -1 n = 1 : real


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
