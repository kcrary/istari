# `Division` (natural number division)

Since divisors must be nonzero, we define `pos` as an abbreviation
(*i.e.,* a soft constant):

    pos : U 0
        = { n : nat | 0 < n }


### Div and Mod

    div : nat -> pos -> nat
        =rec= fn a b . if a <? b then 0 else succ (div (a - b) b)

    mod : nat -> pos -> nat
        =rec= fn a b . if a <? b then a else mod (a - b) b

To save the expense of computing the recursion twice, `divmod` does
both at the same time:

    divmod : nat -> pos -> nat & nat
           =rec= fn a b .
                    if a <? b then (0, a) else (let (q, r) = divmod (a - b) b in (succ q, r))

    divmod_equal : forall (a : nat) (b : pos) . divmod a b = (div a b, mod a b) : (nat & nat)

The defining properties of `div` and `mod`:

    mod_lt_r : forall (a : nat) (b : pos) . mod a b < b

    div_prop : forall (a : nat) (b : pos) . div a b * b + mod a b = a : nat

The latter, restated in two different ways:

    div_prop' : forall (a : nat) (b : pos) . div a b * b = a - mod a b : nat

    mod_prop : forall (a : nat) (b : pos) . mod a b = a - div a b * b : nat

The quotient and remainder are uniquely defined:

    division_property : forall (a : nat) (b : pos) (q r : nat) .
                           a = q * b + r : nat -> r < b -> div a b = q : nat & mod a b = r : nat

    division_unique : forall (a : nat) (b : pos) (q q' r r' : nat) .
                         a = q * b + r : nat
                         -> a = q' * b + r' : nat
                         -> r < b
                         -> r' < b
                         -> q = q' : nat & r = r' : nat

    div_leq_l : forall (a : nat) (b : pos) . div a b <= a

    mod_leq_l : forall (a : nat) (b : pos) . mod a b <= a

    div_times_r : forall (a : nat) (b : pos) . div (a * b) b = a : nat

    div_times_l : forall (a : nat) (b : pos) . div (b * a) b = a : nat

    mod_times_r : forall (a : nat) (b : pos) . mod (a * b) b = 0 : nat

    mod_times_l : forall (a : nat) (b : pos) . mod (b * a) b = 0 : nat

    div_0 : forall (a : pos) . div 0 a = 0 : nat

    mod_0 : forall (a : pos) . mod 0 a = 0 : nat

    div_1 : forall (a : nat) . div a 1 = a : nat

    mod_1 : forall (a : nat) . mod a 1 = 0 : nat

    div_self : forall (a : pos) . div a a = 1 : nat

    mod_self : forall (a : pos) . mod a a = 0 : nat

    div_operands_lt : forall (a : nat) (b : pos) . a < b -> div a b = 0 : nat

    mod_operands_lt : forall (a : nat) (b : pos) . a < b -> mod a b = a : nat

    div_mono : forall (a b : nat) (c : pos) . a <= b -> div a c <= div b c

    mod_idem : forall (a : nat) (b : pos) . mod a b = mod (mod a b) b : nat

    div_plus_r : forall (a : nat) (b : pos) . div (a + b) b = succ (div a b) : nat

    div_plus_l : forall (a : nat) (b : pos) . div (b + a) b = succ (div a b) : nat

    mod_plus_r : forall (a : nat) (b : pos) . mod (a + b) b = mod a b : nat

    mod_plus_l : forall (a : nat) (b : pos) . mod (b + a) b = mod a b : nat

    times_div_r : forall (a : nat) (b : pos) . b * div a b = a - mod a b : nat

    times_div_l : forall (a : nat) (b : pos) . div a b * b = a - mod a b : nat

    div_assoc : forall (a : nat) (b c : pos) . div (div a b) c = div a (b * c) : nat

This relates the remainders of the divisions in `div_assoc`:

    div_assoc_remainder : forall (a : nat) (b c : pos) .
                             mod (div a b) c * b + mod a b = mod a (b * c) : nat

    mod_plus_alt : forall (a b : nat) (c : pos) . mod (a + b) c = mod (mod a c + b) c : nat

    mod_plus_alt2 : forall (a b : nat) (c : pos) . mod (a + b) c = mod (mod a c + mod b c) c : nat

    mod_times_alt : forall (a b : nat) (c : pos) . mod (a * b) c = mod (mod a c * b) c : nat

    mod_times_alt2 : forall (a b : nat) (c : pos) .
                        mod (a * b) c = mod (mod a c * mod b c) c : nat

    div_times_alt : forall (a b : nat) (c : pos) . div a c * b <= div (a * b) c


### Divides predicate

    divides : nat -> nat -> U 0
            = fn a b . exists (n : nat) . a * n = b : nat

    divides_iff_modulus : forall (a : pos) (b : nat) . divides a b <-> mod b a = 0 : nat

    divides_1 : forall (a : nat) . divides 1 a

    divides_0 : forall (a : nat) . divides a 0

    divides_refl : forall (a : nat) . divides a a

    divides_trans : forall (a b c : nat) . divides a b -> divides b c -> divides a c

    divides_antisymm : forall (a b : nat) . divides a b -> divides b a -> a = b : nat

    divides_product_r : forall (a b : nat) . divides a (a * b)

    divides_product_l : forall (a b : nat) . divides a (b * a)

    divides_plus : forall (a b c : nat) . divides a b -> divides a c -> divides a (b + c)

    divides_minus : forall (a b c : nat) . divides a b -> divides a c -> divides a (b - c)

    divides_times_times_r : forall (a b c : nat) . divides a b -> divides (a * c) (b * c)

    divides_times_times_l : forall (a b c : nat) . divides a b -> divides (c * a) (c * b)

    divides_times_r : forall (a b c : nat) . divides a b -> divides a (b * c)

    divides_times_l : forall (a b c : nat) . divides a b -> divides a (c * b)

    divides_mod : forall (a b : nat) (c : pos) . divides a b -> divides a c -> divides a (mod b c)

    divides_div : forall (a b : nat) (c : pos) . divides (a * c) b -> divides a (div b c)

    divides_impl_leq : forall (a b : nat) . 0 < b -> divides a b -> a <= b

    modulus_implies_mod_eq : forall (a b : nat) (c : pos) .
                                a <= b -> divides c (b - a) -> mod a c = mod b c : nat


### Greatest common divisor

    gcd : pos -> pos -> pos
        =rec= fn a b . if mod a b =? 0 then b else gcd b (mod a b)

    gcd_positive : forall (a b : pos) . 0 < gcd a b

    gcd_divides_l : forall (a b : pos) . divides (gcd a b) a

    gcd_divides_r : forall (a b : pos) . divides (gcd a b) b

    gcd_glb : forall (a b : pos) (n : nat) . divides n a -> divides n b -> divides n (gcd a b)

    gcd_commute : forall (a b : pos) . gcd a b = gcd b a : nat

    gcd_assoc : forall (a b c : pos) . gcd (gcd a b) c = gcd a (gcd b c) : nat

    gcd_ann_r : forall (a : pos) . gcd a 1 = 1 : nat

    gcd_ann_l : forall (a : pos) . gcd 1 a = 1 : nat


### Logarithms

    exp : nat -> nat -> nat
        = fn a . (fnind nat_fn : forall (v0 : nat) . nat of
                   | zero . 1
                   | succ n . nat_fn n * a)

    exp_positive : forall (a n : nat) . 0 < a -> 0 < exp a n

    exp_plus : forall (a m n : nat) . exp a (m + n) = exp a m * exp a n : nat

    exp_times : forall (a m n : nat) . exp a (m * n) = exp (exp a m) n : nat

    exp_mono_base : forall (a a' b : nat) . a <= a' -> exp a b <= exp a' b

    exp_mono_exponent : forall (a b b' : nat) . 0 < a -> b <= b' -> exp a b <= exp a b'

    exp_mono : forall (a a' b b' : nat) . 0 < a -> a <= a' -> b <= b' -> exp a b <= exp a' b'

We arbitrarily set `log2 0 = 0`, so that `log2` can be defined for every natural number.

    log2 : nat -> nat
         =rec= fn a . if a <? 2 then 0 else succ (log2 (div a 2))

    log2_mono : forall (a b : nat) . a <= b -> log2 a <= log2 b

    log2_one : log2 1 = 0 : nat

    log2_even : forall (a : nat) . 0 < a -> log2 (a * 2) = succ (log2 a) : nat

    log2_odd : forall (a : nat) . 0 < a -> log2 (succ (a * 2)) = succ (log2 a) : nat

    log2_two : log2 2 = 1 : nat

    log2_exp_inverse : forall (n : nat) . log2 (exp 2 n) = n : nat

    log2_spec : forall (a : nat) .
                   0 < a -> exists (b : nat) . a = exp 2 (log2 a) + b : nat & b < exp 2 (log2 a)

    log2_unique : forall (a e e' r r' : nat) .
                     0 < a
                     -> a = exp 2 e + r : nat
                     -> a = exp 2 e' + r' : nat
                     -> r < exp 2 e
                     -> r' < exp 2 e'
                     -> e = e' : nat & r = r' : nat

    log2_property : forall (a e r : nat) .
                       0 < a -> a = exp 2 e + r : nat -> r < exp 2 e -> log2 a = e : nat

    log2_lower : forall (a : nat) . 0 < a -> exp 2 (log2 a) <= a

    log2_upper : forall (a : nat) . a < exp 2 (succ (log2 a))

    log2_times_leq : forall (a b : nat) . 0 < a -> 0 < b -> log2 a + log2 b <= log2 (a * b)


### Relation to integers

    div_to_integer : forall (a : nat) (b : pos) .
                        Integer.nat_to_integer (div a b)
                          = Integer.divz (Integer.nat_to_integer a) (Integer.nat_to_integer b)
                          : integer

    mod_to_integer : forall (a : nat) (b : pos) .
                        Integer.nat_to_integer (mod a b)
                          = Integer.modz (Integer.nat_to_integer a) (Integer.nat_to_integer b)
                          : integer
