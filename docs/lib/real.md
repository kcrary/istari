# `Real`

Expressions in this file are rendered using the `real`
[overloading mode](../overloading.html).

Our development of real numbers is based on the one in Bishop and
Bridges [1], with some important differences.  Most notably we accept
Markov's principle, which makes some results stronger (*e.g.,*
`real_dichotomy_neq`); but we are careful about eliminations from
quotient types (Istari requires it), which makes some other results
weaker (*e.g.,* `plusr_positive_invert`).

The type of reals:

    real : U 0

    nonzero_real : U 0
                 = { x : real | x != 0 : real }


### Inequalities

    (* <r *)
    ltr : real -> real -> U 0

    (* <r= *)
    leqr : real -> real -> U 0
         = fn x y . not (y < x)

    ltr_inhabitant : forall (x y : real) . x < y -> () : x < y

    leqr_inhabitant : forall (x y : real) . x <= y -> (fn v0 . ()) : x <= y

    ltr_ext : forall (x y : real) (h h' : x < y) . h = h' : (x < y)

    leqr_ext : forall (x y : real) (h h' : x <= y) . h = h' : (x <= y)

    ltr_impl_leqr : forall (x y : real) . x < y -> x <= y
    
    ltr_irrefl : forall (x : real) . not (x < x)
    
    ltr_impl_neq : forall (x y : real) . x < y -> x != y : real
    
    leqr_refl : forall (x : real) . x <= x
    
    leqr_refl' : forall (x y : real) . x = y : real -> x <= y
    
    leqr_antisymm : forall (x y : real) . x <= y -> y <= x -> x = y : real
    
    leqr_ltr_trans : forall (x y z : real) . x <= y -> y < z -> x < z
    
    ltr_leqr_trans : forall (x y z : real) . x < y -> y <= z -> x < z
    
    ltr_trans : forall (x y z : real) . x < y -> y < z -> x < z
    
    leqr_trans : forall (x y z : real) . x <= y -> y <= z -> x <= z
    
This one gives transitivity in the form needed for rewriting:

    leqr_implication : forall (x x' y y' : real) . x' <= x -> y <= y' -> x <= y -> x' <= y'

    ltr_implication : forall (x x' y y' : real) . x' <= x -> y <= y' -> x < y -> x' < y'

    not_leqr : forall (x y : real) . not (x <= y) <-> y < x
    
    not_ltr : forall (x y : real) . not (x < y) <-> y <= x
    
    ltr_from_leqr_neq : forall (x y : real) . x <= y -> x != y : real -> x < y

These lemmas are convenient for rewriting under `invr`:

    eq_nonzero_real : forall (x y : real) . x != 0 : real -> x = y : real -> x = y : nonzero_real

    eq_nonzero_real' : forall (x y : real) . y != 0 : real -> x = y : real -> x = y : nonzero_real


### Plus and negation

    (* +r *)
    plusr : real -> real -> real
    
    (* ~r *)
    negr : real -> real
    
    (* -r *)
    minusr : real -> real -> real
           = fn x y . x + ~ y


    plusr_commute : forall (x y : real) . x + y = y + x : real
    
    plusr_assoc : forall (x y z : real) . x + y + z = x + (y + z) : real
    
    minusr_assoc : forall (a b c : real) . a - b - c = a - (b + c) : real
    
    plusr_minusr_assoc : forall (a b c : real) . a + b - c = a + (b - c) : real
    
    minusr_plusr_assoc : forall (a b c : real) . a - b + c = a - (b - c) : real
    
    plusr_id_l : forall (x : real) . 0 + x = x : real
    
    plusr_id_r : forall (x : real) . x + 0 = x : real
    
    minusr_id_l : forall (a : real) . 0 - a = ~ a : real
    
    minusr_id_r : forall (a : real) . a - 0 = a : real
    
    plusr_inverse_l : forall (x : real) . ~ x + x = 0 : real
    
    plusr_inverse_r : forall (x : real) . x + ~ x = 0 : real
    
    negr_invol : forall (x : real) . ~ (~ x) = x : real
    
    negr_injective : forall (x y : real) . ~ x = ~ y : real -> x = y : real
    
    negr_plusr : forall (x y : real) . ~ (x + y) = ~ x + ~ y : real
    
    negr_minusr : forall (x y : real) . ~ (x - y) = y - x : real
    
    minusr_self : forall (x : real) . x - x = 0 : real
    
    plusr_commute3 : forall (a b c : real) . a + b + c = a + c + b : real
    
    plusr_rotate : forall (a b c : real) . a + b + c = c + a + b : real
    
    plusr_rotate4 : forall (a b c d : real) . a + b + c + d = a + d + b + c : real

    plusr_cancel_l : forall (a b c : real) . c + a = c + b : real -> a = b : real

    plusr_cancel_r : forall (x y z : real) . x + z = y + z : real -> x = y : real

In each of the `plusr` and `timesr` shift lemmas, the negation/inverse
term is the on the right of the `<->`.  Then the first letter
indicates which direction the negated/inverted term is moving, the
second indicates which operand it is before moving, and the third is
which operand it is after moving.

    plusr_shift_lll : forall (x y z : real) . x = y + z : real <-> ~ y + x = z : real

    plusr_shift_lrr : forall (x y z : real) . x = y + z : real <-> x + ~ z = y : real

    plusr_shift_llr : forall (a b c : real) . a = b + c : real <-> a + ~ b = c : real

    plusr_shift_lrl : forall (a b c : real) . a = b + c : real <-> ~ c + a = b : real

    plusr_shift_rrr : forall (x y z : real) . x + y = z : real <-> x = z + ~ y : real

    plusr_shift_rll : forall (x y z : real) . x + y = z : real <-> y = ~ x + z : real

    plusr_shift_rlr : forall (a b c : real) . a + b = c : real <-> b = c + ~ a : real

    plusr_shift_rrl : forall (a b c : real) . a + b = c : real <-> a = ~ b + c : real

    negr_minusr : forall (x y : real) . ~ (x - y) = y - x : real

    minusr_cancel_r : forall (a b c : real) . a - c = b - c : real -> a = b : real

    minusr_cancel_l : forall (a b c : real) . c - a = c - b : real -> a = b : real

In each of the `minusr` shift lemmas, the subtraction term is on the
right of the `<->`.  Then the first letter indicates which direction
the subtrahend is moving, the second indicates which operand it is
before moving.  It is always the right-hand operand after moving.

    minusr_shift_ll : forall (a b c : real) . a = b + c : real <-> a - b = c : real

    minusr_shift_lr : forall (a b c : real) . a = b + c : real <-> a - c = b : real

    minusr_shift_rr : forall (a b c : real) . a + b = c : real <-> a = c - b : real

    minusr_shift_rl : forall (a b c : real) . a + b = c : real <-> b = c - a : real

    plusr_compat : forall (x x' y y' : real) .
                      x = x' : real -> y = y' : real -> x + y = x' + y' : real

    minusr_compat : forall (x x' y y' : real) .
                       x = x' : real -> y = y' : real -> x - y = x' - y' : real

    negr_compat : forall (x x' : real) . x = x' : real -> ~ x = ~ x' : real

    plusr_ltr : forall (x x' y y' : real) . x < x' -> y < y' -> x + y < x' + y'

    plusr_leqr : forall (x x' y y' : real) . x <= x' -> y <= y' -> x + y <= x' + y'

    plusr_ltr_l : forall (x x' y y' : real) . x < x' -> y <= y' -> x + y < x' + y'

    plusr_ltr_r : forall (x x' y y' : real) . x <= x' -> y < y' -> x + y < x' + y'

    negr_ltr : forall (x y : real) . x < y -> ~ y < ~ x

    negr_ltr' : forall (x y : real) . ~ y < ~ x -> x < y

    negr_leqr : forall (x y : real) . x <= y -> ~ y <= ~ x

    negr_leqr' : forall (x y : real) . ~ y <= ~ x -> x <= y

    plusr_cancel_leqr_l : forall (x y z : real) . z + x <= z + y -> x <= y

    plusr_cancel_leqr_r : forall (x y z : real) . x + z <= y + z -> x <= y

    plusr_cancel_leqr_leqr_l : forall (x x' y y' : real) . x + y <= x' + y' -> x' <= x -> y <= y'

    plusr_cancel_leqr_leqr_r : forall (x x' y y' : real) . x + y <= x' + y' -> y' <= y -> x <= x'

    plusr_shift_leqr_lll : forall (x y z : real) . x <= y + z <-> ~ y + x <= z

    plusr_shift_leqr_lrr : forall (x y z : real) . x <= y + z <-> x + ~ z <= y

    plusr_shift_leqr_llr : forall (x y z : real) . x <= y + z <-> x + ~ y <= z

    plusr_shift_leqr_lrl : forall (x y z : real) . x <= y + z <-> ~ z + x <= y

    plusr_shift_leqr_rrr : forall (x y z : real) . x + y <= z <-> x <= z + ~ y

    plusr_shift_leqr_rll : forall (x y z : real) . x + y <= z <-> y <= ~ x + z

    plusr_shift_leqr_rlr : forall (x y z : real) . x + y <= z <-> y <= z + ~ x

    plusr_shift_leqr_rrl : forall (x y z : real) . x + y <= z <-> x <= ~ y + z

    plusr_cancel_ltr_l : forall (x y z : real) . z + x < z + y -> x < y

    plusr_cancel_ltr_r : forall (x y z : real) . x + z < y + z -> x < y

    plusr_shift_ltr_lll : forall (x y z : real) . x < y + z <-> ~ y + x < z

    plusr_shift_ltr_lrr : forall (x y z : real) . x < y + z <-> x + ~ z < y

    plusr_shift_ltr_llr : forall (x y z : real) . x < y + z <-> x + ~ y < z

    plusr_shift_ltr_lrl : forall (x y z : real) . x < y + z <-> ~ z + x < y

    plusr_shift_ltr_rrr : forall (x y z : real) . x + y < z <-> x < z + ~ y

    plusr_shift_ltr_rll : forall (x y z : real) . x + y < z <-> y < ~ x + z

    plusr_shift_ltr_rlr : forall (x y z : real) . x + y < z <-> y < z + ~ x

    plusr_shift_ltr_rrl : forall (x y z : real) . x + y < z <-> x < ~ y + z

    minusr_leqr : forall (a a' b b' : real) . a <= a' -> b' <= b -> a - b <= a' - b'

    minusr_ltr_l : forall (x x' y y' : real) . x < x' -> y' <= y -> x - y < x' - y'

    minusr_ltr_r : forall (x x' y y' : real) . x <= x' -> y' < y -> x - y < x' - y'

    minusr_cancel_leqr_l : forall (a b c : real) . c - a <= c - b -> b <= a

    minusr_cancel_leqr_r : forall (a b c : real) . a - c <= b - c -> a <= b

    minusr_cancel_ltr_l : forall (a b c : real) . c - a < c - b -> b < a

    minusr_cancel_ltr_r : forall (a b c : real) . a - c < b - c -> a < b

    minusr_shift_leqr_ll : forall (a b c : real) . a <= b + c <-> a - b <= c

    minusr_shift_leqr_lr : forall (a b c : real) . a <= b + c <-> a - c <= b

    minusr_shift_leqr_rr : forall (a b c : real) . a + b <= c <-> a <= c - b

    minusr_shift_leqr_rl : forall (a b c : real) . a + b <= c <-> b <= c - a

    minusr_shift_ltr_ll : forall (a b c : real) . a < b + c <-> a - b < c

    minusr_shift_ltr_lr : forall (a b c : real) . a < b + c <-> a - c < b

    minusr_shift_ltr_rr : forall (a b c : real) . a + b < c <-> a < c - b

    minusr_shift_ltr_rl : forall (a b c : real) . a + b < c <-> b < c - a

    minusr_swap : forall (x y z : real) . x - y - z = x - z - y : real

    plusr_minusr_swap : forall (x y z : real) . x + y - z = x - z + y : real

    plusr_minusr_cancel_r : forall (x y : real) . x + y - y = x : real

    plusr_minusr_cancel_l : forall (x y : real) . x + y - x = y : real

    negr_zero : ~ 0 = 0 : real

    negr_nonzero : forall (x : real) . x != 0 : real -> ~ x != 0 : real


### Times and inverse

    (* *r *)
    timesr : real -> real -> real

    invr : nonzero_real -> real

    (* |r *)
    divr : real -> nonzero_real -> real
         = fn x y . x * invr y


    timesr_commute : forall (x y : real) . x * y = y * x : real

    timesr_assoc : forall (x y z : real) . x * y * z = x * (y * z) : real

    divr_assoc : forall (a : real) (b c : nonzero_real) . a || b || c = a || (b * c) : real

    timesr_divr_assoc : forall (a : real) (b c : nonzero_real) . a * b || c = a * (b || c) : real

    divr_timesr_assoc : forall (a : real) (b c : nonzero_real) . a || b * c = a || (b || c) : real

    timesr_id_l : forall (x : real) . 1 * x = x : real

    timesr_id_r : forall (x : real) . x * 1 = x : real

    divr_id_l : forall (a : nonzero_real) . 1 || a = invr a : real

    divr_id_r : forall (a : real) . a || 1 = a : real

    timesr_inverse_l : forall (x : nonzero_real) . invr x * x = 1 : real

    timesr_inverse_r : forall (x : nonzero_real) . x * invr x = 1 : real

    invr_nonzero : forall (x : nonzero_real) . invr x != 0 : real

    invr_invol : forall (x : nonzero_real) . invr (invr x) = x : real

    invr_timesr : forall (x y : nonzero_real) . invr (x * y) = invr x * invr y : real

    invr_injective : forall (x y : nonzero_real) . invr x = invr y : real -> x = y : real

    real_integral_domain : forall (x y : real) .
                              x * y = 0 : real -> not (not (x = 0 : real % y = 0 : real))

    timesr_neq_zero : forall (x y : real) . x != 0 : real -> y != 0 : real -> x * y != 0 : real

    timesr_neq_zero_invert : forall (x y : real) .
                                x * y != 0 : real -> x != 0 : real & y != 0 : real

    timesr_ltr_zero_invert : forall (x y : real) . 0 < x * y -> x < 0 & y < 0 % 0 < x & 0 < y

    timesr_ltr_zero_invert_neg : forall (x y : real) . x * y < 0 -> x < 0 & 0 < y % 0 < x & y < 0

    square_nonnegative : forall (x : real) . 0 <= x * x

    invr_positive : forall (x : real) . 0 < x -> 0 < invr x

    invr_negative : forall (x : real) . x < 0 -> invr x < 0

    divr_self : forall (a : real) . a != 0 : real -> a || a = 1 : real

    timesr_commute3 : forall (a b c : real) . a * b * c = a * c * b : real

    timesr_rotate : forall (a b c : real) . a * b * c = c * a * b : real

    timesr_rotate4 : forall (a b c d : real) . a * b * c * d = a * d * b * c : real

    timesr_cancel_l : forall (x y z : real) .
                         z != 0 : real -> z * x = z * y : real -> x = y : real

    timesr_cancel_r : forall (x y z : real) .
                         z != 0 : real -> x * z = y * z : real -> x = y : real

    timesr_shift_lll : forall (x y z : real) .
                          y != 0 : real -> x = y * z : real <-> invr y * x = z : real

    timesr_shift_lrr : forall (x y z : real) .
                          z != 0 : real -> x = y * z : real <-> x * invr z = y : real

    timesr_shift_llr : forall (x y z : real) .
                          y != 0 : real -> x = y * z : real <-> x * invr y = z : real

    timesr_shift_lrl : forall (x y z : real) .
                          z != 0 : real -> x = y * z : real <-> invr z * x = y : real

    timesr_shift_rrr : forall (x y z : real) .
                          y != 0 : real -> x * y = z : real <-> x = z * invr y : real

    timesr_shift_rll : forall (x y z : real) .
                          x != 0 : real -> x * y = z : real <-> y = invr x * z : real

    timesr_shift_rlr : forall (x y z : real) .
                          x != 0 : real -> x * y = z : real <-> y = z * invr x : real

    timesr_shift_rrl : forall (x y z : real) .
                          y != 0 : real -> x * y = z : real <-> x = invr y * z : real

    divr_cancel_l : forall (a b : nonzero_real) (c : real) .
                       c != 0 : real -> c || a = c || b : real -> a = b : real

    divr_cancel_r : forall (a b c : real) .
                       c != 0 : real -> a || c = b || c : real -> a = b : real

    divr_shift_ll : forall (a b c : real) .
                       b != 0 : real -> a = b * c : real <-> a || b = c : real

    divr_shift_lr : forall (a b c : real) .
                       c != 0 : real -> a = b * c : real <-> a || c = b : real

    divr_shift_rr : forall (a b c : real) .
                       b != 0 : real -> a * b = c : real <-> a = c || b : real

    divr_shift_rl : forall (a b c : real) .
                       a != 0 : real -> a * b = c : real <-> b = c || a : real

    timesr_compat : forall (x x' y y' : real) .
                       x = x' : real -> y = y' : real -> x * y = x' * y' : real

    invr_compat : forall (x x' : nonzero_real) . x = x' : real -> invr x = invr x' : real

    timesr_leqr : forall (x x' y y' : real) .
                     0 <= x -> 0 <= y -> x <= x' -> y <= y' -> x * y <= x' * y'

    (* an alias for timesr_leqr *)
    timesr_leqr_pos_pos : forall (x x' y y' : real) .
                             0 <= x -> 0 <= y -> x <= x' -> y <= y' -> x * y <= x' * y'

    timesr_leqr_neg_neg : forall (x x' y y' : real) .
                             x' <= 0 -> y' <= 0 -> x <= x' -> y <= y' -> x' * y' <= x * y

    timesr_leqr_pos_neg : forall (x x' y y' : real) .
                             0 <= x -> y' <= 0 -> x <= x' -> y <= y' -> x' * y <= x * y'

    timesr_leqr_neg_neg : forall (x x' y y' : real) .
                             x' <= 0 -> y' <= 0 -> x <= x' -> y <= y' -> x' * y' <= x * y

    timesr_leqr_zero : forall (x y : real) . 0 <= x -> 0 <= y -> 0 <= x * y

    (* an alias for timesq_leqq_zero *)
    timesr_leqr_zero_pos_pos : forall (x y : real) . 0 <= x -> 0 <= y -> 0 <= x * y

    timesr_leqr_zero_pos_neg : forall (x y : real) . 0 <= x -> y <= 0 -> x * y <= 0

    timesr_leqr_zero_neg_pos : forall (x y : real) . x <= 0 -> 0 <= y -> x * y <= 0

    timesr_leqr_zero_neg_neg : forall (x y : real) . x <= 0 -> y <= 0 -> 0 <= x * y

    timesr_leqr_l : forall (x y y' : real) . 0 <= x -> y <= y' -> x * y <= x * y'

    timesr_leqr_r : forall (x x' y : real) . x <= x' -> 0 <= y -> x * y <= x' * y

    timesr_leqr_l_neg : forall (x y y' : real) . x <= 0 -> y <= y' -> x * y' <= x * y

    timesr_leqr_r_neg : forall (x x' y : real) . x <= x' -> y <= 0 -> x' * y <= x * y

    timesr_ltr_leqr : forall (x y x' y' : real) .
                         0 <= x -> 0 < y -> x < x' -> y <= y' -> x * y < x' * y'

    timesr_leqr_ltr : forall (x y x' y' : real) .
                         0 < x -> 0 <= y -> x <= x' -> y < y' -> x * y < x' * y'

    timesr_ltr : forall (x y x' y' : real) .
                    0 <= x -> 0 <= y -> x < x' -> y < y' -> x * y < x' * y'

    timesr_ltr_l : forall (x y y' : real) . 0 < x -> y < y' -> x * y < x * y'

    timesr_ltr_r : forall (x x' y : real) . 0 < y -> x < x' -> x * y < x' * y

    timesr_ltr_l_neg : forall (x y y' : real) . x < 0 -> y < y' -> x * y' < x * y

    timesr_ltr_r_neg : forall (x x' y : real) . x < x' -> y < 0 -> x' * y < x * y

    timesr_ltr_zero : forall (x y : real) . 0 < x -> 0 < y -> 0 < x * y

    (* an alias for timesr_ltr_zero *)
    timesr_ltr_zero_pos_pos : forall (x y : real) . 0 < x -> 0 < y -> 0 < x * y

    timesr_ltr_zero_pos_neg : forall (x y : real) . 0 < x -> y < 0 -> x * y < 0

    timesr_ltr_zero_neg_pos : forall (x y : real) . x < 0 -> 0 < y -> x * y < 0

    timesr_ltr_zero_neg_neg : forall (x y : real) . x < 0 -> y < 0 -> 0 < x * y

    timesr_cancel_leqr_l : forall (x y z : real) . 0 < z -> z * x <= z * y -> x <= y

    timesr_cancel_leqr_r : forall (x y z : real) . 0 < z -> x * z <= y * z -> x <= y

    timesr_cancel_ltr_l : forall (x y z : real) . 0 < z -> z * x < z * y -> x < y

    timesr_cancel_ltr_r : forall (x y z : real) . 0 < z -> x * z < y * z -> x < y

    timesr_cancel_leqr_l_neg : forall (x y z : real) . z < 0 -> z * x <= z * y -> y <= x

    timesr_cancel_leqr_r_neg : forall (x y z : real) . z < 0 -> x * z <= y * z -> y <= x

    timesr_cancel_ltr_l_neg : forall (x y z : real) . z < 0 -> z * x < z * y -> y < x

    timesr_cancel_ltr_r_neg : forall (x y z : real) . z < 0 -> x * z < y * z -> y < x

    timesr_shift_leqr_lll : forall (x y z : real) . 0 < y -> x <= y * z <-> invr y * x <= z

    timesr_shift_leqr_lrr : forall (x y z : real) . 0 < z -> x <= y * z <-> x * invr z <= y

    timesr_shift_leqr_llr : forall (x y z : real) . 0 < y -> x <= y * z <-> x * invr y <= z

    timesr_shift_leqr_lrl : forall (x y z : real) . 0 < z -> x <= y * z <-> invr z * x <= y

    timesr_shift_leqr_rrr : forall (x y z : real) . 0 < y -> x * y <= z <-> x <= z * invr y

    timesr_shift_leqr_rll : forall (x y z : real) . 0 < x -> x * y <= z <-> y <= invr x * z

    timesr_shift_leqr_rlr : forall (x y z : real) . 0 < x -> x * y <= z <-> y <= z * invr x

    timesr_shift_leqr_rrl : forall (x y z : real) . 0 < y -> x * y <= z <-> x <= invr y * z

    timesr_shift_ltr_lll : forall (x y z : real) . 0 < y -> x < y * z <-> invr y * x < z

    timesr_shift_ltr_lrr : forall (x y z : real) . 0 < z -> x < y * z <-> x * invr z < y

    timesr_shift_ltr_llr : forall (x y z : real) . 0 < y -> x < y * z <-> x * invr y < z

    timesr_shift_ltr_lrl : forall (x y z : real) . 0 < z -> x < y * z <-> invr z * x < y

    timesr_shift_ltr_rrr : forall (x y z : real) . 0 < y -> x * y < z <-> x < z * invr y

    timesr_shift_ltr_rll : forall (x y z : real) . 0 < x -> x * y < z <-> y < invr x * z

    timesr_shift_ltr_rlr : forall (x y z : real) . 0 < x -> x * y < z <-> y < z * invr x

    timesr_shift_ltr_rrl : forall (x y z : real) . 0 < y -> x * y < z <-> x < invr y * z

In the negative multiplicative shifts, the naming is as though the
inequality did not reverse on the right.

    timesr_shift_leqr_lll_neg : forall (x y z : real) . y < 0 -> x <= y * z <-> z <= invr y * x

    timesr_shift_leqr_lrr_neg : forall (x y z : real) . z < 0 -> x <= y * z <-> y <= x * invr z

    timesr_shift_leqr_llr_neg : forall (x y z : real) . y < 0 -> x <= y * z <-> z <= x * invr y

    timesr_shift_leqr_lrl_neg : forall (x y z : real) . z < 0 -> x <= y * z <-> y <= invr z * x

    timesr_shift_leqr_rrr_neg : forall (x y z : real) . y < 0 -> x * y <= z <-> z * invr y <= x

    timesr_shift_leqr_rll_neg : forall (x y z : real) . x < 0 -> x * y <= z <-> invr x * z <= y

    timesr_shift_leqr_rlr_neg : forall (x y z : real) . x < 0 -> x * y <= z <-> z * invr x <= y

    timesr_shift_leqr_rrl_neg : forall (x y z : real) . y < 0 -> x * y <= z <-> invr y * z <= x

    timesr_shift_ltr_lll_neg : forall (x y z : real) . y < 0 -> x < y * z <-> z < invr y * x

    timesr_shift_ltr_lrr_neg : forall (x y z : real) . z < 0 -> x < y * z <-> y < x * invr z

    timesr_shift_ltr_llr_neg : forall (x y z : real) . y < 0 -> x < y * z <-> z < x * invr y

    timesr_shift_ltr_lrl_neg : forall (x y z : real) . z < 0 -> x < y * z <-> y < invr z * x

    timesr_shift_ltr_rrr_neg : forall (x y z : real) . y < 0 -> x * y < z <-> z * invr y < x

    timesr_shift_ltr_rll_neg : forall (x y z : real) . x < 0 -> x * y < z <-> invr x * z < y

    timesr_shift_ltr_rlr_neg : forall (x y z : real) . x < 0 -> x * y < z <-> z * invr x < y

    timesr_shift_ltr_rrl_neg : forall (x y z : real) . y < 0 -> x * y < z <-> invr y * z < x

    divr_shift_leqr_ll : forall (a b c : real) . 0 < b -> a <= b * c <-> a || b <= c

    divr_shift_leqr_lr : forall (a b c : real) . 0 < c -> a <= b * c <-> a || c <= b

    divr_shift_leqr_rr : forall (a b c : real) . 0 < b -> a * b <= c <-> a <= c || b

    divr_shift_leqr_rl : forall (a b c : real) . 0 < a -> a * b <= c <-> b <= c || a

    divr_shift_ltr_ll : forall (a b c : real) . 0 < b -> a < b * c <-> a || b < c

    divr_shift_ltr_lr : forall (a b c : real) . 0 < c -> a < b * c <-> a || c < b

    divr_shift_ltr_rr : forall (a b c : real) . 0 < b -> a * b < c <-> a < c || b

    divr_shift_ltr_rl : forall (a b c : real) . 0 < a -> a * b < c <-> b < c || a

    divr_shift_leqr_ll_neg : forall (a b c : real) . b < 0 -> a <= b * c <-> c <= a || b

    divr_shift_leqr_lr_neg : forall (a b c : real) . c < 0 -> a <= b * c <-> b <= a || c

    divr_shift_leqr_rr_neg : forall (a b c : real) . b < 0 -> a * b <= c <-> c || b <= a

    divr_shift_leqr_rl_neg : forall (a b c : real) . a < 0 -> a * b <= c <-> c || a <= b

    divr_shift_ltr_ll_neg : forall (a b c : real) . b < 0 -> a < b * c <-> c < a || b

    divr_shift_ltr_lr_neg : forall (a b c : real) . c < 0 -> a < b * c <-> b < a || c

    divr_shift_ltr_rr_neg : forall (a b c : real) . b < 0 -> a * b < c <-> c || b < a

    divr_shift_ltr_rl_neg : forall (a b c : real) . a < 0 -> a * b < c <-> c || a < b

    divr_leqr_zero : forall (x y : real) . 0 <= x -> 0 < y -> 0 <= x || y

    (* an alias for divr_leq_zero *)
    divr_leqr_zero_pos_pos : forall (x y : real) . 0 <= x -> 0 < y -> 0 <= x || y
    
    divr_leqr_zero_pos_neg : forall (x y : real) . 0 <= x -> y < 0 -> x || y <= 0

    divr_leqr_zero_neg_pos : forall (x y : real) . x <= 0 -> 0 < y -> x || y <= 0

    divr_leqr_zero_neg_neg : forall (x y : real) . x <= 0 -> y < 0 -> 0 <= x || y

    divr_ltr_zero : forall (x y : real) . 0 < x -> 0 < y -> 0 < x || y

    (* an alias for divr_leq_zero *)
    divr_ltr_zero_pos_pos : forall (x y : real) . 0 < x -> 0 < y -> 0 < x || y

    divr_ltr_zero_pos_neg : forall (x y : real) . 0 < x -> y < 0 -> x || y < 0

    divr_ltr_zero_neg_pos : forall (x y : real) . x < 0 -> 0 < y -> x || y < 0

    divr_ltr_zero_neg_neg : forall (x y : real) . x < 0 -> y < 0 -> 0 < x || y

    invr_leqr_pos : forall (x y : real) . 0 < x -> x <= y -> invr y <= invr x

    invr_leqr_neg : forall (x y : real) . y < 0 -> x <= y -> invr y <= invr x

    invr_ltr_pos : forall (x y : real) . 0 < x -> x < y -> invr y < invr x

    invr_ltr_neg : forall (x y : real) . y < 0 -> x < y -> invr y < invr x

    datatype
      intersect (i : level) . U i
    of
      samesign : real -> real -> type =
  
      | samesign_pos :
          forall x y .
            0 < x
            -> 0 < y
            -> samesign x y
  
      | samesign_neg :
          forall x y .
            x < 0
            -> y < 0
            -> samesign x y

    invr_leqr_samesign : forall (x y : real) . samesign x y -> x <= y -> invr y <= invr x

    invr_ltr_samesign : forall (x y : real) . samesign x y -> x < y -> invr y < invr x

    invr_one : invr 1 = 1 : real


### Distributivity

    timesr_dist_plusr_r : forall (x y z : real) . x * (y + z) = x * y + x * z : real

    timesr_dist_plusr_l : forall (x y z : real) . (x + y) * z = x * z + y * z : real

    timesr_ann_l : forall (x : real) . 0 * x = 0 : real

    timesr_ann_r : forall (x : real) . x * 0 = 0 : real

    plusr_self : forall (x : real) . x + x = 2 * x : real

    negr_as_timesr : forall (x : real) . ~ x = -1 * x : real

    negr_dist_timesr_l : forall (x y : real) . ~ (x * y) = ~ x * y : real

    negr_dist_timesr_r : forall (x y : real) . ~ (x * y) = x * ~ y : real

    timesr_dist_minusr_r : forall (a b c : real) . a * (b - c) = a * b - a * c : real

    timesr_dist_minusr_l : forall (a b c : real) . (a - b) * c = a * c - b * c : real

    negr_dist_invr : forall (x : nonzero_real) . ~ (invr x) = invr (~ x) : real

    negr_dist_divr_l : forall (x : real) (y : nonzero_real) . ~ (x || y) = ~ x || y : real

    negr_dist_divr_r : forall (x : real) (y : nonzero_real) . ~ (x || y) = x || ~ y : real


### Relation to rationals

    rational_to_real : Rational.rational -> real


    rational_to_real_injective : forall (x y : Rational.rational) .
                                    rational_to_real x = rational_to_real y : real
                                    -> x = y : Rational.rational

    rational_to_real_neq : forall (x y : Rational.rational) .
                              x != y : Rational.rational
                              -> rational_to_real x != rational_to_real y : real

    rational_to_real_nonzero : forall (x : Rational.rational) .
                                  x != q`0 : Rational.rational -> rational_to_real x != 0 : real

    rational_to_real_mono : forall (x y : Rational.rational) .
                               x <q= y -> rational_to_real x <= rational_to_real y

    rational_to_real_mono_conv : forall (x y : Rational.rational) .
                                    rational_to_real x <= rational_to_real y -> x <q= y

    rational_to_real_mono_lt : forall (x y : Rational.rational) .
                                  x <q y -> rational_to_real x < rational_to_real y

    rational_to_real_mono_lt_conv : forall (x y : Rational.rational) .
                                       rational_to_real x < rational_to_real y -> x <q y

    plusq_to_real : forall (x y : Rational.rational) .
                       rational_to_real (x +q y) = rational_to_real x + rational_to_real y : real

    negq_to_real : forall (x : Rational.rational) .
                      rational_to_real (~q x) = ~ (rational_to_real x) : real

    minusq_to_real : forall (x y : Rational.rational) .
                        rational_to_real (x -q y) = rational_to_real x - rational_to_real y : real

    timesq_to_real : forall (x y : Rational.rational) .
                        rational_to_real (x *q y) = rational_to_real x * rational_to_real y : real

    invq_to_real : forall (x : Rational.rational) .
                      x != q`0 : Rational.rational
                      -> rational_to_real (Rational.invq x) = invr (rational_to_real x) : real

    divq_to_real : forall (x y : Rational.rational) .
                      y != q`0 : Rational.rational
                      -> rational_to_real (x |q y)
                           = rational_to_real x || rational_to_real y
                           : real


### Relation to integers

    integer_to_real : integer -> real
                    = fn x . rational_to_real (Rational.integer_to_rational x)

    integer_to_real_injective : forall (x y : integer) .
                                   integer_to_real x = integer_to_real y : real -> x = y : integer

    integer_to_real_neq : forall (x y : integer) .
                             x != y : integer -> integer_to_real x != integer_to_real y : real

    integer_to_real_nonzero : forall (x : integer) .
                                 x != z`0 : integer -> integer_to_real x != 0 : real

    integer_to_real_mono : forall (x y : integer) .
                              x <z= y -> integer_to_real x <= integer_to_real y

    integer_to_real_mono_conv : forall (x y : integer) .
                                   integer_to_real x <= integer_to_real y -> x <z= y

    integer_to_real_mono_lt : forall (x y : integer) .
                                 x <z y -> integer_to_real x < integer_to_real y

    integer_to_real_mono_lt_conv : forall (x y : integer) .
                                      integer_to_real x < integer_to_real y -> x <z y

    plusz_to_real : forall (x y : integer) .
                       integer_to_real (x +z y) = integer_to_real x + integer_to_real y : real

    negz_to_real : forall (x : integer) . integer_to_real (~z x) = ~ (integer_to_real x) : real

    minusz_to_real : forall (x y : integer) .
                        integer_to_real (x -z y) = integer_to_real x - integer_to_real y : real

    timesz_to_real : forall (x y : integer) .
                        integer_to_real (x *z y) = integer_to_real x * integer_to_real y : real


### Relation to natural numbers

    nat_to_real : nat -> real
                = fn n .
                     rational_to_real (Rational.integer_to_rational (Integer.nat_to_integer n))

    nat_to_real_injective : forall (x y : nat) .
                               nat_to_real x = nat_to_real y : real -> x = y : nat

    nat_to_real_neq : forall (x y : nat) . x != y : nat -> nat_to_real x != nat_to_real y : real

    nat_to_real_nonzero : forall (n : nat) . n != n`0 : nat -> nat_to_real n != 0 : real

    nat_to_real_mono : forall (x y : nat) . x <n= y -> nat_to_real x <= nat_to_real y

    nat_to_real_mono_conv : forall (x y : nat) . nat_to_real x <= nat_to_real y -> x <n= y

    nat_to_real_mono_lt : forall (x y : nat) . x <n y -> nat_to_real x < nat_to_real y

    nat_to_real_mono_lt_conv : forall (x y : nat) . nat_to_real x < nat_to_real y -> x <n y

    plus_to_real : forall (x y : nat) .
                      nat_to_real (x +n y) = nat_to_real x + nat_to_real y : real

    times_to_real : forall (x y : nat) .
                       nat_to_real (x *n y) = nat_to_real x * nat_to_real y : real


### Significant numbers

    ltr_0_1 : 0 < 1

    leqr_0_1 : 0 <= 1

    neqr_0_1 : 0 != 1 : real

    ltr_neg1_0 : -1 < 0

    leqr_neg1_0 : -1 <= 0

    neqr_neg1_0 : -1 != 0 : real

    negr_one : ~ 1 = -1 : real

    negr_minus_one : ~ -1 = 1 : real


### Stability and limited decidability

    eq_real_stable : forall (x y : real) . Stable.stable (x = y : real)

    ltr_stable : forall (x y : real) . Stable.stable (x < y)

    leqr_stable : forall (x y : real) . Stable.stable (x <= y)

    ltr_sqstable : forall (x y : real) . Sqstable.sqstable (x < y)

    leqr_sqstable : forall (x y : real) . Sqstable.sqstable (x <= y)

    real_dichotomy_neq : forall (x y : real) . x != y : real -> x < y % y < x

    real_trichotomy_if_stable : forall (i : level) (P : U i) (x y : real) .
                                   Stable.stable P -> (x < y % x = y : real % y < x -> P) -> P

    real_dichotomy_if_stable : forall (i : level) (P : U i) (x y : real) .
                                  Stable.stable P -> (x <= y % y < x -> P) -> P

    real_dichotomy_weak_if_stable : forall (i : level) (P : U i) (x y : real) .
                                       Stable.stable P -> (x <= y % y <= x -> P) -> P

These lemmas (and others) require a [`squish`](squish.html) in their
result, since the disjunct returned can depend on the representations
of their inputs:

    plusr_positive_invert : forall (x y : real) . 0 < x + y -> Squish.squish (0 < x % 0 < y)

    plusr_positive_invert_squash : forall (x y : real) . 0 < x + y -> { 0 < x % 0 < y }

    overlapping_ranges : forall (x y z : real) . y < z -> Squish.squish (x < z % y < x)

    overlapping_ranges_squash : forall (x y z : real) . y < z -> { x < z % y < x }


### Absolute value

    absr : real -> real


    absr_nonneg : forall (x : real) . 0 <= absr x

    absr_of_nonneg : forall (x : real) . 0 <= x -> absr x = x : real

    absr_of_nonpos : forall (x : real) . x <= 0 -> absr x = ~ x : real

    absr_negr : forall (x : real) . absr (~ x) = absr x : real

    absr_timesr : forall (x y : real) . absr (x * y) = absr x * absr y : real

    absr_plusr_leqr : forall (x y : real) . absr (x + y) <= absr x + absr y

    absr_minusr_leqr : forall (x y : real) . absr (x - y) <= absr x + absr y

    absr_preserves_nonzero : forall (x : real) . x != 0 : real -> absr x != 0 : real

    absr_ub : forall (x : real) . x <= absr x

    absr_idem : forall (x : real) . absr (absr x) = absr x : real

    absr_invr : forall (x : nonzero_real) . absr (invr x) = invr (absr x) : real

    absr_zero : absr 0 = 0 : real

    absr_one : absr 1 = 1 : real

    absr_minus_one : absr -1 = 1 : real

    absr_positive_iff_nonzero : forall (x : real) . 0 < absr x <-> x != 0 : real

    absr_minusr_commute : forall (a b : real) . absr (a - b) = absr (b - a) : real

    absr_minusr_upper_bound : forall (a b c : real) . absr (a - b) <= c -> a <= b + c

    absr_minusr_lower_bound : forall (a b c : real) . absr (a - b) <= c -> b - c <= a

    absr_minusr_absr : forall (a b : real) . absr (absr a - absr b) <= absr (a - b)

    absr_minusr_leqr_lower : forall (x y : real) . absr x - absr y <= absr (x - y)

    absq_to_real : forall (x : Rational.rational) .
                      rational_to_real (Rational.absq x) = absr (rational_to_real x) : real

    absz_to_real : forall (x : integer) .
                      integer_to_real (Integer.absz x) = absr (integer_to_real x) : real


### Maximum and minimum

    maxr : real -> real -> real

    minr : real -> real -> real
         = fn x y . ~ (maxr (~ x) (~ y))


    maxr_commute : forall (x y : real) . maxr x y = maxr y x : real

    minr_commute : forall (x y : real) . minr x y = minr y x : real

    maxr_assoc : forall (a b c : real) . maxr (maxr a b) c = maxr a (maxr b c) : real

    minr_assoc : forall (a b c : real) . minr (minr a b) c = minr a (minr b c) : real

    maxr_leq_l : forall (x y : real) . x <= maxr x y

    maxr_leq_r : forall (x y : real) . y <= maxr x y

    minr_leq_l : forall (x y : real) . minr x y <= x

    minr_leq_r : forall (x y : real) . minr x y <= y

    maxr_lub : forall (x y z : real) . x <= z -> y <= z -> maxr x y <= z

    minr_glb : forall (x y z : real) . z <= x -> z <= y -> z <= minr x y

    maxr_lub_strict : forall (a b c : real) . a < c -> b < c -> maxr a b < c

    minr_glb_strict : forall (a b c : real) . c < a -> c < b -> c < minr a b

    maxr_eq_l : forall (x y : real) . y <= x -> maxr x y = x : real

    maxr_eq_r : forall (x y : real) . x <= y -> maxr x y = y : real

    minr_eq_l : forall (x y : real) . x <= y -> minr x y = x : real

    minr_eq_r : forall (x y : real) . y <= x -> minr x y = y : real

    negr_maxr : forall (a b : real) . ~ (maxr a b) = minr (~ a) (~ b) : real

    minr_as_maxr : forall (a b : real) . minr a b = ~ (maxr (~ a) (~ b)) : real

    negr_minr : forall (a b : real) . ~ (minr a b) = maxr (~ a) (~ b) : real

    minr_as_maxr : forall (a b : real) . minr a b = ~ (maxr (~ a) (~ b)) : real

    maxr_idem : forall (a : real) . maxr a a = a : real

    minr_idem : forall (a : real) . minr a a = a : real

    minr_dist_maxr_l : forall (a b c : real) .
                          minr (maxr a b) c = maxr (minr a c) (minr b c) : real

    minr_dist_maxr_r : forall (a b c : real) .
                          minr a (maxr b c) = maxr (minr a b) (minr a c) : real

    maxr_dist_minr_l : forall (a b c : real) .
                          maxr (minr a b) c = minr (maxr a c) (maxr b c) : real

    maxr_dist_minr_r : forall (a b c : real) .
                          maxr a (minr b c) = minr (maxr a b) (maxr a c) : real

    plusr_dist_minr_l : forall (a b c : real) . minr a b + c = minr (a + c) (b + c) : real

    plusr_dist_minr_r : forall (a b c : real) . a + minr b c = minr (a + b) (a + c) : real

    plusr_dist_maxr_l : forall (a b c : real) . maxr a b + c = maxr (a + c) (b + c) : real

    plusr_dist_maxr_r : forall (a b c : real) . a + maxr b c = maxr (a + b) (a + c) : real

    absr_minusr_maxr : forall (a b c d : real) .
                          absr (maxr a b - maxr c d) <= maxr (absr (a - c)) (absr (b - d))

    maxq_to_real : forall (a b : Rational.rational) .
                      rational_to_real (Rational.maxq a b)
                        = maxr (rational_to_real a) (rational_to_real b)
                        : real

    minq_to_real : forall (a b : Rational.rational) .
                      rational_to_real (Rational.minq a b)
                        = minr (rational_to_real a) (rational_to_real b)
                        : real

    maxz_to_real : forall (a b : integer) .
                      integer_to_real (Integer.maxz a b)
                        = maxr (integer_to_real a) (integer_to_real b)
                        : real

    minz_to_real : forall (a b : integer) .
                      integer_to_real (Integer.minz a b)
                        = minr (integer_to_real a) (integer_to_real b)
                        : real


### Miscellaneous

    rational_dense_within_real : forall (x y : real) .
                                    x < y
                                    -> Squish.squish
                                         (exists (z : Rational.rational) .
                                            x < rational_to_real z & rational_to_real z < y)

    rational_dense_within_real_squash : forall (x y : real) .
                                           x < y
                                           -> { exists (z : Rational.rational) .
                                                  x < rational_to_real z & rational_to_real z < y }

    real_upper_bound : forall (x : real) .
                          Squish.squish (exists (y : integer) . x < integer_to_real y)

    real_upper_bound_squash : forall (x : real) . { exists (y : integer) . x < integer_to_real y }

    real_upper_bound_nat : forall (x : real) .
                              Squish.squish (exists (n : nat) . n`0 <n n & x < nat_to_real n)

    real_upper_bound_nat_squash : forall (x : real) .
                                     { exists (n : nat) . n`0 <n n & x < nat_to_real n }

    infinitely_close : forall (x y : real) .
                          (forall (k : nat) . n`0 <n k -> absr (x - y) <= invr (nat_to_real k))
                          -> x = y : real

    leqr_from_upper_bounds : forall (x y : real) . (forall (z : real) . y < z -> x <= z) -> x <= y

    leqr_from_lower_bounds : forall (x y : real) . (forall (z : real) . z < y -> z <= x) -> y <= x

    real_total : Partial.total real

    real_strict : Partial.strict real

    real_symmetrical : Quotient.symmetrical real

    ltr_symmetrical : forall (x y : real) . Quotient.symmetrical (x < y)

    leqr_symmetrical : forall (x y : real) . Quotient.symmetrical (x <= y)


### Prereals

A few lemmas require the inputs' unquotiented representation to
produce a deterministic result.

    prereal : U 0

    realintro : prereal -> real

    real_to_prereal : forall (x : real) .
                         Squish.squish (exists (y : prereal) . x = realintro y : real)

    real_to_prereal_squash : forall (x : real) . { exists (y : prereal) . x = realintro y : real }

    real_sequence_to_prereal_sequence : forall (f : nat -> real) .
                                           Squish.squish
                                             (exists (g : nat -> prereal) .
                                                f = (fn x . realintro (g x)) : (nat -> real))

    real_sequence_to_prereal_sequence_squash : forall (f : nat -> real) .
                                                  { exists (g : nat -> prereal) .
                                                      f = (fn x . realintro (g x)) : (nat -> real) }

    rational_to_prereal : Rational.rational -> prereal

    integer_to_prereal : integer -> prereal
                       = fn x . rational_to_prereal (Rational.integer_to_rational x)

    preplusr : prereal -> prereal -> prereal

    prenegr : prereal -> prereal

    pretimesr : prereal -> prereal -> prereal

    preinvr : { x : prereal | realintro x != 0 : real } -> prereal

    rational_to_prereal_to_real : forall (x : Rational.rational) .
                                     realintro (rational_to_prereal x) = rational_to_real x : real

    integer_to_prereal_to_real : forall (x : integer) .
                                    realintro (integer_to_prereal x) = integer_to_real x : real

    preplusr_to_real : forall (x y : prereal) .
                          realintro (preplusr x y) = realintro x + realintro y : real

    prenegr_to_real : forall (x : prereal) . realintro (prenegr x) = ~ (realintro x) : real

    pretimesr_to_real : forall (x y : prereal) .
                           realintro (pretimesr x y) = realintro x * realintro y : real

    preinvr_to_real : forall (x : { x : prereal | realintro x != 0 : real }) .
                         realintro (preinvr x) = invr (realintro x) : real

    plusq_to_prereal : forall (x y : Rational.rational) .
                          rational_to_prereal (x +q y)
                            = preplusr (rational_to_prereal x) (rational_to_prereal y)
                            : prereal

    negq_to_prereal : forall (x : Rational.rational) .
                         rational_to_prereal (~q x) = prenegr (rational_to_prereal x) : prereal

    timesq_to_prereal : forall (x y : Rational.rational) .
                           rational_to_prereal (x *q y)
                             = pretimesr (rational_to_prereal x) (rational_to_prereal y)
                             : prereal

    invq_to_prereal : forall (x : Rational.rational) .
                         rational_to_prereal (Rational.invq x)
                           = preinvr (rational_to_prereal x)
                           : prereal

    plusz_to_prereal : forall (x y : integer) .
                          integer_to_prereal (x +z y)
                            = preplusr (integer_to_prereal x) (integer_to_prereal y)
                            : prereal

    negz_to_prereal : forall (x : integer) .
                         integer_to_prereal (~z x) = prenegr (integer_to_prereal x) : prereal

    timesz_to_prereal : forall (x y : integer) .
                           integer_to_prereal (x *z y)
                             = pretimesr (integer_to_prereal x) (integer_to_prereal y)
                             : prereal

    plusr_positive_invert_prereal : forall (x y : prereal) .
                                       0 < realintro x + realintro y
                                       -> 0 < realintro x % 0 < realintro y

    overlapping_ranges_prereal : forall (x y z : prereal) .
                                    realintro y < realintro z
                                    -> realintro x < realintro z % realintro y < realintro x

    rational_dense_within_real_prereal : forall (x y : prereal) .
                                            realintro x < realintro y
                                            -> exists (z : Rational.rational) .
                                                 realintro x < rational_to_real z
                                                 & rational_to_real z < realintro y

    real_upper_bound_prereal : forall (x : prereal) .
                                  exists (y : integer) . realintro x < integer_to_real y

    real_upper_bound_nat_prereal : forall (x : prereal) .
                                      exists (n : nat) . n`0 <n n & realintro x < nat_to_real n

---

[1] Errett Bishop and Douglas Bridges.  *Constructive Analysis.*
Springer, 1985.
