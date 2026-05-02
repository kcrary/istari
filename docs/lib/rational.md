# `Rational`

Expressions in this file are rendered using the `rational`
[overloading mode](../overloading.html).

The type of rationals:

    rational : U 0


### Plus and negation

    (* +q *)
    plusq : rational -> rational -> rational

    (* ~q *)
    negq : rational -> rational

    (* -q *)
    minusq : rational -> rational -> rational
           = fn x y . x + ~ y

    plusq_commute : forall (x y : rational) . x + y = y + x : rational

    minusq_assoc : forall (a b c : rational) . a - b - c = a - (b + c) : rational

    plusq_minusq_assoc : forall (a b c : rational) . a + b - c = a + (b - c) : rational

    minusq_plusq_assoc : forall (a b c : rational) . a - b + c = a - (b - c) : rational

    plusq_assoc : forall (x y z : rational) . x + y + z = x + (y + z) : rational

    plusq_id_l : forall (x : rational) . 0 + x = x : rational

    plusq_id_r : forall (x : rational) . x + 0 = x : rational

    minusq_id_l : forall (a : rational) . 0 - a = ~ a : rational

    minusq_id_r : forall (a : rational) . a - 0 = a : rational

    negq_invol : forall (x : rational) . ~ (~ x) = x : rational

    plusq_inverse_l : forall (x : rational) . ~ x + x = 0 : rational

    plusq_inverse_r : forall (x : rational) . x + ~ x = 0 : rational

    minusq_self : forall (x : rational) . x - x = 0 : rational

    negq_zero : ~ 0 = 0 : rational

    negq_nonzero : forall (x : rational) . x != 0 : rational -> ~ x != 0 : rational

    negq_injective : forall (x y : rational) . ~ x = ~ y : rational -> x = y : rational

    negq_plusq : forall (x y : rational) . ~ (x + y) = ~ x + ~ y : rational

    plusq_cancel_l : forall (x y z : rational) . z + x = z + y : rational -> x = y : rational

    plusq_cancel_r : forall (x y z : rational) . x + z = y + z : rational -> x = y : rational

In each of the `plusq` and `timesq` shift lemmas, the negation/inverse
term is the on the right of the `<->`.  Then the first letter
indicates which direction the negated/inverted term is moving, the
second indicates which operand it is before moving, and the third is
which operand it is after moving.

    plusq_shift_lll : forall (x y z : rational) . x = y + z : rational <-> ~ y + x = z : rational

    plusq_shift_lrr : forall (x y z : rational) . x = y + z : rational <-> x + ~ z = y : rational

    plusq_shift_llr : forall (a b c : rational) . a = b + c : rational <-> a + ~ b = c : rational

    plusq_shift_lrl : forall (a b c : rational) . a = b + c : rational <-> ~ c + a = b : rational

    plusq_shift_rrr : forall (x y z : rational) . x + y = z : rational <-> x = z + ~ y : rational

    plusq_shift_rll : forall (x y z : rational) . x + y = z : rational <-> y = ~ x + z : rational

    plusq_shift_rlr : forall (a b c : rational) . a + b = c : rational <-> b = c + ~ a : rational

    plusq_shift_rrl : forall (a b c : rational) . a + b = c : rational <-> a = ~ b + c : rational

    negq_minusq : forall (x y : rational) . ~ (x - y) = y - x : rational

    minusq_cancel_r : forall (a b c : rational) . a - c = b - c : rational -> a = b : rational

    minusq_cancel_l : forall (a b c : rational) . c - a = c - b : rational -> a = b : rational

In each of the `minusq` shift lemmas, the subtraction term is on the
right of the `<->`.  Then the first letter indicates which direction
the subtrahend is moving, the second indicates which operand it is
before moving.  It is always the right-hand operand after moving.

    minusq_shift_ll : forall (a b c : rational) . a = b + c : rational <-> a - b = c : rational

    minusq_shift_lr : forall (a b c : rational) . a = b + c : rational <-> a - c = b : rational

    minusq_shift_rr : forall (a b c : rational) . a + b = c : rational <-> a = c - b : rational

    minusq_shift_rl : forall (a b c : rational) . a + b = c : rational <-> b = c - a : rational

    plusq_compat : forall (x x' y y' : rational) .
                      x = x' : rational -> y = y' : rational -> x + y = x' + y' : rational

    minusq_compat : forall (x x' y y' : rational) .
                       x = x' : rational -> y = y' : rational -> x - y = x' - y' : rational

    negq_compat : forall (x x' : rational) . x = x' : rational -> ~ x = ~ x' : rational


### Times and inverse

    (* *z *)
    timesq : rational -> rational -> rational

To simplify the type of `invq`, we permit division by zero and we set
its result to zero.  Naturally, the divisor usually must be nonzero
for `invq` to have good properties.

    invq : rational -> rational

    (* |q *)
    divq : rational -> rational -> rational
         = fn x y . x * invq y

    timesq_commute : forall (x y : rational) . x * y = y * x : rational

    timesq_assoc : forall (x y z : rational) . x * y * z = x * (y * z) : rational

    divq_assoc : forall (a b c : rational) . a || b || c = a || (b * c) : rational

    timesq_divq_assoc : forall (a b c : rational) . a * b || c = a * (b || c) : rational

    divq_timesq_assoc : forall (a b c : rational) . a || b * c = a || (b || c) : rational

    timesq_id_l : forall (x : rational) . 1 * x = x : rational

    timesq_id_r : forall (x : rational) . x * 1 = x : rational

    divq_id_l : forall (a : rational) . 1 || a = invq a : rational

    divq_id_r : forall (a : rational) . a || 1 = a : rational

    timesq_ann_l : forall (x : rational) . 0 * x = 0 : rational

    timesq_ann_r : forall (x : rational) . x * 0 = 0 : rational

    invq_invol : forall (x : rational) . invq (invq x) = x : rational

    timesq_inverse_l : forall (x : rational) . x != 0 : rational -> invq x * x = 1 : rational

    timesq_inverse_r : forall (x : rational) . x != 0 : rational -> x * invq x = 1 : rational

    divq_self : forall (a : rational) . a != 0 : rational -> a || a = 1 : rational

    invq_timesq : forall (x y : rational) . invq (x * y) = invq x * invq y : rational

This only works because of our special definition of `invq`.

    invq_zero : invq 0 = 0 : rational

    invq_nonzero : forall (x : rational) . x != 0 : rational -> invq x != 0 : rational

    invq_one : invq 1 = 1 : rational

    invq_injective : forall (x y : rational) . invq x = invq y : rational -> x = y : rational

    rational_integral_domain : forall (x y : rational) .
                                  x * y = 0 : rational -> x = 0 : rational % y = 0 : rational

    timesq_cancel_l : forall (x y z : rational) .
                         z != 0 : rational -> z * x = z * y : rational -> x = y : rational

    timesq_cancel_r : forall (x y z : rational) .
                         z != 0 : rational -> x * z = y * z : rational -> x = y : rational

    timesq_shift_lll : forall (x y z : rational) .
                          y != 0 : rational -> x = y * z : rational <-> invq y * x = z : rational

    timesq_shift_lrr : forall (x y z : rational) .
                          z != 0 : rational -> x = y * z : rational <-> x * invq z = y : rational

    timesq_shift_llr : forall (x y z : rational) .
                          y != 0 : rational -> x = y * z : rational <-> x * invq y = z : rational

    timesq_shift_lrl : forall (x y z : rational) .
                          z != 0 : rational -> x = y * z : rational <-> invq z * x = y : rational

    timesq_shift_rrr : forall (x y z : rational) .
                          y != 0 : rational -> x * y = z : rational <-> x = z * invq y : rational

    timesq_shift_rll : forall (x y z : rational) .
                          x != 0 : rational -> x * y = z : rational <-> y = invq x * z : rational

    timesq_shift_rlr : forall (x y z : rational) .
                          x != 0 : rational -> x * y = z : rational <-> y = z * invq x : rational

    timesq_shift_rrl : forall (x y z : rational) .
                          y != 0 : rational -> x * y = z : rational <-> x = invq y * z : rational

    divq_cancel_l : forall (a b c : rational) .
                       c != 0 : rational -> c || a = c || b : rational -> a = b : rational

    divq_cancel_r : forall (a b c : rational) .
                       c != 0 : rational -> a || c = b || c : rational -> a = b : rational

    divq_shift_ll : forall (a b c : rational) .
                       b != 0 : rational -> a = b * c : rational <-> a || b = c : rational

    divq_shift_lr : forall (a b c : rational) .
                       c != 0 : rational -> a = b * c : rational <-> a || c = b : rational

    divq_shift_rr : forall (a b c : rational) .
                       b != 0 : rational -> a * b = c : rational <-> a = c || b : rational

    divq_shift_rl : forall (a b c : rational) .
                       a != 0 : rational -> a * b = c : rational <-> b = c || a : rational

    timesq_compat : forall (x x' y y' : rational) .
                       x = x' : rational -> y = y' : rational -> x * y = x' * y' : rational

    invq_compat : forall (x x' : rational) . x = x' : rational -> invq x = invq x' : rational


### Distributivity

    timesq_dist_plusq_l : forall (x y z : rational) . (x + y) * z = x * z + y * z : rational

    timesq_dist_plusq_r : forall (x y z : rational) . x * (y + z) = x * y + x * z : rational

    negq_dist_plusq : forall (x y : rational) . ~ (x + y) = ~ x + ~ y : rational

    timesq_dist_minusq_l : forall (a b c : rational) . (a - b) * c = a * c - b * c : rational

    timesq_dist_minusq_r : forall (a b c : rational) . a * (b - c) = a * b - a * c : rational

    negq_dist_timesq_l : forall (x y : rational) . ~ (x * y) = ~ x * y : rational

    negq_dist_timesq_r : forall (x y : rational) . ~ (x * y) = x * ~ y : rational

    negq_dist_invq : forall (x : rational) . ~ (invq x) = invq (~ x) : rational

    negq_dist_divq_l : forall (x y : rational) . ~ (x || y) = ~ x || y : rational

    negq_dist_divq_r : forall (x y : rational) . ~ (x || y) = x || ~ y : rational

    negq_as_timesq : forall (x : rational) . ~ x = -1 * x : rational

    plusq_self : forall (a : rational) . a + a = 2 * a : rational


### Inequalities

    (* <q= *)
    leqq : rational -> rational -> U 0

    (* <q *)
    ltq : rational -> rational -> U 0

    leqq_inhabitant : forall (x y : rational) . x <= y -> () : x <= y

    ltq_inhabitant : forall (x y : rational) . x < y -> () : x < y

    leqq_refl : forall (x : rational) . x <= x

    leqq_refl_eq : forall (x y : rational) . x = y : rational -> x <= y

    leqq_trans : forall (x y z : rational) . x <= y -> y <= z -> x <= z

    leqq_antisymm : forall (x y : rational) . x <= y -> y <= x -> x = y : rational

    ltq_irrefl : forall (x : rational) . x < x -> void

    leqq_ltq_trans : forall (x y z : rational) . x <= y -> y < z -> x < z

    ltq_leqq_trans : forall (x y z : rational) . x < y -> y <= z -> x < z

    ltq_trans : forall (x y z : rational) . x < y -> y < z -> x < z

    ltq_impl_leqq : forall (x y : rational) . x < y -> x <= y

    ltq_impl_neq : forall (x y : rational) . x < y -> x != y : rational

This one gives transitivity in the form needed for rewriting:

    leqq_implication : forall (x x' y y' : rational) . x' <= x -> y <= y' -> x <= y -> x' <= y'

    ltq_implication : forall (x x' y y' : rational) . x' <= x -> y <= y' -> x < y -> x' < y'

    not_leqq : forall (x y : rational) . not (x <= y) <-> y < x

    not_ltq : forall (x y : rational) . not (x < y) <-> y <= x

    ltq_from_leqq_neq : forall (x y : rational) . x <= y -> not (x = y : rational) -> x < y

    ltq_0_1 : 0 < 1

    neqq_0_1 : 0 != 1 : rational

    leqq_0_1 : 0 <= 1

    ltq_neg1_0 : -1 < 0

    leqq_neg1_0 : -1 <= 0

    neqq_neg1_0 : -1 != 0 : rational


### Plus and negation inequality

    plusq_leqq : forall (x x' y y' : rational) . x <= x' -> y <= y' -> x + y <= x' + y'

    plusq_ltq_l : forall (x x' y y' : rational) . x < x' -> y <= y' -> x + y < x' + y'

    plusq_ltq_r : forall (x x' y y' : rational) . x <= x' -> y < y' -> x + y < x' + y'

    plusq_ltq : forall (x x' y y' : rational) . x < x' -> y < y' -> x + y < x' + y'

    plusq_cancel_leqq_l : forall (x y z : rational) . z + x <= z + y -> x <= y

    plusq_cancel_leqq_r : forall (x y z : rational) . x + z <= y + z -> x <= y

    plusq_cancel_leqq_leqq_l : forall (x x' y y' : rational) .
                                  x + y <= x' + y' -> x' <= x -> y <= y'

    plusq_cancel_leqq_leqq_r : forall (x x' y y' : rational) .
                                  x + y <= x' + y' -> y' <= y -> x <= x'

    plusq_shift_leqq_lll : forall (x y z : rational) . x <= y + z <-> ~ y + x <= z

    plusq_shift_leqq_lrr : forall (x y z : rational) . x <= y + z <-> x + ~ z <= y

    plusq_shift_leqq_llr : forall (x y z : rational) . x <= y + z <-> x + ~ y <= z

    plusq_shift_leqq_lrl : forall (x y z : rational) . x <= y + z <-> ~ z + x <= y

    plusq_shift_leqq_rrr : forall (x y z : rational) . x + y <= z <-> x <= z + ~ y

    plusq_shift_leqq_rll : forall (x y z : rational) . x + y <= z <-> y <= ~ x + z

    plusq_shift_leqq_rlr : forall (x y z : rational) . x + y <= z <-> y <= z + ~ x

    plusq_shift_leqq_rrl : forall (x y z : rational) . x + y <= z <-> x <= ~ y + z

    plusq_cancel_ltq_l : forall (x y z : rational) . z + x < z + y -> x < y

    plusq_cancel_ltq_r : forall (x y z : rational) . x + z < y + z -> x < y

    plusq_shift_ltq_lll : forall (x y z : rational) . x < y + z <-> ~ y + x < z

    plusq_shift_ltq_lrr : forall (x y z : rational) . x < y + z <-> x + ~ z < y

    plusq_shift_ltq_llr : forall (x y z : rational) . x < y + z <-> x + ~ y < z

    plusq_shift_ltq_lrl : forall (x y z : rational) . x < y + z <-> ~ z + x < y

    plusq_shift_ltq_rrr : forall (x y z : rational) . x + y < z <-> x < z + ~ y

    plusq_shift_ltq_rll : forall (x y z : rational) . x + y < z <-> y < ~ x + z

    plusq_shift_ltq_rlr : forall (x y z : rational) . x + y < z <-> y < z + ~ x

    plusq_shift_ltq_rrl : forall (x y z : rational) . x + y < z <-> x < ~ y + z

    negq_leqq : forall (x y : rational) . x <= y -> ~ y <= ~ x

    negq_leqq' : forall (x y : rational) . ~ y <= ~ x -> x <= y

    negq_ltq : forall (x y : rational) . x < y -> ~ y < ~ x

    negq_ltq' : forall (x y : rational) . ~ y < ~ x -> x < y

    minusq_leqq : forall (a a' b b' : rational) . a <= a' -> b' <= b -> a - b <= a' - b'

    minusq_cancel_leqq_l : forall (a b c : rational) . c - a <= c - b -> b <= a

    minusq_cancel_leqq_r : forall (a b c : rational) . a - c <= b - c -> a <= b

    minusq_cancel_ltq_l : forall (a b c : rational) . c - a < c - b -> b < a

    minusq_cancel_ltq_r : forall (a b c : rational) . a - c < b - c -> a < b

    minusq_shift_leqq_ll : forall (a b c : rational) . a <= b + c <-> a - b <= c

    minusq_shift_leqq_lr : forall (a b c : rational) . a <= b + c <-> a - c <= b

    minusq_shift_leqq_rr : forall (a b c : rational) . a + b <= c <-> a <= c - b

    minusq_shift_leqq_rl : forall (a b c : rational) . a + b <= c <-> b <= c - a

    minusq_shift_ltq_ll : forall (a b c : rational) . a < b + c <-> a - b < c

    minusq_shift_ltq_lr : forall (a b c : rational) . a < b + c <-> a - c < b

    minusq_shift_ltq_rr : forall (a b c : rational) . a + b < c <-> a < c - b

    minusq_shift_ltq_rl : forall (a b c : rational) . a + b < c <-> b < c - a


### Times and inverse inequality

    timesq_leqq : forall (x x' y y' : rational) .
                     0 <= x -> 0 <= y -> x <= x' -> y <= y' -> x * y <= x' * y'

    (* an alias for timesq_leqq *)
    timesq_leqq_pos_pos : forall (x x' y y' : rational) .
                             0 <= x -> 0 <= y -> x <= x' -> y <= y' -> x * y <= x' * y'

    timesq_leqq_neg_neg : forall (x x' y y' : rational) .
                             x' <= 0 -> y' <= 0 -> x <= x' -> y <= y' -> x' * y' <= x * y

    timesq_leqq_pos_neg : forall (x x' y y' : rational) .
                             0 <= x -> y' <= 0 -> x <= x' -> y <= y' -> x' * y <= x * y'

    timesq_leqq_neg_neg : forall (x x' y y' : rational) .
                             x' <= 0 -> y' <= 0 -> x <= x' -> y <= y' -> x' * y' <= x * y

    timesq_leqq_zero : forall (x y : rational) . 0 <= x -> 0 <= y -> 0 <= x * y

    (* an alias for timesq_leqq_zero *)
    timesq_leqq_zero_pos_pos : forall (x y : rational) . 0 <= x -> 0 <= y -> 0 <= x * y

    timesq_leqq_zero_pos_neg : forall (x y : rational) . 0 <= x -> y <= 0 -> x * y <= 0

    timesq_leqq_zero_neg_pos : forall (x y : rational) . x <= 0 -> 0 <= y -> x * y <= 0

    timesq_leqq_zero_neg_neg : forall (x y : rational) . x <= 0 -> y <= 0 -> 0 <= x * y

    timesq_leqq_l : forall (x y y' : rational) . 0 <= x -> y <= y' -> x * y <= x * y'

    timesq_leqq_r : forall (x x' y : rational) . x <= x' -> 0 <= y -> x * y <= x' * y

    timesq_leqq_l_neg : forall (x y y' : rational) . x <= 0 -> y <= y' -> x * y' <= x * y

    timesq_leqq_r_neg : forall (x x' y : rational) . x <= x' -> y <= 0 -> x' * y <= x * y

    timesq_ltq_l : forall (x y y' : rational) . 0 < x -> y < y' -> x * y < x * y'

    timesq_ltq_r : forall (x x' y : rational) . 0 < y -> x < x' -> x * y < x' * y

    timesq_ltq_l_neg : forall (x y y' : rational) . x < 0 -> y < y' -> x * y' < x * y

    timesq_ltq_r_neg : forall (x x' y : rational) . x < x' -> y < 0 -> x' * y < x * y

    timesq_ltq_zero : forall (x y : rational) . 0 < x -> 0 < y -> 0 < x * y

    (* an alias for timesq_ltq_zero *)
    timesq_ltq_zero_pos_pos : forall (x y : rational) . 0 < x -> 0 < y -> 0 < x * y

    timesq_ltq_zero_pos_neg : forall (x y : rational) . 0 < x -> y < 0 -> x * y < 0

    timesq_ltq_zero_neg_pos : forall (x y : rational) . x < 0 -> 0 < y -> x * y < 0

    timesq_ltq_zero_neg_neg : forall (x y : rational) . x < 0 -> y < 0 -> 0 < x * y

    timesq_neq_zero : forall (x y : rational) .
                         x != 0 : rational -> y != 0 : rational -> x * y != 0 : rational

    timesq_ltq_zero_invert : forall (x y : rational) . 0 < x * y -> x < 0 & y < 0 % 0 < x & 0 < y

    timesq_ltq_zero_invert_neg : forall (x y : rational) .
                                    x * y < 0 -> x < 0 & 0 < y % 0 < x & y < 0

    timesq_cancel_leqq_l : forall (x y z : rational) . 0 < z -> z * x <= z * y -> x <= y

    timesq_cancel_leqq_r : forall (x y z : rational) . 0 < z -> x * z <= y * z -> x <= y

    timesq_cancel_ltq_l : forall (x y z : rational) . 0 < z -> z * x < z * y -> x < y

    timesq_cancel_ltq_r : forall (x y z : rational) . 0 < z -> x * z < y * z -> x < y

    timesq_cancel_leqq_l_neg : forall (x y z : rational) . z < 0 -> z * x <= z * y -> y <= x

    timesq_cancel_leqq_r_neg : forall (x y z : rational) . z < 0 -> x * z <= y * z -> y <= x

    timesq_cancel_ltq_l_neg : forall (x y z : rational) . z < 0 -> z * x < z * y -> y < x

    timesq_cancel_ltq_r_neg : forall (x y z : rational) . z < 0 -> x * z < y * z -> y < x

    timesq_shift_leqq_lll : forall (x y z : rational) . 0 < y -> x <= y * z <-> invq y * x <= z

    timesq_shift_leqq_lrr : forall (x y z : rational) . 0 < z -> x <= y * z <-> x * invq z <= y

    timesq_shift_leqq_llr : forall (x y z : rational) . 0 < y -> x <= y * z <-> x * invq y <= z

    timesq_shift_leqq_lrl : forall (x y z : rational) . 0 < z -> x <= y * z <-> invq z * x <= y

    timesq_shift_leqq_rrr : forall (x y z : rational) . 0 < y -> x * y <= z <-> x <= z * invq y

    timesq_shift_leqq_rll : forall (x y z : rational) . 0 < x -> x * y <= z <-> y <= invq x * z

    timesq_shift_leqq_rlr : forall (x y z : rational) . 0 < x -> x * y <= z <-> y <= z * invq x

    timesq_shift_leqq_rrl : forall (x y z : rational) . 0 < y -> x * y <= z <-> x <= invq y * z

    timesq_shift_ltq_lll : forall (x y z : rational) . 0 < y -> x < y * z <-> invq y * x < z

    timesq_shift_ltq_lrr : forall (x y z : rational) . 0 < z -> x < y * z <-> x * invq z < y

    timesq_shift_ltq_llr : forall (x y z : rational) . 0 < y -> x < y * z <-> x * invq y < z

    timesq_shift_ltq_lrl : forall (x y z : rational) . 0 < z -> x < y * z <-> invq z * x < y

    timesq_shift_ltq_rrr : forall (x y z : rational) . 0 < y -> x * y < z <-> x < z * invq y

    timesq_shift_ltq_rll : forall (x y z : rational) . 0 < x -> x * y < z <-> y < invq x * z

    timesq_shift_ltq_rlr : forall (x y z : rational) . 0 < x -> x * y < z <-> y < z * invq x

    timesq_shift_ltq_rrl : forall (x y z : rational) . 0 < y -> x * y < z <-> x < invq y * z

In the negative multiplicative shifts, the naming is as though the
inequality did not reverse on the right.

    timesq_shift_leqq_lll_neg : forall (x y z : rational) .
                                   y < 0 -> x <= y * z <-> z <= invq y * x

    timesq_shift_leqq_lrr_neg : forall (x y z : rational) .
                                   z < 0 -> x <= y * z <-> y <= x * invq z

    timesq_shift_leqq_llr_neg : forall (x y z : rational) .
                                   y < 0 -> x <= y * z <-> z <= x * invq y

    timesq_shift_leqq_lrl_neg : forall (x y z : rational) .
                                   z < 0 -> x <= y * z <-> y <= invq z * x

    timesq_shift_leqq_rrr_neg : forall (x y z : rational) .
                                   y < 0 -> x * y <= z <-> z * invq y <= x

    timesq_shift_leqq_rll_neg : forall (x y z : rational) .
                                   x < 0 -> x * y <= z <-> invq x * z <= y

    timesq_shift_leqq_rlr_neg : forall (x y z : rational) .
                                   x < 0 -> x * y <= z <-> z * invq x <= y

    timesq_shift_leqq_rrl_neg : forall (x y z : rational) .
                                   y < 0 -> x * y <= z <-> invq y * z <= x

    timesq_shift_ltq_lll_neg : forall (x y z : rational) . y < 0 -> x < y * z <-> z < invq y * x

    timesq_shift_ltq_lrr_neg : forall (x y z : rational) . z < 0 -> x < y * z <-> y < x * invq z

    timesq_shift_ltq_llr_neg : forall (x y z : rational) . y < 0 -> x < y * z <-> z < x * invq y

    timesq_shift_ltq_lrl_neg : forall (x y z : rational) . z < 0 -> x < y * z <-> y < invq z * x

    timesq_shift_ltq_rrr_neg : forall (x y z : rational) . y < 0 -> x * y < z <-> z * invq y < x

    timesq_shift_ltq_rll_neg : forall (x y z : rational) . x < 0 -> x * y < z <-> invq x * z < y

    timesq_shift_ltq_rlr_neg : forall (x y z : rational) . x < 0 -> x * y < z <-> z * invq x < y

    timesq_shift_ltq_rrl_neg : forall (x y z : rational) . y < 0 -> x * y < z <-> invq y * z < x

    divq_shift_leqq_ll : forall (a b c : rational) . 0 < b -> a <= b * c <-> a || b <= c

    divq_shift_leqq_lr : forall (a b c : rational) . 0 < c -> a <= b * c <-> a || c <= b

    divq_shift_leqq_rr : forall (a b c : rational) . 0 < b -> a * b <= c <-> a <= c || b

    divq_shift_leqq_rl : forall (a b c : rational) . 0 < a -> a * b <= c <-> b <= c || a

    divq_shift_ltq_ll : forall (a b c : rational) . 0 < b -> a < b * c <-> a || b < c

    divq_shift_ltq_lr : forall (a b c : rational) . 0 < c -> a < b * c <-> a || c < b

    divq_shift_ltq_rr : forall (a b c : rational) . 0 < b -> a * b < c <-> a < c || b

    divq_shift_ltq_rl : forall (a b c : rational) . 0 < a -> a * b < c <-> b < c || a

    divq_shift_leqq_ll_neg : forall (a b c : rational) . b < 0 -> a <= b * c <-> c <= a || b

    divq_shift_leqq_lr_neg : forall (a b c : rational) . c < 0 -> a <= b * c <-> b <= a || c

    divq_shift_leqq_rr_neg : forall (a b c : rational) . b < 0 -> a * b <= c <-> c || b <= a

    divq_shift_leqq_rl_neg : forall (a b c : rational) . a < 0 -> a * b <= c <-> c || a <= b

    divq_shift_ltq_ll_neg : forall (a b c : rational) . b < 0 -> a < b * c <-> c < a || b

    divq_shift_ltq_lr_neg : forall (a b c : rational) . c < 0 -> a < b * c <-> b < a || c

    divq_shift_ltq_rr_neg : forall (a b c : rational) . b < 0 -> a * b < c <-> c || b < a

    divq_shift_ltq_rl_neg : forall (a b c : rational) . a < 0 -> a * b < c <-> c || a < b

    invq_positive : forall (x : rational) . 0 < x -> 0 < invq x

    invq_negative : forall (x : rational) . x < 0 -> invq x < 0

    invq_nonnegative : forall (x : rational) . 0 <= x -> 0 <= invq x

    invq_nonpositive : forall (x : rational) . x <= 0 -> invq x <= 0

    divq_leqq_zero : forall (x y : rational) . 0 <= x -> 0 <= y -> 0 <= x || y

    divq_leqq_zero_pos_pos : forall (x y : rational) . 0 <= x -> 0 <= y -> 0 <= x || y

    divq_leqq_zero_pos_neg : forall (x y : rational) . 0 <= x -> y <= 0 -> x || y <= 0

    divq_leqq_zero_neg_pos : forall (x y : rational) . x <= 0 -> 0 <= y -> x || y <= 0

    divq_leqq_zero_neg_neg : forall (x y : rational) . x <= 0 -> y <= 0 -> 0 <= x || y

    divq_ltq_zero : forall (x y : rational) . 0 < x -> 0 < y -> 0 < x || y

    divq_ltq_zero_pos_pos : forall (x y : rational) . 0 < x -> 0 < y -> 0 < x || y

    divq_ltq_zero_pos_neg : forall (x y : rational) . 0 < x -> y < 0 -> x || y < 0

    divq_ltq_zero_neg_pos : forall (x y : rational) . x < 0 -> 0 < y -> x || y < 0

    divq_ltq_zero_neg_neg : forall (x y : rational) . x < 0 -> y < 0 -> 0 < x || y

    (* an alias for timesq_leqq *)
    timesq_leqq_pos_pos : forall (x x' y y' : rational) .
                             0 <= x -> 0 <= y -> x <= x' -> y <= y' -> x * y <= x' * y'

    timesq_leqq_neg_neg : forall (x x' y y' : rational) .
                             x' <= 0 -> y' <= 0 -> x <= x' -> y <= y' -> x' * y' <= x * y

    timesq_leqq_pos_neg : forall (x x' y y' : rational) .
                             0 <= x -> y' <= 0 -> x <= x' -> y <= y' -> x' * y <= x * y'

    timesq_leqq_neg_neg : forall (x x' y y' : rational) .
                             x' <= 0 -> y' <= 0 -> x <= x' -> y <= y' -> x' * y' <= x * y

    timesq_leqq_zero : forall (x y : rational) . 0 <= x -> 0 <= y -> 0 <= x * y

    (* an alias for timesq_leqq_zero *)
    timesq_leqq_zero_pos_pos : forall (x y : rational) . 0 <= x -> 0 <= y -> 0 <= x * y

    timesq_leqq_zero_pos_neg : forall (x y : rational) . 0 <= x -> y <= 0 -> x * y <= 0

    timesq_leqq_zero_neg_pos : forall (x y : rational) . x <= 0 -> 0 <= y -> x * y <= 0

    timesq_leqq_zero_neg_neg : forall (x y : rational) . x <= 0 -> y <= 0 -> 0 <= x * y

    timesq_leqq_l : forall (x y y' : rational) . 0 <= x -> y <= y' -> x * y <= x * y'

    timesq_leqq_r : forall (x x' y : rational) . x <= x' -> 0 <= y -> x * y <= x' * y

    timesq_leqq_l_neg : forall (x y y' : rational) . x <= 0 -> y <= y' -> x * y' <= x * y

    timesq_leqq_r_neg : forall (x x' y : rational) . x <= x' -> y <= 0 -> x' * y <= x * y

    timesq_ltq_l : forall (x y y' : rational) . 0 < x -> y < y' -> x * y < x * y'

    timesq_ltq_r : forall (x x' y : rational) . 0 < y -> x < x' -> x * y < x' * y

    timesq_ltq_l_neg : forall (x y y' : rational) . x < 0 -> y < y' -> x * y' < x * y

    timesq_ltq_r_neg : forall (x x' y : rational) . x < x' -> y < 0 -> x' * y < x * y

    timesq_ltq_zero : forall (x y : rational) . 0 < x -> 0 < y -> 0 < x * y

    (* an alias for timesq_ltq_zero *)
    timesq_ltq_zero_pos_pos : forall (x y : rational) . 0 < x -> 0 < y -> 0 < x * y

    timesq_ltq_zero_pos_neg : forall (x y : rational) . 0 < x -> y < 0 -> x * y < 0

    timesq_ltq_zero_neg_pos : forall (x y : rational) . x < 0 -> 0 < y -> x * y < 0

    timesq_ltq_zero_neg_neg : forall (x y : rational) . x < 0 -> y < 0 -> 0 < x * y

    timesq_neq_zero : forall (x y : rational) .
                         x != 0 : rational -> y != 0 : rational -> x * y != 0 : rational

    timesq_ltq_zero_invert : forall (x y : rational) . 0 < x * y -> x < 0 & y < 0 % 0 < x & 0 < y

    timesq_ltq_zero_invert_neg : forall (x y : rational) .
                                    x * y < 0 -> x < 0 & 0 < y % 0 < x & y < 0

    timesq_cancel_leqq_l : forall (x y z : rational) . 0 < z -> z * x <= z * y -> x <= y

    timesq_cancel_leqq_r : forall (x y z : rational) . 0 < z -> x * z <= y * z -> x <= y

    timesq_cancel_ltq_l : forall (x y z : rational) . 0 < z -> z * x < z * y -> x < y

    timesq_cancel_ltq_r : forall (x y z : rational) . 0 < z -> x * z < y * z -> x < y

    timesq_cancel_leqq_l_neg : forall (x y z : rational) . z < 0 -> z * x <= z * y -> y <= x

    timesq_cancel_leqq_r_neg : forall (x y z : rational) . z < 0 -> x * z <= y * z -> y <= x

    timesq_cancel_ltq_l_neg : forall (x y z : rational) . z < 0 -> z * x < z * y -> y < x

    timesq_cancel_ltq_r_neg : forall (x y z : rational) . z < 0 -> x * z < y * z -> y < x

    timesq_shift_leqq_lll : forall (x y z : rational) . 0 < y -> x <= y * z <-> invq y * x <= z

    timesq_shift_leqq_lrr : forall (x y z : rational) . 0 < z -> x <= y * z <-> x * invq z <= y

    timesq_shift_leqq_llr : forall (x y z : rational) . 0 < y -> x <= y * z <-> x * invq y <= z

    timesq_shift_leqq_lrl : forall (x y z : rational) . 0 < z -> x <= y * z <-> invq z * x <= y

    timesq_shift_leqq_rrr : forall (x y z : rational) . 0 < y -> x * y <= z <-> x <= z * invq y

    timesq_shift_leqq_rll : forall (x y z : rational) . 0 < x -> x * y <= z <-> y <= invq x * z

    timesq_shift_leqq_rlr : forall (x y z : rational) . 0 < x -> x * y <= z <-> y <= z * invq x

    timesq_shift_leqq_rrl : forall (x y z : rational) . 0 < y -> x * y <= z <-> x <= invq y * z

    timesq_shift_ltq_lll : forall (x y z : rational) . 0 < y -> x < y * z <-> invq y * x < z

    timesq_shift_ltq_lrr : forall (x y z : rational) . 0 < z -> x < y * z <-> x * invq z < y

    timesq_shift_ltq_llr : forall (x y z : rational) . 0 < y -> x < y * z <-> x * invq y < z

    timesq_shift_ltq_lrl : forall (x y z : rational) . 0 < z -> x < y * z <-> invq z * x < y

    timesq_shift_ltq_rrr : forall (x y z : rational) . 0 < y -> x * y < z <-> x < z * invq y

    timesq_shift_ltq_rll : forall (x y z : rational) . 0 < x -> x * y < z <-> y < invq x * z

    timesq_shift_ltq_rlr : forall (x y z : rational) . 0 < x -> x * y < z <-> y < z * invq x

    timesq_shift_ltq_rrl : forall (x y z : rational) . 0 < y -> x * y < z <-> x < invq y * z

In the negative multiplicative shifts, the naming is as though the
inequality did not reverse on the right.

    timesq_shift_leqq_lll_neg : forall (x y z : rational) .
                                   y < 0 -> x <= y * z <-> z <= invq y * x

    timesq_shift_leqq_lrr_neg : forall (x y z : rational) .
                                   z < 0 -> x <= y * z <-> y <= x * invq z

    timesq_shift_leqq_llr_neg : forall (x y z : rational) .
                                   y < 0 -> x <= y * z <-> z <= x * invq y

    timesq_shift_leqq_lrl_neg : forall (x y z : rational) .
                                   z < 0 -> x <= y * z <-> y <= invq z * x

    timesq_shift_leqq_rrr_neg : forall (x y z : rational) .
                                   y < 0 -> x * y <= z <-> z * invq y <= x

    timesq_shift_leqq_rll_neg : forall (x y z : rational) .
                                   x < 0 -> x * y <= z <-> invq x * z <= y

    timesq_shift_leqq_rlr_neg : forall (x y z : rational) .
                                   x < 0 -> x * y <= z <-> z * invq x <= y

    timesq_shift_leqq_rrl_neg : forall (x y z : rational) .
                                   y < 0 -> x * y <= z <-> invq y * z <= x

    timesq_shift_ltq_lll_neg : forall (x y z : rational) . y < 0 -> x < y * z <-> z < invq y * x

    timesq_shift_ltq_lrr_neg : forall (x y z : rational) . z < 0 -> x < y * z <-> y < x * invq z

    timesq_shift_ltq_llr_neg : forall (x y z : rational) . y < 0 -> x < y * z <-> z < x * invq y

    timesq_shift_ltq_lrl_neg : forall (x y z : rational) . z < 0 -> x < y * z <-> y < invq z * x

    timesq_shift_ltq_rrr_neg : forall (x y z : rational) . y < 0 -> x * y < z <-> z * invq y < x

    timesq_shift_ltq_rll_neg : forall (x y z : rational) . x < 0 -> x * y < z <-> invq x * z < y

    timesq_shift_ltq_rlr_neg : forall (x y z : rational) . x < 0 -> x * y < z <-> z * invq x < y

    timesq_shift_ltq_rrl_neg : forall (x y z : rational) . y < 0 -> x * y < z <-> invq y * z < x

    divq_shift_leqq_ll : forall (a b c : rational) . 0 < b -> a <= b * c <-> a || b <= c

    divq_shift_leqq_lr : forall (a b c : rational) . 0 < c -> a <= b * c <-> a || c <= b

    divq_shift_leqq_rr : forall (a b c : rational) . 0 < b -> a * b <= c <-> a <= c || b

    divq_shift_leqq_rl : forall (a b c : rational) . 0 < a -> a * b <= c <-> b <= c || a

    divq_shift_ltq_ll : forall (a b c : rational) . 0 < b -> a < b * c <-> a || b < c

    divq_shift_ltq_lr : forall (a b c : rational) . 0 < c -> a < b * c <-> a || c < b

    divq_shift_ltq_rr : forall (a b c : rational) . 0 < b -> a * b < c <-> a < c || b

    divq_shift_ltq_rl : forall (a b c : rational) . 0 < a -> a * b < c <-> b < c || a

    divq_shift_leqq_ll_neg : forall (a b c : rational) . b < 0 -> a <= b * c <-> c <= a || b

    divq_shift_leqq_lr_neg : forall (a b c : rational) . c < 0 -> a <= b * c <-> b <= a || c

    divq_shift_leqq_rr_neg : forall (a b c : rational) . b < 0 -> a * b <= c <-> c || b <= a

    divq_shift_leqq_rl_neg : forall (a b c : rational) . a < 0 -> a * b <= c <-> c || a <= b

    divq_shift_ltq_ll_neg : forall (a b c : rational) . b < 0 -> a < b * c <-> c < a || b

    divq_shift_ltq_lr_neg : forall (a b c : rational) . c < 0 -> a < b * c <-> b < a || c

    divq_shift_ltq_rr_neg : forall (a b c : rational) . b < 0 -> a * b < c <-> c || b < a

    divq_shift_ltq_rl_neg : forall (a b c : rational) . a < 0 -> a * b < c <-> c || a < b

    invq_positive : forall (x : rational) . 0 < x -> 0 < invq x

    invq_negative : forall (x : rational) . x < 0 -> invq x < 0

    invq_nonnegative : forall (x : rational) . 0 <= x -> 0 <= invq x

    invq_nonpositive : forall (x : rational) . x <= 0 -> invq x <= 0

    divq_leqq_zero : forall (x y : rational) . 0 <= x -> 0 <= y -> 0 <= x || y

    divq_leqq_zero_pos_pos : forall (x y : rational) . 0 <= x -> 0 <= y -> 0 <= x || y

    divq_leqq_zero_pos_neg : forall (x y : rational) . 0 <= x -> y <= 0 -> x || y <= 0

    divq_leqq_zero_neg_pos : forall (x y : rational) . x <= 0 -> 0 <= y -> x || y <= 0

    divq_leqq_zero_neg_neg : forall (x y : rational) . x <= 0 -> y <= 0 -> 0 <= x || y

    invq_leqq_pos : forall (x y : rational) . 0 < x -> x <= y -> invq y <= invq x

    invq_leqq_neg : forall (x y : rational) . y < 0 -> x <= y -> invq y <= invq x

    invq_ltq_pos : forall (x y : rational) . 0 < x -> x < y -> invq y < invq x

    invq_ltq_neg : forall (x y : rational) . y < 0 -> x < y -> invq y < invq x

    datatype
      intersect (i : level) . U i
    of
      samesign : rational -> rational -> type =
  
      | samesign_pos :
          forall x y .
            q`0 <q x
            -> q`0 <q y
            -> samesign x y
  
      | samesign_neg :
          forall x y .
            x <q q`0
            -> y <q q`0
            -> samesign x y

    invq_leqq_samesign : forall (x y : rational) . samesign x y -> x <= y -> invq y <= invq x

    invq_ltq_samesign : forall (x y : rational) . samesign x y -> x < y -> invq y < invq x


### Relation to integers

    integer_to_rational : integer -> rational

    integer_to_rational_injective : forall (a b : integer) .
                                       integer_to_rational a = integer_to_rational b : rational
                                       -> a = b : integer

    integer_to_rational_neq : forall (a b : integer) .
                                 a != b : integer
                                 -> integer_to_rational a != integer_to_rational b : rational

    integer_to_rational_mono : forall (a b : integer) .
                                  a <z= b -> integer_to_rational a <= integer_to_rational b

    integer_to_rational_mono_conv : forall (a b : integer) .
                                       integer_to_rational a <= integer_to_rational b -> a <z= b

    integer_to_rational_mono_lt : forall (a b : integer) .
                                     a <z b -> integer_to_rational a < integer_to_rational b

    integer_to_rational_mono_lt_conv : forall (a b : integer) .
                                          integer_to_rational a < integer_to_rational b -> a <z b

    plusz_to_rational : forall (a b : integer) .
                           integer_to_rational (a +z b)
                             = integer_to_rational a + integer_to_rational b
                             : rational

    negz_to_rational : forall (a : integer) .
                          integer_to_rational (~z a) = ~ (integer_to_rational a) : rational

    minusz_to_rational : forall (a b : integer) .
                            integer_to_rational (a -z b)
                              = integer_to_rational a - integer_to_rational b
                              : rational

    timesz_to_rational : forall (a b : integer) .
                            integer_to_rational (a *z b)
                              = integer_to_rational a * integer_to_rational b
                              : rational

    eqzb_to_rational : forall (a b : integer) .
                          a =z? b = integer_to_rational a =? integer_to_rational b : bool

    neqzb_to_rational : forall (a b : integer) .
                           a !z=? b = integer_to_rational a !=? integer_to_rational b : bool

    leqzb_to_rational : forall (a b : integer) .
                           a <z=? b = integer_to_rational a <=? integer_to_rational b : bool

    ltzb_to_rational : forall (a b : integer) .
                          a <z? b = integer_to_rational a <? integer_to_rational b : bool


#### Relation to natural numbers

    nat_to_rational : nat -> rational
                    = fn n . integer_to_rational (Integer.nat_to_integer n)

    nat_to_rational_injective : forall (a b : nat) .
                                   nat_to_rational a = nat_to_rational b : rational -> a = b : nat

    nat_to_rational_neq : forall (a b : nat) .
                             a != b : nat -> nat_to_rational a != nat_to_rational b : rational

    integer_nat_to_rational_eq : forall (a : integer) (b : nat) .
                                    a = Integer.nat_to_integer b : integer
                                    -> integer_to_rational a = nat_to_rational b : rational

    nat_integer_to_rational_eq : forall (a : nat) (b : integer) .
                                    Integer.nat_to_integer a = b : integer
                                    -> nat_to_rational a = integer_to_rational b : rational

    integer_nat_to_rational_neq : forall (a : integer) (b : nat) .
                                     a != Integer.nat_to_integer b : integer
                                     -> integer_to_rational a != nat_to_rational b : rational

    nat_integer_to_rational_neq : forall (a : nat) (b : integer) .
                                     Integer.nat_to_integer a != b : integer
                                     -> nat_to_rational a != integer_to_rational b : rational

    nat_to_rational_mono : forall (a b : nat) . a <n= b -> nat_to_rational a <= nat_to_rational b

    integer_nat_to_rational_mono : forall (a : integer) (b : nat) .
                                      a <z= Integer.nat_to_integer b
                                      -> integer_to_rational a <= nat_to_rational b

    nat_integer_to_rational_mono : forall (a : nat) (b : integer) .
                                      Integer.nat_to_integer a <z= b
                                      -> nat_to_rational a <= integer_to_rational b

    nat_to_rational_mono_lt : forall (a b : nat) . a <n b -> nat_to_rational a < nat_to_rational b

    integer_nat_to_rational_mono_lt : forall (a : integer) (b : nat) .
                                         a <z Integer.nat_to_integer b
                                         -> integer_to_rational a < nat_to_rational b

    nat_integer_to_rational_mono_lt : forall (a : nat) (b : integer) .
                                         Integer.nat_to_integer a <z b
                                         -> nat_to_rational a < integer_to_rational b

    nat_to_rational_nonneg : forall (n : nat) . 0 <= nat_to_rational n

    plus_to_rational : forall (a b : nat) .
                          nat_to_rational (a +n b)
                            = nat_to_rational a + nat_to_rational b
                            : rational

    succ_to_rational : forall (a : nat) .
                          nat_to_rational (succ a) = 1 + nat_to_rational a : rational

    times_to_rational : forall (a b : nat) .
                           nat_to_rational (a *n b)
                             = nat_to_rational a * nat_to_rational b
                             : rational

    eqb_to_rational : forall (a b : nat) . a =n? b = nat_to_rational a =? nat_to_rational b : bool

    leqb_to_rational : forall (a b : nat) .
                          a <n=? b = nat_to_rational a <=? nat_to_rational b : bool

    ltb_to_rational : forall (a b : nat) . a <n? b = nat_to_rational a <? nat_to_rational b : bool

    neqb_to_rational : forall (a b : nat) .
                          a !n=? b = nat_to_rational a !=? nat_to_rational b : bool


### Effective comparisons

    (* =q? *)
    eqqb : rational -> rational -> bool

    (* <q=? *)
    leqqb : rational -> rational -> bool

    (* <q? *)
    ltqb : rational -> rational -> bool

    (* !q=? *)
    neqqb : rational -> rational -> bool

    notb_eqqb : forall (x y : rational) . Bool.notb (x =? y) = x !=? y : bool

    notb_neqqb : forall (x y : rational) . Bool.notb (x !=? y) = x =? y : bool

    notb_leqqb : forall (x y : rational) . Bool.notb (x <=? y) = y <? x : bool

    notb_ltqb : forall (x y : rational) . Bool.notb (x <? y) = y <=? x : bool

    istrue_eqqb : forall (x y : rational) . Bool.istrue (x =? y) <-> x = y : rational

    istrue_neqqb : forall (x y : rational) . Bool.istrue (x !=? y) <-> x != y : rational

    istrue_leqqb : forall (x y : rational) . Bool.istrue (x <=? y) <-> x <= y

    istrue_ltqb : forall (x y : rational) . Bool.istrue (x <? y) <-> x < y


### Decidability

    eq_rational_decide : forall (x y : rational) . Decidable.decidable (x = y : rational)

    neq_rational_decide : forall (x y : rational) . Decidable.decidable (x != y : rational)

    leqq_decide : forall (x y : rational) . Decidable.decidable (x <= y)

    ltq_decide : forall (x y : rational) . Decidable.decidable (x < y)

    eq_rational_stable : forall (x y : rational) . Stable.stable (x = y : rational)

    neq_rational_stable : forall (x y : rational) . Stable.stable (x != y : rational)

    leqq_stable : forall (x y : rational) . Stable.stable (x <= y)

    ltq_stable : forall (x y : rational) . Stable.stable (x < y)

    leqq_iff_ltq_or_eq : forall (x y : rational) . x <= y <-> x < y % x = y : rational

    rational_trichotomy : forall (x y : rational) . x < y % x = y : rational % y < x

    rational_dichotomy : forall (x y : rational) . x <= y % y < x

    rational_dichotomy_weak : forall (x y : rational) . x <= y % y <= x

    rational_dichotomy_neq : forall (x y : rational) . x != y : rational -> x < y % y < x


### Minimum/Maximum

    minq : rational -> rational -> rational
         = fn a b . if a <=? b then a else b

    maxq : rational -> rational -> rational
         = fn a b . if a <=? b then b else a

    negq_minq : forall (a b : rational) . ~ (minq a b) = maxq (~ a) (~ b) : rational

    negq_maxq : forall (a b : rational) . ~ (maxq a b) = minq (~ a) (~ b) : rational

    maxq_as_minq : forall (a b : rational) . maxq a b = ~ (minq (~ a) (~ b)) : rational

    minq_as_maxq : forall (a b : rational) . minq a b = ~ (maxq (~ a) (~ b)) : rational

    minq_commute : forall (a b : rational) . minq a b = minq b a : rational

    maxq_commute : forall (a b : rational) . maxq a b = maxq b a : rational

    minq_assoc : forall (a b c : rational) . minq (minq a b) c = minq a (minq b c) : rational

    maxq_assoc : forall (a b c : rational) . maxq (maxq a b) c = maxq a (maxq b c) : rational

    minq_leq_l : forall (a b : rational) . minq a b <= a

    minq_leq_r : forall (a b : rational) . minq a b <= b

    maxq_leq_l : forall (a b : rational) . a <= maxq a b

    maxq_leq_r : forall (a b : rational) . b <= maxq a b

    minq_glb : forall (a b c : rational) . c <= a -> c <= b -> c <= minq a b

    maxq_lub : forall (a b c : rational) . a <= c -> b <= c -> maxq a b <= c

    minq_eq_l : forall (a b : rational) . a <= b -> minq a b = a : rational

    minq_eq_r : forall (a b : rational) . b <= a -> minq a b = b : rational

    maxq_eq_l : forall (a b : rational) . b <= a -> maxq a b = a : rational

    maxq_eq_r : forall (a b : rational) . a <= b -> maxq a b = b : rational

    minq_idem : forall (a : rational) . minq a a = a : rational

    maxq_idem : forall (a : rational) . maxq a a = a : rational

    minq_dist_maxq_l : forall (a b c : rational) .
                          minq (maxq a b) c = maxq (minq a c) (minq b c) : rational

    minq_dist_maxq_r : forall (a b c : rational) .
                          minq a (maxq b c) = maxq (minq a b) (minq a c) : rational

    maxq_dist_minq_l : forall (a b c : rational) .
                          maxq (minq a b) c = minq (maxq a c) (maxq b c) : rational

    maxq_dist_minq_r : forall (a b c : rational) .
                          maxq a (minq b c) = minq (maxq a b) (maxq a c) : rational

    plusq_dist_minq_l : forall (a b c : rational) . minq a b + c = minq (a + c) (b + c) : rational

    plusq_dist_minq_r : forall (a b c : rational) . a + minq b c = minq (a + b) (a + c) : rational

    plusq_dist_maxq_l : forall (a b c : rational) . maxq a b + c = maxq (a + c) (b + c) : rational

    plusq_dist_maxq_r : forall (a b c : rational) . a + maxq b c = maxq (a + b) (a + c) : rational

    minz_to_rational : forall (m n : integer) .
                          integer_to_rational (Integer.minz m n)
                            = minq (integer_to_rational m) (integer_to_rational n)
                            : rational

    maxz_to_rational : forall (m n : integer) .
                          integer_to_rational (Integer.maxz m n)
                            = maxq (integer_to_rational m) (integer_to_rational n)
                            : rational


### Absolute value

    absq : rational -> rational
         = fn a . if 0 <=? a then a else ~ a

    absq_nonneg : forall (a : rational) . 0 <= absq a

    absq_of_nonneg : forall (a : rational) . 0 <= a -> absq a = a : rational

    absq_of_nonpos : forall (a : rational) . a <= 0 -> absq a = ~ a : rational

    absq_ub : forall (x : rational) . x <= absq x

    absq_idem : forall (x : rational) . absq (absq x) = absq x : rational

    absq_negq : forall (a : rational) . absq (~ a) = absq a : rational

    absq_timesq : forall (a b : rational) . absq (a * b) = absq a * absq b : rational

    absq_plusq_leqq : forall (a b : rational) . absq (a + b) <= absq a + absq b

    absq_minusq_leqq : forall (a b : rational) . absq (a - b) <= absq a + absq b

    absz_to_rational : forall (a : integer) .
                          integer_to_rational (Integer.absz a)
                            = absq (integer_to_rational a)
                            : rational

    absq_zero : absq 0 = 0 : rational

    absq_one : absq 1 = 1 : rational

    absq_minus_one : absq -1 = 1 : rational

    absq_minusq_commute : forall (a b : rational) . absq (a - b) = absq (b - a) : rational

    absq_minusq_upper_bound : forall (a b c : rational) . absq (a - b) <= c -> a <= b + c

    absq_minusq_lower_bound : forall (a b c : rational) . absq (a - b) <= c -> b - c <= a

    absq_minusq_absq : forall (a b : rational) . absq (absq a - absq b) <= absq (a - b)


### Floor and Ceiling

    floor : rational -> integer

    ceiling : rational -> integer
            = fn x . ~z (floor (~ x))

    floor_lb : forall (x : rational) . integer_to_rational (floor x) <= x

    floor_glb : forall (x : rational) (y : integer) . integer_to_rational y <= x -> y <z= floor x

    ceiling_ub : forall (x : rational) . x <= integer_to_rational (ceiling x)

    ceiling_lub : forall (x : rational) (y : integer) .
                     x <= integer_to_rational y -> ceiling x <z= y

    floor_mono : forall (x y : rational) . x <= y -> floor x <z= floor y

    ceiling_mono : forall (x y : rational) . x <= y -> ceiling x <z= ceiling y

    floor_integer_to_rational : forall (x : integer) . floor (integer_to_rational x) = x : integer

    ceiling_integer_to_rational : forall (x : integer) .
                                     ceiling (integer_to_rational x) = x : integer

    floor_plus_r : forall (x : rational) (y : integer) .
                      floor (x + integer_to_rational y) = floor x +z y : integer

    floor_plus_l : forall (x : rational) (y : integer) .
                      floor (integer_to_rational y + x) = y +z floor x : integer

    ceiling_plus_r : forall (x : rational) (y : integer) .
                        ceiling (x + integer_to_rational y) = ceiling x +z y : integer

    ceiling_plus_l : forall (x : rational) (y : integer) .
                        ceiling (integer_to_rational y + x) = y +z ceiling x : integer

    floor_mono_lt : forall (x y : rational) . 1 + x <= y -> floor x <z floor y

    ceiling_mono_lt : forall (x y : rational) . 1 + x <= y -> ceiling x <z ceiling y

    floor_negq : forall (x : rational) . floor (~ x) = ~z (ceiling x) : integer

    ceiling_negq : forall (x : rational) . ceiling (~ x) = ~z (floor x) : integer

    floor_nonneg : forall (x : rational) . 0 <= x -> z`0 <z= floor x

    floor_nonpos : forall (x : rational) . x <= 0 -> floor x <z= z`0

    ceiling_nonneg : forall (x : rational) . 0 <= x -> z`0 <z= ceiling x

    ceiling_nonpos : forall (x : rational) . x <= 0 -> ceiling x <z= z`0

    floor_from_bounds : forall (x : integer) (y : rational) .
                           integer_to_rational x <= y
                           -> y < integer_to_rational (z`1 +z x)
                           -> floor y = x : integer

    ceiling_from_bounds : forall (x : integer) (y : rational) .
                             y <= integer_to_rational x
                             -> integer_to_rational (z`-1 +z x) < y
                             -> ceiling y = x : integer

    floor_ceiling_leqz : forall (x : rational) . floor x <z= ceiling x


### Miscellaneous

    rational_dense : forall (a b : rational) . a < b -> exists (c : rational) . a < c & c < b

    leqq_from_upper_bounds : forall (x y : rational) .
                                (forall (z : rational) . y < z -> x <= z) -> x <= y

    rational_total : Partial.total rational

    rational_strict : Partial.strict rational
