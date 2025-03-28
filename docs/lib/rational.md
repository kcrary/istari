# `Rational`

The type of rationals:

    rational : U 0

Rational literals are written using a `` q` `` parsing directive.  For
example, zero is ``q`0``.


### Plus and negation

    (* +q *)
    plusq : rational -> rational -> rational

    (* ~q *)
    negq : rational -> rational

    (* -q *)
    minusq : rational -> rational -> rational
           = fn x y . x +q ~q y

    plusq_commute : forall (x y : rational) . x +q y = y +q x : rational

    plusq_assoc : forall (x y z : rational) . x +q y +q z = x +q (y +q z) : rational

    plusq_id_l : forall (x : rational) . q`0 +q x = x : rational

    plusq_id_r : forall (x : rational) . x +q q`0 = x : rational

    negq_invol : forall (x : rational) . ~q (~q x) = x : rational

    plusq_inverse_l : forall (x : rational) . ~q x +q x = q`0 : rational

    plusq_inverse_r : forall (x : rational) . x +q ~q x = q`0 : rational

    negq_zero : ~q q`0 = q`0 : rational

    negq_nonzero : forall (x : rational) . x != q`0 : rational -> ~q x != q`0 : rational

    negq_injective : forall (x y : rational) . ~q x = ~q y : rational -> x = y : rational

    negq_plusq : forall (x y : rational) . ~q (x +q y) = ~q x +q ~q y : rational

    plusq_cancel_l : forall (x y z : rational) . z +q x = z +q y : rational -> x = y : rational

    plusq_cancel_r : forall (x y z : rational) . x +q z = y +q z : rational -> x = y : rational

    plusq_shift_l : forall (x y z : rational) . x = y +q z : rational <-> ~q y +q x = z : rational

    plusq_shift_r : forall (x y z : rational) . x +q y = z : rational <-> x = z +q ~q y : rational

    plusq_shift_lr : forall (x y z : rational) .
                        x +q y = z : rational <-> y = ~q x +q z : rational

    plusq_shift_rl : forall (x y z : rational) .
                        x = y +q z : rational <-> x +q ~q z = y : rational

    plusq_compat : forall (x x' y y' : rational) .
                      x = x' : rational -> y = y' : rational -> x +q y = x' +q y' : rational

    negq_compat : forall (x x' : rational) . x = x' : rational -> ~q x = ~q x' : rational


### Times and inverse

    (* *z *)
    timesq : rational -> rational -> rational

To simplify the type of `invq`, we permit division by zero and we set
its result to zero.  Naturally, the divisor usually must be nonzero
for `invq` to have good properties.

    invq : rational -> rational

    (* |q *)
    divq : rational -> rational -> rational
         = fn x y . x *q invq y

    timesq_commute : forall (x y : rational) . x *q y = y *q x : rational

    timesq_assoc : forall (x y z : rational) . x *q y *q z = x *q (y *q z) : rational

    timesq_id_l : forall (x : rational) . q`1 *q x = x : rational

    timesq_id_r : forall (x : rational) . x *q q`1 = x : rational

    timesq_ann_l : forall (x : rational) . q`0 *q x = q`0 : rational

    timesq_ann_r : forall (x : rational) . x *q q`0 = q`0 : rational

    invq_invol : forall (x : rational) . invq (invq x) = x : rational

    timesq_inverse_l : forall (x : rational) . x != q`0 : rational -> invq x *q x = q`1 : rational

    timesq_inverse_r : forall (x : rational) . x != q`0 : rational -> x *q invq x = q`1 : rational

    invq_timesq : forall (x y : rational) . invq (x *q y) = invq x *q invq y : rational

    invq_zero : invq q`0 = q`0 : rational

    invq_nonzero : forall (x : rational) . x != q`0 : rational -> invq x != q`0 : rational

    invq_one : invq q`1 = q`1 : rational

    invq_injective : forall (x y : rational) . invq x = invq y : rational -> x = y : rational

    rational_integral_domain : forall (x y : rational) .
                                  x *q y = q`0 : rational
                                  -> x = q`0 : rational % y = q`0 : rational

    timesq_cancel_l : forall (x y z : rational) .
                         z != q`0 : rational -> z *q x = z *q y : rational -> x = y : rational

    timesq_cancel_r : forall (x y z : rational) .
                         z != q`0 : rational -> x *q z = y *q z : rational -> x = y : rational

    timesq_shift_l : forall (x y z : rational) .
                        y != q`0 : rational -> x = y *q z : rational <-> invq y *q x = z : rational

    timesq_shift_r : forall (x y z : rational) .
                        y != q`0 : rational -> x *q y = z : rational <-> x = z *q invq y : rational

    timesq_shift_lr : forall (x y z : rational) .
                         x != q`0 : rational
                         -> x *q y = z : rational <-> y = invq x *q z : rational

    timesq_shift_rl : forall (x y z : rational) .
                         z != q`0 : rational
                         -> x = y *q z : rational <-> x *q invq z = y : rational

    timesq_compat : forall (x x' y y' : rational) .
                       x = x' : rational -> y = y' : rational -> x *q y = x' *q y' : rational

    invq_compat : forall (x x' : rational) . x = x' : rational -> invq x = invq x' : rational


### Distributivity

    timesq_dist_plusq_l : forall (x y z : rational) . (x +q y) *q z = x *q z +q y *q z : rational

    timesq_dist_plusq_r : forall (x y z : rational) . x *q (y +q z) = x *q y +q x *q z : rational

    negq_dist_timesq_l : forall (x y : rational) . ~q (x *q y) = ~q x *q y : rational

    negq_dist_timesq_r : forall (x y : rational) . ~q (x *q y) = x *q ~q y : rational

    negq_dist_invq : forall (x : rational) . ~q (invq x) = invq (~q x) : rational

    negq_as_timesq : forall (x : rational) . ~q x = q`-1 *q x : rational

### Inequalities

    (* <q= *)
    leqq : rational -> rational -> U 0

    (* <q *)
    ltq : rational -> rational -> U 0

    leqq_inhabitant : forall (x y : rational) . x <q= y -> () : x <q= y

    ltq_inhabitant : forall (x y : rational) . x <q y -> () : x <q y

    leqq_refl : forall (x : rational) . x <q= x

    leqq_refl_eq : forall (x y : rational) . x = y : rational -> x <q= y

    leqq_trans : forall (x y z : rational) . x <q= y -> y <q= z -> x <q= z

    leqq_antisymm : forall (x y : rational) . x <q= y -> y <q= x -> x = y : rational

    ltq_irrefl : forall (x : rational) . x <q x -> void

    leqq_ltq_trans : forall (x y z : rational) . x <q= y -> y <q z -> x <q z

    ltq_leqq_trans : forall (x y z : rational) . x <q y -> y <q= z -> x <q z

    ltq_trans : forall (x y z : rational) . x <q y -> y <q z -> x <q z

    ltq_impl_leqq : forall (x y : rational) . x <q y -> x <q= y

    ltq_impl_neq : forall (x y : rational) . x <q y -> x != y : rational

This one gives transitivity in the form needed for rewriting:

    leqq_implication : forall (x x' y y' : rational) .
                          x' <q= x -> y <q= y' -> x <q= y -> x' <q= y'

    not_leqq : forall (x y : rational) . not (x <q= y) <-> y <q x

    not_ltq : forall (x y : rational) . not (x <q y) <-> y <q= x

    ltq_from_leqq_neq : forall (x y : rational) . x <q= y -> not (x = y : rational) -> x <q y

    ltq_0_1 : q`0 <q q`1

    neqq_0_1 : q`0 != q`1 : rational

    leqq_0_1 : q`0 <q= q`1


### Plus and negation inequality

    plusq_leqq : forall (x x' y y' : rational) . x <q= x' -> y <q= y' -> x +q y <q= x' +q y'

    plusq_ltq_l : forall (x x' y y' : rational) . x <q x' -> y <q= y' -> x +q y <q x' +q y'

    plusq_ltq_r : forall (x x' y y' : rational) . x <q= x' -> y <q y' -> x +q y <q x' +q y'

    plusq_ltq : forall (x x' y y' : rational) . x <q x' -> y <q y' -> x +q y <q x' +q y'

    plusq_cancel_leqq_l : forall (x y z : rational) . z +q x <q= z +q y -> x <q= y

    plusq_cancel_leqq_r : forall (x y z : rational) . x +q z <q= y +q z -> x <q= y

    plusq_cancel_leqq_leqq_l : forall (x x' y y' : rational) .
                                  x +q y <q= x' +q y' -> x' <q= x -> y <q= y'

    plusq_cancel_leqq_leqq_r : forall (x x' y y' : rational) .
                                  x +q y <q= x' +q y' -> y' <q= y -> x <q= x'

    plusq_shift_leqq_l : forall (x y z : rational) . x <q= y +q z <-> ~q y +q x <q= z

    plusq_shift_leqq_r : forall (x y z : rational) . x +q y <q= z <-> x <q= z +q ~q y

    plusq_shift_leqq_lr : forall (x y z : rational) . x +q y <q= z <-> y <q= ~q x +q z

    plusq_shift_leqq_rl : forall (x y z : rational) . x <q= y +q z <-> x +q ~q z <q= y

    plusq_cancel_ltq_l : forall (x y z : rational) . z +q x <q z +q y -> x <q y

    plusq_cancel_ltq_r : forall (x y z : rational) . x +q z <q y +q z -> x <q y

    plusq_shift_ltq_l : forall (x y z : rational) . x <q y +q z <-> ~q y +q x <q z

    plusq_shift_ltq_r : forall (x y z : rational) . x +q y <q z <-> x <q z +q ~q y

    plusq_shift_ltq_lr : forall (x y z : rational) . x +q y <q z <-> y <q ~q x +q z

    plusq_shift_ltq_rl : forall (x y z : rational) . x <q y +q z <-> x +q ~q z <q y

    negq_leqq : forall (x y : rational) . x <q= y -> ~q y <q= ~q x

    negq_leqq' : forall (x y : rational) . ~q y <q= ~q x -> x <q= y

    negq_ltq : forall (x y : rational) . x <q y -> ~q y <q ~q x

    negq_ltq' : forall (x y : rational) . ~q y <q ~q x -> x <q y


### Times and inverse inequality

    timesq_leqq : forall (x x' y y' : rational) .
                     q`0 <q= x -> q`0 <q= y -> x <q= x' -> y <q= y' -> x *q y <q= x' *q y'

    (* an alias for timesq_leqq *)
    timesq_leqq_pos_pos : forall (x x' y y' : rational) .
                             q`0 <q= x -> q`0 <q= y -> x <q= x' -> y <q= y' -> x *q y <q= x' *q y'

    timesq_leqq_neg_neg : forall (x x' y y' : rational) .
                             x' <q= q`0
                             -> y' <q= q`0
                             -> x <q= x'
                             -> y <q= y'
                             -> x' *q y' <q= x *q y

    timesq_leqq_pos_neg : forall (x x' y y' : rational) .
                             q`0 <q= x -> y' <q= q`0 -> x <q= x' -> y <q= y' -> x' *q y <q= x *q y'

    timesq_leqq_neg_neg : forall (x x' y y' : rational) .
                             x' <q= q`0
                             -> y' <q= q`0
                             -> x <q= x'
                             -> y <q= y'
                             -> x' *q y' <q= x *q y

    timesq_leqq_zero : forall (x y : rational) . q`0 <q= x -> q`0 <q= y -> q`0 <q= x *q y

    (* an alias for timesq_leqq_zero *)
    timesq_leqq_zero_pos_pos : forall (x y : rational) . q`0 <q= x -> q`0 <q= y -> q`0 <q= x *q y

    timesq_leqq_zero_pos_neg : forall (x y : rational) . q`0 <q= x -> y <q= q`0 -> x *q y <q= q`0

    timesq_leqq_zero_neg_pos : forall (x y : rational) . x <q= q`0 -> q`0 <q= y -> x *q y <q= q`0

    timesq_leqq_zero_neg_neg : forall (x y : rational) . x <q= q`0 -> y <q= q`0 -> q`0 <q= x *q y

    timesq_leqq_l : forall (x y y' : rational) . q`0 <q= x -> y <q= y' -> x *q y <q= x *q y'

    timesq_leqq_r : forall (x x' y : rational) . x <q= x' -> q`0 <q= y -> x *q y <q= x' *q y

    timesq_leqq_l_neg : forall (x y y' : rational) . x <q= q`0 -> y <q= y' -> x *q y' <q= x *q y

    timesq_leqq_r_neg : forall (x x' y : rational) . x <q= x' -> y <q= q`0 -> x' *q y <q= x *q y

    timesq_ltq_l : forall (x y y' : rational) . q`0 <q x -> y <q y' -> x *q y <q x *q y'

    timesq_ltq_r : forall (x x' y : rational) . q`0 <q y -> x <q x' -> x *q y <q x' *q y

    timesq_ltq_l_neg : forall (x y y' : rational) . x <q q`0 -> y <q y' -> x *q y' <q x *q y

    timesq_ltq_r_neg : forall (x x' y : rational) . x <q x' -> y <q q`0 -> x' *q y <q x *q y

    timesq_ltq_zero : forall (x y : rational) . q`0 <q x -> q`0 <q y -> q`0 <q x *q y

    (* an alias for timesq_ltq_zero *)
    timesq_ltq_zero_pos_pos : forall (x y : rational) . q`0 <q x -> q`0 <q y -> q`0 <q x *q y

    timesq_ltq_zero_pos_neg : forall (x y : rational) . q`0 <q x -> y <q q`0 -> x *q y <q q`0

    timesq_ltq_zero_neg_pos : forall (x y : rational) . x <q q`0 -> q`0 <q y -> x *q y <q q`0

    timesq_ltq_zero_neg_neg : forall (x y : rational) . x <q q`0 -> y <q q`0 -> q`0 <q x *q y

    timesq_neq_zero : forall (x y : rational) .
                         x != q`0 : rational -> y != q`0 : rational -> x *q y != q`0 : rational

    timesq_ltq_zero_invert : forall (x y : rational) .
                                q`0 <q x *q y -> x <q q`0 & y <q q`0 % q`0 <q x & q`0 <q y

    timesq_ltq_zero_invert_neg : forall (x y : rational) .
                                    x *q y <q q`0 -> x <q q`0 & q`0 <q y % q`0 <q x & y <q q`0

    timesq_cancel_leqq_l : forall (x y z : rational) . q`0 <q z -> z *q x <q= z *q y -> x <q= y

    timesq_cancel_leqq_r : forall (x y z : rational) . q`0 <q z -> x *q z <q= y *q z -> x <q= y

    timesq_cancel_ltq_l : forall (x y z : rational) . q`0 <q z -> z *q x <q z *q y -> x <q y

    timesq_cancel_ltq_r : forall (x y z : rational) . q`0 <q z -> x *q z <q y *q z -> x <q y

    invq_positive : forall (x : rational) . q`0 <q x -> q`0 <q invq x

    invq_negative : forall (x : rational) . x <q q`0 -> invq x <q q`0

    invq_leqq_pos : forall (x y : rational) . q`0 <q x -> x <q= y -> invq y <q= invq x

    invq_leqq_neg : forall (x y : rational) . y <q q`0 -> x <q= y -> invq y <q= invq x

    invq_ltq_pos : forall (x y : rational) . q`0 <q x -> x <q y -> invq y <q invq x

    invq_ltq_neg : forall (x y : rational) . y <q q`0 -> x <q y -> invq y <q invq x


### Relation to integers

    integer_to_rational : integer -> rational

    integer_to_rational_injective : forall (a b : integer) .
                                       integer_to_rational a = integer_to_rational b : rational
                                       -> a = b : integer

    integer_to_rational_neq : forall (a b : integer) .
                                 a != b : integer
                                 -> integer_to_rational a != integer_to_rational b : rational

    integer_to_rational_mono : forall (a b : integer) .
                                  a <z= b -> integer_to_rational a <q= integer_to_rational b

    integer_to_rational_mono_lt : forall (a b : integer) .
                                     a <z b -> integer_to_rational a <q integer_to_rational b

    plusz_to_rational : forall (a b : integer) .
                           integer_to_rational (a +z b)
                             = integer_to_rational a +q integer_to_rational b
                             : rational

    negz_to_rational : forall (a : integer) .
                          integer_to_rational (~z a) = ~q (integer_to_rational a) : rational

    minusz_to_rational : forall (a b : integer) .
                            integer_to_rational (a -z b)
                              = integer_to_rational a -q integer_to_rational b
                              : rational

    timesz_to_rational : forall (a b : integer) .
                            integer_to_rational (a *z b)
                              = integer_to_rational a *q integer_to_rational b
                              : rational

    eqzb_to_rational : forall (a b : integer) .
                          a =z? b = integer_to_rational a =q? integer_to_rational b : bool

    neqzb_to_rational : forall (a b : integer) .
                           a !z=? b = integer_to_rational a !q=? integer_to_rational b : bool

    leqzb_to_rational : forall (a b : integer) .
                           a <z=? b = integer_to_rational a <q=? integer_to_rational b : bool

    ltzb_to_rational : forall (a b : integer) .
                          a <z? b = integer_to_rational a <q? integer_to_rational b : bool


### Effective comparisons

    (* =q? *)
    eqqb : rational -> rational -> bool

    (* <q=? *)
    leqqb : rational -> rational -> bool

    (* <q? *)
    ltqb : rational -> rational -> bool

    (* !q=? *)
    neqqb : rational -> rational -> bool

    notb_eqqb : forall (x y : rational) . Bool.notb (x =q? y) = x !q=? y : bool

    notb_neqqb : forall (x y : rational) . Bool.notb (x !q=? y) = x =q? y : bool

    notb_leqqb : forall (x y : rational) . Bool.notb (x <q=? y) = y <q? x : bool

    notb_ltqb : forall (x y : rational) . Bool.notb (x <q? y) = y <q=? x : bool

    istrue_eqqb : forall (x y : rational) . Bool.istrue (x =q? y) <-> x = y : rational

    istrue_neqqb : forall (x y : rational) . Bool.istrue (x !q=? y) <-> x != y : rational

    istrue_leqqb : forall (x y : rational) . Bool.istrue (x <q=? y) <-> x <q= y

    istrue_ltqb : forall (x y : rational) . Bool.istrue (x <q? y) <-> x <q y


### Decidability

    eq_rational_decide : forall (x y : rational) . Decidable.decidable (x = y : rational)

    neq_rational_decide : forall (x y : rational) . Decidable.decidable (x != y : rational)

    leqq_decide : forall (x y : rational) . Decidable.decidable (x <q= y)

    ltq_decide : forall (x y : rational) . Decidable.decidable (x <q y)

    eq_rational_stable : forall (x y : rational) . Stable.stable (x = y : rational)

    neq_rational_stable : forall (x y : rational) . Stable.stable (x != y : rational)

    leqq_stable : forall (x y : rational) . Stable.stable (x <q= y)

    ltq_stable : forall (x y : rational) . Stable.stable (x <q y)

    leqq_iff_ltq_or_eq : forall (x y : rational) . x <q= y <-> x <q y % x = y : rational

    rational_trichotomy : forall (x y : rational) . x <q y % x = y : rational % y <q x

    rational_dichotomy : forall (x y : rational) . x <q= y % y <q x

    rational_dichotomy_weak : forall (x y : rational) . x <q= y % y <q= x

    rational_dichotomy_neq : forall (x y : rational) . x != y : rational -> x <q y % y <q x


### Miscellaneous

    rational_total : Partial.total rational

    rational_strict : rational <: partial rational
