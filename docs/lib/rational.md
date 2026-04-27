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

    negq_minusq : forall (x y : rational) . ~q (x -q y) = y -q x : rational

    plusq_compat : forall (x x' y y' : rational) .
                      x = x' : rational -> y = y' : rational -> x +q y = x' +q y' : rational

    minusq_compat : forall (x x' y y' : rational) .
                       x = x' : rational -> y = y' : rational -> x -q y = x' -q y' : rational

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

    negq_dist_plusq : forall (x y : rational) . ~q (x +q y) = ~q x +q ~q y : rational

    negq_dist_timesq_l : forall (x y : rational) . ~q (x *q y) = ~q x *q y : rational

    negq_dist_timesq_r : forall (x y : rational) . ~q (x *q y) = x *q ~q y : rational

    negq_dist_invq : forall (x : rational) . ~q (invq x) = invq (~q x) : rational

    negq_as_timesq : forall (x : rational) . ~q x = q`-1 *q x : rational

    plusq_self : forall (a : rational) . a +q a = q`2 *q a : rational


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

    ltq_implication : forall (x x' y y' : rational) . x' <q= x -> y <q= y' -> x <q y -> x' <q y'

    not_leqq : forall (x y : rational) . not (x <q= y) <-> y <q x

    not_ltq : forall (x y : rational) . not (x <q y) <-> y <q= x

    ltq_from_leqq_neq : forall (x y : rational) . x <q= y -> not (x = y : rational) -> x <q y

    ltq_0_1 : q`0 <q q`1

    neqq_0_1 : q`0 != q`1 : rational

    leqq_0_1 : q`0 <q= q`1

    ltq_neg1_0 : q`-1 <q q`0

    leqq_neg1_0 : q`-1 <q= q`0

    neqq_neg1_0 : q`-1 != q`0 : rational


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

    timesq_cancel_leqq_l_neg : forall (x y z : rational) .
                                  z <q q`0 -> z *q x <q= z *q y -> y <q= x

    timesq_cancel_leqq_r_neg : forall (x y z : rational) .
                                  z <q q`0 -> x *q z <q= y *q z -> y <q= x

    timesq_cancel_ltq_l_neg : forall (x y z : rational) . z <q q`0 -> z *q x <q z *q y -> y <q x

    timesq_cancel_ltq_r_neg : forall (x y z : rational) . z <q q`0 -> x *q z <q y *q z -> y <q x

    timesq_shift_leqq_r : forall (x y z : rational) .
                             q`0 <q y -> x *q y <q= z <-> x <q= z *q invq y

    timesq_shift_leqq_l : forall (x y z : rational) .
                             q`0 <q y -> x <q= y *q z <-> invq y *q x <q= z

    timesq_shift_leqq_lr : forall (x y z : rational) .
                              q`0 <q x -> x *q y <q= z <-> y <q= invq x *q z

    timesq_shift_leqq_rl : forall (x y z : rational) .
                              q`0 <q z -> x <q= y *q z <-> x *q invq z <q= y

    timesq_shift_ltq_r : forall (x y z : rational) . q`0 <q y -> x *q y <q z <-> x <q z *q invq y

    timesq_shift_ltq_l : forall (x y z : rational) . q`0 <q y -> x <q y *q z <-> invq y *q x <q z

    timesq_shift_ltq_lr : forall (x y z : rational) . q`0 <q x -> x *q y <q z <-> y <q invq x *q z

    timesq_shift_ltq_rl : forall (x y z : rational) . q`0 <q z -> x <q y *q z <-> x *q invq z <q y

    timesq_shift_leqq_r_neg : forall (x y z : rational) .
                                 y <q q`0 -> x *q y <q= z <-> z *q invq y <q= x

    timesq_shift_leqq_l_neg : forall (x y z : rational) .
                                 y <q q`0 -> x <q= y *q z <-> z <q= invq y *q x

    timesq_shift_leqq_lr_neg : forall (x y z : rational) .
                                  x <q q`0 -> x *q y <q= z <-> invq x *q z <q= y

    timesq_shift_leqq_rl_neg : forall (x y z : rational) .
                                  z <q q`0 -> x <q= y *q z <-> y <q= x *q invq z

    timesq_shift_ltq_r_neg : forall (x y z : rational) .
                                y <q q`0 -> x *q y <q z <-> z *q invq y <q x

    timesq_shift_ltq_l_neg : forall (x y z : rational) .
                                y <q q`0 -> x <q y *q z <-> z <q invq y *q x

    timesq_shift_ltq_lr_neg : forall (x y z : rational) .
                                 x <q q`0 -> x *q y <q z <-> invq x *q z <q y

    timesq_shift_ltq_rl_neg : forall (x y z : rational) .
                                 z <q q`0 -> x <q y *q z <-> y <q x *q invq z

    invq_positive : forall (x : rational) . q`0 <q x -> q`0 <q invq x

    invq_negative : forall (x : rational) . x <q q`0 -> invq x <q q`0

    invq_leqq_pos : forall (x y : rational) . q`0 <q x -> x <q= y -> invq y <q= invq x

    invq_leqq_neg : forall (x y : rational) . y <q q`0 -> x <q= y -> invq y <q= invq x

    invq_ltq_pos : forall (x y : rational) . q`0 <q x -> x <q y -> invq y <q invq x

    invq_ltq_neg : forall (x y : rational) . y <q q`0 -> x <q y -> invq y <q invq x

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

    invq_leqq_samesign : forall (x y : rational) . samesign x y -> x <q= y -> invq y <q= invq x

    invq_ltq_samesign : forall (x y : rational) . samesign x y -> x <q y -> invq y <q invq x


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

    integer_to_rational_mono_conv : forall (a b : integer) .
                                       integer_to_rational a <q= integer_to_rational b -> a <z= b

    integer_to_rational_mono_lt : forall (a b : integer) .
                                     a <z b -> integer_to_rational a <q integer_to_rational b

    integer_to_rational_mono_lt_conv : forall (a b : integer) .
                                          integer_to_rational a <q integer_to_rational b -> a <z b

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

    nat_to_rational_mono : forall (a b : nat) . a <= b -> nat_to_rational a <q= nat_to_rational b

    integer_nat_to_rational_mono : forall (a : integer) (b : nat) .
                                      a <z= Integer.nat_to_integer b
                                      -> integer_to_rational a <q= nat_to_rational b

    nat_integer_to_rational_mono : forall (a : nat) (b : integer) .
                                      Integer.nat_to_integer a <z= b
                                      -> nat_to_rational a <q= integer_to_rational b

    nat_to_rational_mono_lt : forall (a b : nat) . a < b -> nat_to_rational a <q nat_to_rational b

    integer_nat_to_rational_mono_lt : forall (a : integer) (b : nat) .
                                         a <z Integer.nat_to_integer b
                                         -> integer_to_rational a <q nat_to_rational b

    nat_integer_to_rational_mono_lt : forall (a : nat) (b : integer) .
                                         Integer.nat_to_integer a <z b
                                         -> nat_to_rational a <q integer_to_rational b

    nat_to_rational_nonneg : forall (n : nat) . q`0 <q= nat_to_rational n

    plus_to_rational : forall (a b : nat) .
                          nat_to_rational (a + b)
                            = nat_to_rational a +q nat_to_rational b
                            : rational

    succ_to_rational : forall (a : nat) .
                          nat_to_rational (succ a) = q`1 +q nat_to_rational a : rational

    times_to_rational : forall (a b : nat) .
                           nat_to_rational (a * b)
                             = nat_to_rational a *q nat_to_rational b
                             : rational

    eqb_to_rational : forall (a b : nat) . a =? b = nat_to_rational a =q? nat_to_rational b : bool

    leqb_to_rational : forall (a b : nat) .
                          a <=? b = nat_to_rational a <q=? nat_to_rational b : bool

    ltb_to_rational : forall (a b : nat) . a <? b = nat_to_rational a <q? nat_to_rational b : bool

    neqb_to_rational : forall (a b : nat) .
                          a !=? b = nat_to_rational a !q=? nat_to_rational b : bool


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


### Minimum/Maximum

    minq : rational -> rational -> rational
         = fn a b . if a <q=? b then a else b

    maxq : rational -> rational -> rational
         = fn a b . if a <q=? b then b else a

    negq_minq : forall (a b : rational) . ~q (minq a b) = maxq (~q a) (~q b) : rational

    negq_maxq : forall (a b : rational) . ~q (maxq a b) = minq (~q a) (~q b) : rational

    maxq_as_minq : forall (a b : rational) . maxq a b = ~q (minq (~q a) (~q b)) : rational

    minq_as_maxq : forall (a b : rational) . minq a b = ~q (maxq (~q a) (~q b)) : rational

    minq_commute : forall (a b : rational) . minq a b = minq b a : rational

    maxq_commute : forall (a b : rational) . maxq a b = maxq b a : rational

    minq_assoc : forall (a b c : rational) . minq (minq a b) c = minq a (minq b c) : rational

    maxq_assoc : forall (a b c : rational) . maxq (maxq a b) c = maxq a (maxq b c) : rational

    minq_leq_l : forall (a b : rational) . minq a b <q= a

    minq_leq_r : forall (a b : rational) . minq a b <q= b

    maxq_leq_l : forall (a b : rational) . a <q= maxq a b

    maxq_leq_r : forall (a b : rational) . b <q= maxq a b

    minq_glb : forall (a b c : rational) . c <q= a -> c <q= b -> c <q= minq a b

    maxq_lub : forall (a b c : rational) . a <q= c -> b <q= c -> maxq a b <q= c

    minq_eq_l : forall (a b : rational) . a <q= b -> minq a b = a : rational

    minq_eq_r : forall (a b : rational) . b <q= a -> minq a b = b : rational

    maxq_eq_l : forall (a b : rational) . b <q= a -> maxq a b = a : rational

    maxq_eq_r : forall (a b : rational) . a <q= b -> maxq a b = b : rational

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

    plusq_dist_minq_l : forall (a b c : rational) .
                           minq a b +q c = minq (a +q c) (b +q c) : rational

    plusq_dist_minq_r : forall (a b c : rational) .
                           a +q minq b c = minq (a +q b) (a +q c) : rational

    plusq_dist_maxq_l : forall (a b c : rational) .
                           maxq a b +q c = maxq (a +q c) (b +q c) : rational

    plusq_dist_maxq_r : forall (a b c : rational) .
                           a +q maxq b c = maxq (a +q b) (a +q c) : rational

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
         = fn a . if q`0 <q=? a then a else ~q a

    absq_nonneg : forall (a : rational) . q`0 <q= absq a

    absq_of_nonneg : forall (a : rational) . q`0 <q= a -> absq a = a : rational

    absq_of_nonpos : forall (a : rational) . a <q= q`0 -> absq a = ~q a : rational

    absq_ub : forall (x : rational) . x <q= absq x

    absq_idem : forall (x : rational) . absq (absq x) = absq x : rational

    absq_negq : forall (a : rational) . absq (~q a) = absq a : rational

    absq_timesq : forall (a b : rational) . absq (a *q b) = absq a *q absq b : rational

    absq_plusq_leqq : forall (a b : rational) . absq (a +q b) <q= absq a +q absq b

    absq_minusq_leqq : forall (a b : rational) . absq (a -q b) <q= absq a +q absq b

    absz_to_rational : forall (a : integer) .
                          integer_to_rational (Integer.absz a)
                            = absq (integer_to_rational a)
                            : rational

    absq_zero : absq q`0 = q`0 : rational

    absq_one : absq q`1 = q`1 : rational

    absq_minus_one : absq q`-1 = q`1 : rational

    absq_minusq_commute : forall (a b : rational) . absq (a -q b) = absq (b -q a) : rational

    absq_minusq_upper_bound : forall (a b c : rational) . absq (a -q b) <q= c -> a <q= b +q c

    absq_minusq_lower_bound : forall (a b c : rational) . absq (a -q b) <q= c -> b -q c <q= a

    absq_minusq_absq : forall (a b : rational) . absq (absq a -q absq b) <q= absq (a -q b)


### Floor and Ceiling

    floor : rational -> integer

    ceiling : rational -> integer
            = fn x . ~z (floor (~q x))

    floor_lb : forall (x : rational) . integer_to_rational (floor x) <q= x

    floor_glb : forall (x : rational) (y : integer) . integer_to_rational y <q= x -> y <z= floor x

    ceiling_ub : forall (x : rational) . x <q= integer_to_rational (ceiling x)

    ceiling_lub : forall (x : rational) (y : integer) .
                     x <q= integer_to_rational y -> ceiling x <z= y

    floor_mono : forall (x y : rational) . x <q= y -> floor x <z= floor y

    ceiling_mono : forall (x y : rational) . x <q= y -> ceiling x <z= ceiling y

    floor_integer_to_rational : forall (x : integer) . floor (integer_to_rational x) = x : integer

    ceiling_integer_to_rational : forall (x : integer) .
                                     ceiling (integer_to_rational x) = x : integer

    floor_plus_r : forall (x : rational) (y : integer) .
                      floor (x +q integer_to_rational y) = floor x +z y : integer

    floor_plus_l : forall (x : rational) (y : integer) .
                      floor (integer_to_rational y +q x) = y +z floor x : integer

    ceiling_plus_r : forall (x : rational) (y : integer) .
                        ceiling (x +q integer_to_rational y) = ceiling x +z y : integer

    ceiling_plus_l : forall (x : rational) (y : integer) .
                        ceiling (integer_to_rational y +q x) = y +z ceiling x : integer

    floor_mono_lt : forall (x y : rational) . q`1 +q x <q= y -> floor x <z floor y

    ceiling_mono_lt : forall (x y : rational) . q`1 +q x <q= y -> ceiling x <z ceiling y

    floor_negq : forall (x : rational) . floor (~q x) = ~z (ceiling x) : integer

    ceiling_negq : forall (x : rational) . ceiling (~q x) = ~z (floor x) : integer

    floor_nonneg : forall (x : rational) . q`0 <q= x -> z`0 <z= floor x

    floor_nonpos : forall (x : rational) . x <q= q`0 -> floor x <z= z`0

    ceiling_nonneg : forall (x : rational) . q`0 <q= x -> z`0 <z= ceiling x

    ceiling_nonpos : forall (x : rational) . x <q= q`0 -> ceiling x <z= z`0

    floor_from_bounds : forall (x : integer) (y : rational) .
                           integer_to_rational x <q= y
                           -> y <q integer_to_rational (z`1 +z x)
                           -> floor y = x : integer

    ceiling_from_bounds : forall (x : integer) (y : rational) .
                             y <q= integer_to_rational x
                             -> integer_to_rational (z`-1 +z x) <q y
                             -> ceiling y = x : integer

    floor_ceiling_leqz : forall (x : rational) . floor x <z= ceiling x


### Miscellaneous

    rational_dense : forall (a b : rational) . a <q b -> exists (c : rational) . a <q c & c <q b

    leqq_from_upper_bounds : forall (x y : rational) .
                                (forall (z : rational) . y <q z -> x <q= z) -> x <q= y

    rational_total : Partial.total rational

    rational_strict : Partial.strict rational
