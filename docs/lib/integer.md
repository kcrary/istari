# `Integer`

Expressions in this file are rendered using the `integer` [overloading
mode](../overloading.html).

The `integer` type is primitive but aliased in the `Integer` module:

    integer : U 0


### Plus and negation

    (* +z *)
    plusz : integer -> integer -> integer

    (* ~z *)
    negz : integer -> integer

    (* -z *)
    minusz : integer -> integer -> integer
           = fn x y . x + ~ y

    neq_0_1 : 0 = 1 : integer -> void

    neq_0_neg1 : 0 = -1 : integer -> void

    plusz_commute : forall (a b : integer) . a + b = b + a : integer

    plusz_assoc : forall (a b c : integer) . a + b + c = a + (b + c) : integer

    minusz_assoc : forall (a b c : integer) . a - b - c = a - (b + c) : integer

    plusz_minusz_assoc : forall (a b c : integer) . a + b - c = a + (b - c) : integer

    minusz_plusz_assoc : forall (a b c : integer) . a - b + c = a - (b - c) : integer

    plusz_id_l : forall (a : integer) . 0 + a = a : integer

    plusz_id_r : forall (a : integer) . a + 0 = a : integer

    minusz_id_l : forall (a : integer) . 0 - a = ~ a : integer

    minusz_id_r : forall (a : integer) . a - 0 = a : integer

    plusz_inverse_l : forall (a : integer) . ~ a + a = 0 : integer

    plusz_inverse_r : forall (a : integer) . a + ~ a = 0 : integer

    minusz_self : forall (a : integer) . a - a = 0 : integer

    negz_invol : forall (a : integer) . ~ (~ a) = a : integer

    negz_plusz : forall (a b : integer) . ~ (a + b) = ~ a + ~ b : integer

    negz_minusz : forall (a b : integer) . ~ (a - b) = b - a : integer

    plusz_commute3 : forall (a b c : integer) . a + b + c = a + c + b : integer

    plusz_rotate : forall (a b c : integer) . a + b + c = c + a + b : integer

    plusz_rotate4 : forall (a b c d : integer) . a + b + c + d = a + d + b + c : integer

    plusz_cancel_l : forall (a b c : integer) . c + a = c + b : integer -> a = b : integer

    plusz_cancel_r : forall (a b c : integer) . a + c = b + c : integer -> a = b : integer

In each of the `plusz` shift lemmas, the negation term is on the right
of the `<->`.  Then the first letter indicates which direction the
negated term is moving, the second indicates which operand it is
before moving, and the third is which operand it is after moving.

    plusz_shift_lll : forall (a b c : integer) . a = b + c : integer <-> ~ b + a = c : integer

    plusz_shift_lrr : forall (a b c : integer) . a = b + c : integer <-> a + ~ c = b : integer

    plusz_shift_llr : forall (a b c : integer) . a = b + c : integer <-> a + ~ b = c : integer

    plusz_shift_lrl : forall (a b c : integer) . a = b + c : integer <-> ~ c + a = b : integer

    plusz_shift_rrr : forall (a b c : integer) . a + b = c : integer <-> a = c + ~ b : integer

    plusz_shift_rll : forall (a b c : integer) . a + b = c : integer <-> b = ~ a + c : integer

    plusz_shift_rlr : forall (a b c : integer) . a + b = c : integer <-> b = c + ~ a : integer

    plusz_shift_rrl : forall (a b c : integer) . a + b = c : integer <-> a = ~ b + c : integer

    minusz_cancel_r : forall (a b c : integer) . a - c = b - c : integer -> a = b : integer

    minusz_cancel_l : forall (a b c : integer) . c - a = c - b : integer -> a = b : integer

In each of the `minusz` shift lemmas, the subtraction term is on the
right of the `<->`.  Then the first letter indicates which direction
the subtrahend is moving, the second indicates which operand it is
before moving.  It is always the right-hand operand after moving.

    minusz_shift_ll : forall (a b c : integer) . a = b + c : integer <-> a - b = c : integer

    minusz_shift_lr : forall (a b c : integer) . a = b + c : integer <-> a - c = b : integer

    minusz_shift_rr : forall (a b c : integer) . a + b = c : integer <-> a = c - b : integer

    minusz_shift_rl : forall (a b c : integer) . a + b = c : integer <-> b = c - a : integer

    plusz_compat : forall (a a' b b' : integer) .
                      a = a' : integer -> b = b' : integer -> a + b = a' + b' : integer

    negz_compat : forall (a a' : integer) . a = a' : integer -> ~ a = ~ a' : integer

    negz_injective : forall (a b : integer) . ~ a = ~ b : integer -> a = b : integer

    minusz_compat : forall (a a' b b' : integer) .
                       a = a' : integer -> b = b' : integer -> a - b = a' - b' : integer


### Inequalities

    (* <z= *)
    leqz : integer -> integer -> U 0

    (* <z *)
    ltz : integer -> integer -> U 0
        = fn x y . 1 + x <= y

    leqz_inhabitant : forall (a b : integer) . a <= b -> () : a <= b

    ltz_inhabitant : forall (a b : integer) . a < b -> () : a < b

    leqz_0_1 : 0 <= 1

    ltz_0_1 : 0 < 1

    leqz_neg1_0 : -1 <= 0

    ltz_neg1_0 : -1 < 0

    leqz_refl : forall (a : integer) . a <= a

    leqz_refl_eq : forall (a b : integer) . a = b : integer -> a <= b

    leqz_trans : forall (a b c : integer) . a <= b -> b <= c -> a <= c

    leqz_antisymm : forall (a b : integer) . a <= b -> b <= a -> a = b : integer

This one gives transitivity in the form needed for rewriting:

    leqz_implication : forall (a a' b b' : integer) . a' <= a -> b <= b' -> a <= b -> a' <= b'

    ltz_impl_leqz : forall (a b : integer) . a < b -> a <= b

    ltz_impl_neq : forall (a b : integer) . a < b -> a != b : integer

    ltz_irrefl : forall (a : integer) . a < a -> void

    ltz_trans : forall (a b c : integer) . a < b -> b < c -> a < c

    leqz_ltz_trans : forall (a b c : integer) . a <= b -> b < c -> a < c

    ltz_leqz_trans : forall (a b c : integer) . a < b -> b <= c -> a < c

    ltz_succ : forall (a : integer) . a < 1 + a

    leqz_succ : forall (a : integer) . a <= 1 + a

    plusz_leqz : forall (a a' b b' : integer) . a <= a' -> b <= b' -> a + b <= a' + b'

    plusz_cancel_leqz_l : forall (a b c : integer) . c + a <= c + b -> a <= b

    plusz_cancel_leqz_r : forall (a b c : integer) . a + c <= b + c -> a <= b

    plusz_cancel_leqz_leqz_l : forall (a a' b b' : integer) .
                                  a + b <= a' + b' -> a' <= a -> b <= b'

    plusz_cancel_leqz_leqz_r : forall (a a' b b' : integer) .
                                  a + b <= a' + b' -> b' <= b -> a <= a'

    plusz_shift_leqz_lll : forall (a b c : integer) . a <= b + c <-> ~ b + a <= c

    plusz_shift_leqz_lrr : forall (a b c : integer) . a <= b + c <-> a + ~ c <= b

    plusz_shift_leqz_llr : forall (a b c : integer) . a <= b + c <-> a + ~ b <= c

    plusz_shift_leqz_lrl : forall (a b c : integer) . a <= b + c <-> ~ c + a <= b

    plusz_shift_leqz_rrr : forall (a b c : integer) . a + b <= c <-> a <= c + ~ b

    plusz_shift_leqz_rll : forall (a b c : integer) . a + b <= c <-> b <= ~ a + c

    plusz_shift_leqz_rlr : forall (a b c : integer) . a + b <= c <-> b <= c + ~ a

    plusz_shift_leqz_rrl : forall (a b c : integer) . a + b <= c <-> a <= ~ b + c

    plusz_ltz_l : forall (a a' b b' : integer) . a < a' -> b <= b' -> a + b < a' + b'

    plusz_ltz_r : forall (a a' b b' : integer) . a <= a' -> b < b' -> a + b < a' + b'

    plusz_ltz : forall (a a' b b' : integer) . a < a' -> b < b' -> a + b < a' + b'

    plusz_cancel_ltz_l : forall (a b c : integer) . c + a < c + b -> a < b

    plusz_cancel_ltz_r : forall (a b c : integer) . a + c < b + c -> a < b

    plusz_shift_ltz_lll : forall (a b c : integer) . a < b + c <-> ~ b + a < c

    plusz_shift_ltz_lrr : forall (a b c : integer) . a < b + c <-> a + ~ c < b

    plusz_shift_ltz_llr : forall (a b c : integer) . a < b + c <-> a + ~ b < c

    plusz_shift_ltz_lrl : forall (a b c : integer) . a < b + c <-> ~ c + a < b

    plusz_shift_ltz_rrr : forall (a b c : integer) . a + b < c <-> a < c + ~ b

    plusz_shift_ltz_rll : forall (a b c : integer) . a + b < c <-> b < ~ a + c

    plusz_shift_ltz_rlr : forall (a b c : integer) . a + b < c <-> b < c + ~ a

    plusz_shift_ltz_rrl : forall (a b c : integer) . a + b < c <-> a < ~ b + c

    negz_leqz : forall (a b : integer) . a <= b -> ~ b <= ~ a

    negz_leqz' : forall (a b : integer) . ~ b <= ~ a -> a <= b

    negz_ltz : forall (a b : integer) . a < b -> ~ b < ~ a

    negz_ltz' : forall (a b : integer) . ~ b < ~ a -> a < b

    minusz_leqz : forall (a a' b b' : integer) . a <= a' -> b' <= b -> a - b <= a' - b'

    minusz_cancel_leqz_l : forall (a b c : integer) . c - a <= c - b -> b <= a

    minusz_cancel_leqz_r : forall (a b c : integer) . a - c <= b - c -> a <= b

    minusz_cancel_ltz_l : forall (a b c : integer) . c - a < c - b -> b < a

    minusz_cancel_ltz_r : forall (a b c : integer) . a - c < b - c -> a < b

    minusz_shift_leqz_ll : forall (a b c : integer) . a <= b + c <-> a - b <= c

    minusz_shift_leqz_lr : forall (a b c : integer) . a <= b + c <-> a - c <= b

    minusz_shift_leqz_rr : forall (a b c : integer) . a + b <= c <-> a <= c - b

    minusz_shift_leqz_rl : forall (a b c : integer) . a + b <= c <-> b <= c - a

    minusz_shift_ltz_ll : forall (a b c : integer) . a < b + c <-> a - b < c

    minusz_shift_ltz_lr : forall (a b c : integer) . a < b + c <-> a - c < b

    minusz_shift_ltz_rr : forall (a b c : integer) . a + b < c <-> a < c - b

    minusz_shift_ltz_rl : forall (a b c : integer) . a + b < c <-> b < c - a

    not_leqz : forall (a b : integer) . not (a <= b) <-> b < a

    not_ltz : forall (a b : integer) . not (a < b) <-> b <= a

    ltz_from_leqz_neq : forall (a b : integer) . a <= b -> not (a = b : integer) -> a < b

    ltz_as_leqz_l : forall (a b : integer) . a < b <-> 1 + a <= b

    ltz_as_leqz_r : forall (a b : integer) . a < b <-> a + 1 <= b

    leqz_as_ltz_l : forall (a b : integer) . a <= b <-> a < 1 + b

    leqz_as_ltz_r : forall (a b : integer) . a <= b <-> a < b + 1



### Effective comparisons

    (* =z? *)
    eqzb : integer -> integer -> bool

    (* <z=? *)
    leqzb : integer -> integer -> bool

    (* <z? *)
    ltzb : integer -> integer -> bool
         = fn x y . 1 + x <=? y

    (* !z=? *)
    neqzb : integer -> integer -> bool
          = fn a b . Bool.notb (a =? b)

    istrue_eqzb : forall (a b : integer) . Bool.istrue (a =? b) <-> a = b : integer

    istrue_neqzb : forall (a b : integer) . Bool.istrue (a !=? b) <-> a != b : integer

    istrue_leqzb : forall (a b : integer) . Bool.istrue (a <=? b) <-> a <= b

    istrue_ltzb : forall (a b : integer) . Bool.istrue (a <? b) <-> a < b

    notb_eqzb : forall (a b : integer) . Bool.notb (a =? b) = a !=? b : bool

    notb_neqzb : forall (a b : integer) . Bool.notb (a !=? b) = a =? b : bool

    notb_leqzb : forall (a b : integer) . Bool.notb (a <=? b) = b <? a : bool

    notb_ltzb : forall (a b : integer) . Bool.notb (a <? b) = b <=? a : bool


### Induction

We say that `a` is smaller than `b` when `b` < `a` &le; 0 or 0 &le; `a` < `b`:

    smaller : integer -> integer -> U 0
            = fn a b . b < a & a <= 0 % a < b & 0 <= a


Smaller is well-founded, giving us strong induction for integers:

    smaller_well_founded : forall (a : integer) . Acc.Acc integer smaller a


As a corollary, we can build an iterator for integers.  It has three
cases: a base case for zero, a negative case that works downwards, and a
positive case that works upwards.

    integer_iter : intersect (i : level) .
                      forall (P : integer -> U i) .
                        P 0
                        -> (forall (a : integer) . a <= 0 -> P a -> P (-1 + a))
                        -> (forall (a : integer) . 0 <= a -> P a -> P (1 + a))
                        -> forall (a : integer) . P a
                 =rec= fn P hz hm hp a .
                          if 0 =? a
                          then hz
                          else (if 0 <=? a
                                then hp (-1 + a) () (integer_iter P hz hm hp (-1 + a))
                                else hm (1 + a) () (integer_iter P hz hm hp (1 + a)))


### Relation to natural numbers

    nat_to_integer : nat -> integer
                   =rec= fn n . nat_case n 0 (fn n' . 1 + nat_to_integer n')

    nat_to_integer (zero) --> z`0
    nat_to_integer (succ n) --> plusz z`1 (nat_to_integer n)

    integer_to_nat : integer -> nat
                   =rec= fn x . if x <=? 0 then n`0 else succ (integer_to_nat (-1 + x))

    nat_to_integer_inv : forall (n : nat) . integer_to_nat (nat_to_integer n) = n : nat

    integer_to_nat_inv : forall (a : integer) .
                            0 <= a -> nat_to_integer (integer_to_nat a) = a : integer

    nat_to_integer_injective : forall (m n : nat) .
                                  nat_to_integer m = nat_to_integer n : integer -> m = n : nat

    nat_to_integer_nonneg : forall (n : nat) . 0 <= nat_to_integer n

    nat_to_integer_mono : forall (m n : nat) . m <n= n -> nat_to_integer m <= nat_to_integer n

    nat_to_integer_mono_lt : forall (m n : nat) . m <n n -> nat_to_integer m < nat_to_integer n

    integer_to_nat_zero : integer_to_nat 0 = n`0 : nat

    integer_to_nat_succ : forall (a : integer) .
                             0 <= a -> integer_to_nat (1 + a) = succ (integer_to_nat a) : nat

    integer_to_nat_mono : forall (a b : integer) . a <= b -> integer_to_nat a <n= integer_to_nat b

    integer_to_nat_mono_lt : forall (a b : integer) .
                                0 <= a -> a < b -> integer_to_nat a <n integer_to_nat b

    succ_to_integer : forall (n : nat) . nat_to_integer (succ n) = 1 + nat_to_integer n : integer

    plus_to_integer : forall (m n : nat) .
                         nat_to_integer (m +n n) = nat_to_integer m + nat_to_integer n : integer

    plusz_to_nat : forall (a b : integer) .
                      0 <= a
                      -> 0 <= b
                      -> integer_to_nat (a + b) = integer_to_nat a +n integer_to_nat b : nat

    pred_to_integer : forall (n : nat) .
                         n`0 <n n -> nat_to_integer (Nat.pred n) = -1 + nat_to_integer n : integer

    minus_to_integer : forall (m n : nat) .
                          n <n= m
                          -> nat_to_integer (m -n n)
                               = nat_to_integer m - nat_to_integer n
                               : integer

    minusz_to_nat : forall (a b : integer) .
                       0 <= b
                       -> b <= a
                       -> integer_to_nat (a - b) = integer_to_nat a -n integer_to_nat b : nat

    eqb_to_integer : forall (m n : nat) . m =n? n = nat_to_integer m =? nat_to_integer n : bool

    eqzb_to_nat : forall (a b : integer) .
                     0 <= a -> 0 <= b -> a =? b = integer_to_nat a =n? integer_to_nat b : bool

    leqb_to_integer : forall (m n : nat) . m <n=? n = nat_to_integer m <=? nat_to_integer n : bool

    leqzb_to_nat : forall (a b : integer) .
                      0 <= a -> 0 <= b -> a <=? b = integer_to_nat a <n=? integer_to_nat b : bool

    ltb_to_integer : forall (m n : nat) . m <n? n = nat_to_integer m <? nat_to_integer n : bool

    ltzb_to_nat : forall (a b : integer) .
                     0 <= a -> 0 <= b -> a <? b = integer_to_nat a <n? integer_to_nat b : bool

    neqb_to_integer : forall (m n : nat) . m !n=? n = nat_to_integer m !=? nat_to_integer n : bool

    neqzb_to_nat : forall (a b : integer) .
                      0 <= a -> 0 <= b -> a !=? b = integer_to_nat a !n=? integer_to_nat b : bool


### Decidability

    eq_integer_decide : forall (a b : integer) . Decidable.decidable (a = b : integer)

    neq_integer_decide : forall (a b : integer) . Decidable.decidable (a != b : integer)

    leqz_decide : forall (a b : integer) . Decidable.decidable (a <= b)

    ltz_decide : forall (a b : integer) . Decidable.decidable (a < b)

    eq_integer_stable : forall (a b : integer) . Stable.stable (a = b : integer)

    neq_integer_stable : forall (a b : integer) . Stable.stable (a != b : integer)

    leqz_stable : forall (a b : integer) . Stable.stable (a <= b)

    ltz_stable : forall (a b : integer) . Stable.stable (a < b)

    leqz_iff_ltz_or_eq : forall (a b : integer) . a <= b <-> a < b % a = b : integer

    integer_trichotomy : forall (a b : integer) . a < b % a = b : integer % b < a

    integer_dichotomy : forall (a b : integer) . a <= b % b < a

    integer_dichotomy_weak : forall (a b : integer) . a <= b % b <= a

    integer_dichotomy_neq : forall (a b : integer) . a != b : integer -> a < b % b < a


### Multiplication

    (* *z *)
    timesz : integer -> integer -> integer

    timesz_id_l : forall (a : integer) . 1 * a = a : integer

    timesz_id_r : forall (a : integer) . a * 1 = a : integer

    timesz_ann_l : forall (a : integer) . 0 * a = 0 : integer

    timesz_ann_r : forall (a : integer) . a * 0 = 0 : integer

    timesz_commute : forall (a b : integer) . a * b = b * a : integer

    timesz_assoc : forall (a b c : integer) . a * b * c = a * (b * c) : integer

    timesz_dist_plusz_l : forall (a b c : integer) . (a + b) * c = a * c + b * c : integer

    timesz_dist_plusz_r : forall (a b c : integer) . a * (b + c) = a * b + a * c : integer

    negz_dist_timesz_l : forall (a b : integer) . ~ (a * b) = ~ a * b : integer

    negz_dist_timesz_r : forall (a b : integer) . ~ (a * b) = a * ~ b : integer

    timesz_dist_minusz_l : forall (a b c : integer) . (a - b) * c = a * c - b * c : integer

    timesz_dist_minusz_r : forall (a b c : integer) . a * (b - c) = a * b - a * c : integer

    negz_as_timesz : forall (a : integer) . ~ a = -1 * a : integer

    timesz_compat : forall (a a' b b' : integer) .
                       a = a' : integer -> b = b' : integer -> a * b = a' * b' : integer

    timesz_commute3 : forall (a b c : integer) . a * b * c = a * c * b : integer

    timesz_rotate : forall (a b c : integer) . a * b * c = c * a * b : integer

    timesz_rotate4 : forall (a b c d : integer) . a * b * c * d = a * d * b * c : integer

    timesz_leqz : forall (a a' b b' : integer) .
                     0 <= a -> 0 <= b -> a <= a' -> b <= b' -> a * b <= a' * b'

    (* an alias for timesz_leqz *)
    timesz_leqz_pos_pos : forall (a a' b b' : integer) .
                             0 <= a -> 0 <= b -> a <= a' -> b <= b' -> a * b <= a' * b'

    timesz_leqz_neg_neg : forall (a a' b b' : integer) .
                             a' <= 0 -> b' <= 0 -> a <= a' -> b <= b' -> a' * b' <= a * b

    timesz_leqz_pos_neg : forall (a a' b b' : integer) .
                             0 <= a -> b' <= 0 -> a <= a' -> b <= b' -> a' * b <= a * b'

    timesz_leqz_neg_pos : forall (a a' b b' : integer) .
                             a' <= 0 -> 0 <= b -> a <= a' -> b <= b' -> a * b' <= a' * b

    timesz_leqz_l : forall (a b b' : integer) . 0 <= a -> b <= b' -> a * b <= a * b'

    timesz_leqz_r : forall (a a' b : integer) . 0 <= b -> a <= a' -> a * b <= a' * b

    timesz_leqz_l_neg : forall (a b b' : integer) . a <= 0 -> b <= b' -> a * b' <= a * b

    timesz_leqz_r_neg : forall (a a' b : integer) . b <= 0 -> a <= a' -> a' * b <= a * b

    timesz_leqz_zero : forall (a b : integer) . 0 <= a -> 0 <= b -> 0 <= a * b

    (* an alias for timesz_leqz_zero *)
    timesz_leqz_zero_pos_pos : forall (a b : integer) . 0 <= a -> 0 <= b -> 0 <= a * b

    timesz_leqz_zero_pos_neg : forall (a b : integer) . 0 <= a -> b <= 0 -> a * b <= 0

    timesz_leqz_zero_neg_pos : forall (a b : integer) . a <= 0 -> 0 <= b -> a * b <= 0

    timesz_leqz_zero_neg_neg : forall (a b : integer) . a <= 0 -> b <= 0 -> 0 <= a * b

    timesz_ltz_zero : forall (a b : integer) . 0 < a -> 0 < b -> 0 < a * b

    (* an alias for timesz_ltz_zero *)
    timesz_ltz_zero_pos_pos : forall (a b : integer) . 0 < a -> 0 < b -> 0 < a * b

    timesz_ltz_zero_pos_neg : forall (a b : integer) . 0 < a -> b < 0 -> a * b < 0

    timesz_ltz_zero_neg_pos : forall (a b : integer) . a < 0 -> 0 < b -> a * b < 0

    timesz_ltz_zero_neg_neg : forall (a b : integer) . a < 0 -> b < 0 -> 0 < a * b

    integer_integral_domain : forall (a b : integer) .
                                 a * b = 0 : integer -> a = 0 : integer % b = 0 : integer

    timesz_neq_zero : forall (a b : integer) .
                         a != 0 : integer -> b != 0 : integer -> a * b != 0 : integer

    timesz_ltz_zero_invert : forall (a b : integer) . 0 < a * b -> a < 0 & b < 0 % 0 < a & 0 < b

    timesz_ltz_zero_invert_neg : forall (a b : integer) .
                                    a * b < 0 -> a < 0 & 0 < b % 0 < a & b < 0

    times_to_integer : forall (m n : nat) .
                          nat_to_integer (m *n n) = nat_to_integer m * nat_to_integer n : integer

    timesz_to_nat : forall (a b : integer) .
                       0 <= a
                       -> 0 <= b
                       -> integer_to_nat (a * b) = integer_to_nat a *n integer_to_nat b : nat

    timesz_ltz_l : forall (a b b' : integer) . 0 < a -> b < b' -> a * b < a * b'

    timesz_ltz_r : forall (a a' b : integer) . 0 < b -> a < a' -> a * b < a' * b

    timesz_cancel_l : forall (a b c : integer) .
                         c != 0 : integer -> c * a = c * b : integer -> a = b : integer

    timesz_cancel_r : forall (a b c : integer) .
                         c != 0 : integer -> a * c = b * c : integer -> a = b : integer

    timesz_cancel_leqz_l : forall (a b c : integer) . 0 < c -> c * a <= c * b -> a <= b

    timesz_cancel_leqz_r : forall (a b c : integer) . 0 < c -> a * c <= b * c -> a <= b

    timesz_cancel_ltz_l : forall (a b c : integer) . 0 < c -> c * a < c * b -> a < b

    timesz_cancel_ltz_r : forall (a b c : integer) . 0 < c -> a * c < b * c -> a < b

    timesz_cancel_leqz_l_remainder : forall (a b c r : integer) .
                                        0 < c -> r < c -> c * a <= c * b + r -> a <= b

    timesz_cancel_leqz_r_remainder : forall (a b c r : integer) .
                                        0 < c -> r < c -> a * c <= b * c + r -> a <= b


### Minimum/Maximum

    minz : integer -> integer -> integer
         = fn a b . if a <=? b then a else b

    maxz : integer -> integer -> integer
         = fn a b . if a <=? b then b else a

    negz_minz : forall (a b : integer) . ~ (minz a b) = maxz (~ a) (~ b) : integer

    negz_maxz : forall (a b : integer) . ~ (maxz a b) = minz (~ a) (~ b) : integer

    maxz_as_minz : forall (a b : integer) . maxz a b = ~ (minz (~ a) (~ b)) : integer

    minz_as_maxz : forall (a b : integer) . minz a b = ~ (maxz (~ a) (~ b)) : integer

    minz_commute : forall (a b : integer) . minz a b = minz b a : integer

    maxz_commute : forall (a b : integer) . maxz a b = maxz b a : integer

    minz_assoc : forall (a b c : integer) . minz (minz a b) c = minz a (minz b c) : integer

    maxz_assoc : forall (a b c : integer) . maxz (maxz a b) c = maxz a (maxz b c) : integer

    minz_leq_l : forall (a b : integer) . minz a b <= a

    minz_leq_r : forall (a b : integer) . minz a b <= b

    maxz_leq_l : forall (a b : integer) . a <= maxz a b

    maxz_leq_r : forall (a b : integer) . b <= maxz a b

    minz_glb : forall (a b c : integer) . c <= a -> c <= b -> c <= minz a b

    maxz_lub : forall (a b c : integer) . a <= c -> b <= c -> maxz a b <= c

    minz_eq_l : forall (a b : integer) . a <= b -> minz a b = a : integer

    minz_eq_r : forall (a b : integer) . b <= a -> minz a b = b : integer

    maxz_eq_l : forall (a b : integer) . b <= a -> maxz a b = a : integer

    maxz_eq_r : forall (a b : integer) . a <= b -> maxz a b = b : integer

    minz_idem : forall (a : integer) . minz a a = a : integer

    maxz_idem : forall (a : integer) . maxz a a = a : integer

    minz_dist_maxz_l : forall (a b c : integer) .
                          minz (maxz a b) c = maxz (minz a c) (minz b c) : integer

    minz_dist_maxz_r : forall (a b c : integer) .
                          minz a (maxz b c) = maxz (minz a b) (minz a c) : integer

    maxz_dist_minz_l : forall (a b c : integer) .
                          maxz (minz a b) c = minz (maxz a c) (maxz b c) : integer

    maxz_dist_minz_r : forall (a b c : integer) .
                          maxz a (minz b c) = minz (maxz a b) (maxz a c) : integer

    plusz_dist_minz_l : forall (a b c : integer) . minz a b + c = minz (a + c) (b + c) : integer

    plusz_dist_minz_r : forall (a b c : integer) . a + minz b c = minz (a + b) (a + c) : integer

    plusz_dist_maxz_l : forall (a b c : integer) . maxz a b + c = maxz (a + c) (b + c) : integer

    plusz_dist_maxz_r : forall (a b c : integer) . a + maxz b c = maxz (a + b) (a + c) : integer

    min_to_integer : forall (m n : nat) .
                        nat_to_integer (Nat.min m n)
                          = minz (nat_to_integer m) (nat_to_integer n)
                          : integer

    max_to_integer : forall (m n : nat) .
                        nat_to_integer (Nat.max m n)
                          = maxz (nat_to_integer m) (nat_to_integer n)
                          : integer

    minz_to_nat : forall (a b : integer) .
                     integer_to_nat (minz a b)
                       = Nat.min (integer_to_nat a) (integer_to_nat b)
                       : nat

    maxz_to_nat : forall (a b : integer) .
                     integer_to_nat (maxz a b)
                       = Nat.max (integer_to_nat a) (integer_to_nat b)
                       : nat


### Absolute value

    absz : integer -> integer
         = fn a . if 0 <=? a then a else ~ a

    absz_nonneg : forall (a : integer) . 0 <= absz a

    absz_of_nonneg : forall (a : integer) . 0 <= a -> absz a = a : integer

    absz_of_nonpos : forall (a : integer) . a <= 0 -> absz a = ~ a : integer

    absz_negz : forall (a : integer) . absz (~ a) = absz a : integer

    absz_timesz : forall (a b : integer) . absz (a * b) = absz a * absz b : integer

    absz_plusz_leqz : forall (a b : integer) . absz (a + b) <= absz a + absz b

    absz_minusz_leqz : forall (a b : integer) . absz (a - b) <= absz a + absz b

    absz_nat_to_integer : forall (n : nat) . absz (nat_to_integer n) = nat_to_integer n : integer

    absz_zero : absz 0 = 0 : integer

    absz_zero_invert : forall (a : integer) . absz a = 0 : integer -> a = 0 : integer

    absz_one : absz 1 = 1 : integer

    absz_minus_one : absz -1 = 1 : integer


### Division

Since divisors must be nonzero, we define `nonzero` as an abbreviation
(*i.e.,* a soft constant):

    nonzero : U 0
            = { x : integer | x != 0 : integer }

    divz : integer -> nonzero -> integer
    
    modz : integer -> nonzero -> integer

    modz_spec : forall (a : integer) (b : nonzero) . 0 <= modz a b & modz a b < absz b

    divz_spec : forall (a : integer) (b : nonzero) . divz a b * b + modz a b = a : integer

    modz_nonneg : forall (a : integer) (b : nonzero) . 0 <= modz a b

    modz_ltz_r : forall (a : integer) (b : nonzero) . modz a b < absz b

    divz_prop : forall (a : integer) (b : nonzero) . divz a b * b + modz a b = a : integer

    modz_prop : forall (a : integer) (b : nonzero) . modz a b = a - divz a b * b : integer

    division_unique : forall (a : integer) (b : nonzero) (q q' r r' : integer) .
                         a = q * b + r : integer
                         -> a = q' * b + r' : integer
                         -> 0 <= r
                         -> 0 <= r'
                         -> r < absz b
                         -> r' < absz b
                         -> q = q' : integer & r = r' : integer

    division_property : forall (a : integer) (b : nonzero) (q r : integer) .
                           a = q * b + r : integer
                           -> 0 <= r
                           -> r < absz b
                           -> divz a b = q : integer & modz a b = r : integer

    divz_timesz_r : forall (a : integer) (b : nonzero) . divz (a * b) b = a : integer

    divz_timesz_l : forall (a : integer) (b : nonzero) . divz (b * a) b = a : integer

    modz_timesz_r : forall (a : integer) (b : nonzero) . modz (a * b) b = 0 : integer

    modz_timesz_l : forall (a : integer) (b : nonzero) . modz (b * a) b = 0 : integer

    divz_0 : forall (a : nonzero) . divz 0 a = 0 : integer

    modz_0 : forall (a : nonzero) . modz 0 a = 0 : integer

    divz_1 : forall (a : integer) . divz a 1 = a : integer

    modz_1 : forall (a : integer) . modz a 1 = 0 : integer

    divz_self : forall (a : nonzero) . divz a a = 1 : integer

    modz_self : forall (a : nonzero) . modz a a = 0 : integer

    divz_plusz_r : forall (a : integer) (b : nonzero) . divz (a + b) b = 1 + divz a b : integer

    divz_plusz_l : forall (a : integer) (b : nonzero) . divz (b + a) b = 1 + divz a b : integer

    modz_plusz_r : forall (a : integer) (b : nonzero) . modz (a + b) b = modz a b : integer

    modz_plusz_l : forall (a : integer) (b : nonzero) . modz (b + a) b = modz a b : integer

    divz_minusz : forall (a : integer) (b : nonzero) . divz (a - b) b = -1 + divz a b : integer

    modz_minusz : forall (a : integer) (b : nonzero) . modz (a - b) b = modz a b : integer

    timesz_divz_l : forall (a : integer) (b : nonzero) . divz a b * b = a - modz a b : integer

    timesz_divz_r : forall (a : integer) (b : nonzero) . b * divz a b = a - modz a b : integer

