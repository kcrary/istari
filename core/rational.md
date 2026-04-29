open:Rational
overload:rational
# `Rational`

Expressions in this file are rendered using the `rational`
[overloading mode](../overloading.html).

The type of rationals:

    rational : type:rational


### Plus and negation

    (* +q *)
    plusq : type:plusq

    (* ~q *)
    negq : type:negq

    (* -q *)
    minusq : type:minusq
           = def:minusq

    plusq_commute : type:plusq_commute

    plusq_assoc : type:plusq_assoc

    plusq_id_l : type:plusq_id_l

    plusq_id_r : type:plusq_id_r

    negq_invol : type:negq_invol

    plusq_inverse_l : type:plusq_inverse_l

    plusq_inverse_r : type:plusq_inverse_r

    negq_zero : type:negq_zero

    negq_nonzero : type:negq_nonzero

    negq_injective : type:negq_injective

    negq_plusq : type:negq_plusq

    plusq_cancel_l : type:plusq_cancel_l

    plusq_cancel_r : type:plusq_cancel_r

    plusq_shift_l : type:plusq_shift_l

    plusq_shift_r : type:plusq_shift_r

    plusq_shift_lr : type:plusq_shift_lr

    plusq_shift_rl : type:plusq_shift_rl

    negq_minusq : type:negq_minusq

    plusq_compat : type:plusq_compat

    minusq_compat : type:minusq_compat

    negq_compat : type:negq_compat


### Times and inverse

    (* *z *)
    timesq : type:timesq

To simplify the type of `invq`, we permit division by zero and we set
its result to zero.  Naturally, the divisor usually must be nonzero
for `invq` to have good properties.

    invq : type:invq

    (* |q *)
    divq : type:divq
         = def:divq

    timesq_commute : type:timesq_commute

    timesq_assoc : type:timesq_assoc

    timesq_id_l : type:timesq_id_l

    timesq_id_r : type:timesq_id_r

    timesq_ann_l : type:timesq_ann_l

    timesq_ann_r : type:timesq_ann_r

    invq_invol : type:invq_invol

    timesq_inverse_l : type:timesq_inverse_l

    timesq_inverse_r : type:timesq_inverse_r

    invq_timesq : type:invq_timesq

    invq_zero : type:invq_zero

    invq_nonzero : type:invq_nonzero

    invq_one : type:invq_one

    invq_injective : type:invq_injective

    rational_integral_domain : type:rational_integral_domain

    timesq_cancel_l : type:timesq_cancel_l

    timesq_cancel_r : type:timesq_cancel_r

    timesq_shift_l : type:timesq_shift_l

    timesq_shift_r : type:timesq_shift_r

    timesq_shift_lr : type:timesq_shift_lr

    timesq_shift_rl : type:timesq_shift_rl

    timesq_compat : type:timesq_compat

    invq_compat : type:invq_compat


### Distributivity

    timesq_dist_plusq_l : type:timesq_dist_plusq_l

    timesq_dist_plusq_r : type:timesq_dist_plusq_r

    negq_dist_plusq : type:negq_dist_plusq

    negq_dist_timesq_l : type:negq_dist_timesq_l

    negq_dist_timesq_r : type:negq_dist_timesq_r

    negq_dist_invq : type:negq_dist_invq

    negq_as_timesq : type:negq_as_timesq

    plusq_self : type:plusq_self


### Inequalities

    (* <q= *)
    leqq : type:leqq

    (* <q *)
    ltq : type:ltq

    leqq_inhabitant : type:leqq_inhabitant

    ltq_inhabitant : type:ltq_inhabitant

    leqq_refl : type:leqq_refl

    leqq_refl_eq : type:leqq_refl_eq

    leqq_trans : type:leqq_trans

    leqq_antisymm : type:leqq_antisymm

    ltq_irrefl : type:ltq_irrefl

    leqq_ltq_trans : type:leqq_ltq_trans

    ltq_leqq_trans : type:ltq_leqq_trans

    ltq_trans : type:ltq_trans

    ltq_impl_leqq : type:ltq_impl_leqq

    ltq_impl_neq : type:ltq_impl_neq

This one gives transitivity in the form needed for rewriting:

    leqq_implication : type:leqq_implication

    ltq_implication : type:ltq_implication

    not_leqq : type:not_leqq

    not_ltq : type:not_ltq

    ltq_from_leqq_neq : type:ltq_from_leqq_neq

    ltq_0_1 : type:ltq_0_1

    neqq_0_1 : type:neqq_0_1

    leqq_0_1 : type:leqq_0_1

    ltq_neg1_0 : type:ltq_neg1_0

    leqq_neg1_0 : type:leqq_neg1_0

    neqq_neg1_0 : type:neqq_neg1_0


### Plus and negation inequality

    plusq_leqq : type:plusq_leqq

    plusq_ltq_l : type:plusq_ltq_l

    plusq_ltq_r : type:plusq_ltq_r

    plusq_ltq : type:plusq_ltq

    plusq_cancel_leqq_l : type:plusq_cancel_leqq_l

    plusq_cancel_leqq_r : type:plusq_cancel_leqq_r

    plusq_cancel_leqq_leqq_l : type:plusq_cancel_leqq_leqq_l

    plusq_cancel_leqq_leqq_r : type:plusq_cancel_leqq_leqq_r

    plusq_shift_leqq_l : type:plusq_shift_leqq_l

    plusq_shift_leqq_r : type:plusq_shift_leqq_r

    plusq_shift_leqq_lr : type:plusq_shift_leqq_lr

    plusq_shift_leqq_rl : type:plusq_shift_leqq_rl

    plusq_cancel_ltq_l : type:plusq_cancel_ltq_l

    plusq_cancel_ltq_r : type:plusq_cancel_ltq_r

    plusq_shift_ltq_l : type:plusq_shift_ltq_l

    plusq_shift_ltq_r : type:plusq_shift_ltq_r

    plusq_shift_ltq_lr : type:plusq_shift_ltq_lr

    plusq_shift_ltq_rl : type:plusq_shift_ltq_rl

    negq_leqq : type:negq_leqq

    negq_leqq' : type:negq_leqq'

    negq_ltq : type:negq_ltq

    negq_ltq' : type:negq_ltq'


### Times and inverse inequality

    timesq_leqq : type:timesq_leqq

    (* an alias for timesq_leqq *)
    timesq_leqq_pos_pos : type:timesq_leqq_pos_pos

    timesq_leqq_neg_neg : type:timesq_leqq_neg_neg

    timesq_leqq_pos_neg : type:timesq_leqq_pos_neg

    timesq_leqq_neg_neg : type:timesq_leqq_neg_neg

    timesq_leqq_zero : type:timesq_leqq_zero

    (* an alias for timesq_leqq_zero *)
    timesq_leqq_zero_pos_pos : type:timesq_leqq_zero_pos_pos

    timesq_leqq_zero_pos_neg : type:timesq_leqq_zero_pos_neg

    timesq_leqq_zero_neg_pos : type:timesq_leqq_zero_neg_pos

    timesq_leqq_zero_neg_neg : type:timesq_leqq_zero_neg_neg

    timesq_leqq_l : type:timesq_leqq_l

    timesq_leqq_r : type:timesq_leqq_r

    timesq_leqq_l_neg : type:timesq_leqq_l_neg

    timesq_leqq_r_neg : type:timesq_leqq_r_neg

    timesq_ltq_l : type:timesq_ltq_l

    timesq_ltq_r : type:timesq_ltq_r

    timesq_ltq_l_neg : type:timesq_ltq_l_neg

    timesq_ltq_r_neg : type:timesq_ltq_r_neg

    timesq_ltq_zero : type:timesq_ltq_zero

    (* an alias for timesq_ltq_zero *)
    timesq_ltq_zero_pos_pos : type:timesq_ltq_zero_pos_pos

    timesq_ltq_zero_pos_neg : type:timesq_ltq_zero_pos_neg

    timesq_ltq_zero_neg_pos : type:timesq_ltq_zero_neg_pos

    timesq_ltq_zero_neg_neg : type:timesq_ltq_zero_neg_neg

    timesq_neq_zero : type:timesq_neq_zero

    timesq_ltq_zero_invert : type:timesq_ltq_zero_invert

    timesq_ltq_zero_invert_neg : type:timesq_ltq_zero_invert_neg

    timesq_cancel_leqq_l : type:timesq_cancel_leqq_l

    timesq_cancel_leqq_r : type:timesq_cancel_leqq_r

    timesq_cancel_ltq_l : type:timesq_cancel_ltq_l

    timesq_cancel_ltq_r : type:timesq_cancel_ltq_r

    timesq_cancel_leqq_l_neg : type:timesq_cancel_leqq_l_neg

    timesq_cancel_leqq_r_neg : type:timesq_cancel_leqq_r_neg

    timesq_cancel_ltq_l_neg : type:timesq_cancel_ltq_l_neg

    timesq_cancel_ltq_r_neg : type:timesq_cancel_ltq_r_neg

    timesq_shift_leqq_r : type:timesq_shift_leqq_r

    timesq_shift_leqq_l : type:timesq_shift_leqq_l

    timesq_shift_leqq_lr : type:timesq_shift_leqq_lr

    timesq_shift_leqq_rl : type:timesq_shift_leqq_rl

    timesq_shift_ltq_r : type:timesq_shift_ltq_r

    timesq_shift_ltq_l : type:timesq_shift_ltq_l

    timesq_shift_ltq_lr : type:timesq_shift_ltq_lr

    timesq_shift_ltq_rl : type:timesq_shift_ltq_rl

    timesq_shift_leqq_r_neg : type:timesq_shift_leqq_r_neg

    timesq_shift_leqq_l_neg : type:timesq_shift_leqq_l_neg

    timesq_shift_leqq_lr_neg : type:timesq_shift_leqq_lr_neg

    timesq_shift_leqq_rl_neg : type:timesq_shift_leqq_rl_neg

    timesq_shift_ltq_r_neg : type:timesq_shift_ltq_r_neg

    timesq_shift_ltq_l_neg : type:timesq_shift_ltq_l_neg

    timesq_shift_ltq_lr_neg : type:timesq_shift_ltq_lr_neg

    timesq_shift_ltq_rl_neg : type:timesq_shift_ltq_rl_neg

    invq_positive : type:invq_positive

    invq_negative : type:invq_negative

    invq_leqq_pos : type:invq_leqq_pos

    invq_leqq_neg : type:invq_leqq_neg

    invq_ltq_pos : type:invq_ltq_pos

    invq_ltq_neg : type:invq_ltq_neg

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

    invq_leqq_samesign : type:invq_leqq_samesign

    invq_ltq_samesign : type:invq_ltq_samesign


### Relation to integers

    integer_to_rational : type:integer_to_rational

    integer_to_rational_injective : type:integer_to_rational_injective

    integer_to_rational_neq : type:integer_to_rational_neq

    integer_to_rational_mono : type:integer_to_rational_mono

    integer_to_rational_mono_conv : type:integer_to_rational_mono_conv

    integer_to_rational_mono_lt : type:integer_to_rational_mono_lt

    integer_to_rational_mono_lt_conv : type:integer_to_rational_mono_lt_conv

    plusz_to_rational : type:plusz_to_rational

    negz_to_rational : type:negz_to_rational

    minusz_to_rational : type:minusz_to_rational

    timesz_to_rational : type:timesz_to_rational

    eqzb_to_rational : type:eqzb_to_rational

    neqzb_to_rational : type:neqzb_to_rational

    leqzb_to_rational : type:leqzb_to_rational

    ltzb_to_rational : type:ltzb_to_rational


#### Relation to natural numbers

    nat_to_rational : type:nat_to_rational
                    = def:nat_to_rational

    nat_to_rational_injective : type:nat_to_rational_injective

    nat_to_rational_neq : type:nat_to_rational_neq

    integer_nat_to_rational_eq : type:integer_nat_to_rational_eq

    nat_integer_to_rational_eq : type:nat_integer_to_rational_eq

    integer_nat_to_rational_neq : type:integer_nat_to_rational_neq

    nat_integer_to_rational_neq : type:nat_integer_to_rational_neq

    nat_to_rational_mono : type:nat_to_rational_mono

    integer_nat_to_rational_mono : type:integer_nat_to_rational_mono

    nat_integer_to_rational_mono : type:nat_integer_to_rational_mono

    nat_to_rational_mono_lt : type:nat_to_rational_mono_lt

    integer_nat_to_rational_mono_lt : type:integer_nat_to_rational_mono_lt

    nat_integer_to_rational_mono_lt : type:nat_integer_to_rational_mono_lt

    nat_to_rational_nonneg : type:nat_to_rational_nonneg

    plus_to_rational : type:plus_to_rational

    succ_to_rational : type:succ_to_rational

    times_to_rational : type:times_to_rational

    eqb_to_rational : type:eqb_to_rational

    leqb_to_rational : type:leqb_to_rational

    ltb_to_rational : type:ltb_to_rational

    neqb_to_rational : type:neqb_to_rational


### Effective comparisons

    (* =q? *)
    eqqb : type:eqqb

    (* <q=? *)
    leqqb : type:leqqb

    (* <q? *)
    ltqb : type:ltqb

    (* !q=? *)
    neqqb : type:neqqb

    notb_eqqb : type:notb_eqqb

    notb_neqqb : type:notb_neqqb

    notb_leqqb : type:notb_leqqb

    notb_ltqb : type:notb_ltqb

    istrue_eqqb : type:istrue_eqqb

    istrue_neqqb : type:istrue_neqqb

    istrue_leqqb : type:istrue_leqqb

    istrue_ltqb : type:istrue_ltqb


### Decidability

    eq_rational_decide : type:eq_rational_decide

    neq_rational_decide : type:neq_rational_decide

    leqq_decide : type:leqq_decide

    ltq_decide : type:ltq_decide

    eq_rational_stable : type:eq_rational_stable

    neq_rational_stable : type:neq_rational_stable

    leqq_stable : type:leqq_stable

    ltq_stable : type:ltq_stable

    leqq_iff_ltq_or_eq : type:leqq_iff_ltq_or_eq

    rational_trichotomy : type:rational_trichotomy

    rational_dichotomy : type:rational_dichotomy

    rational_dichotomy_weak : type:rational_dichotomy_weak

    rational_dichotomy_neq : type:rational_dichotomy_neq


### Minimum/Maximum

    minq : type:minq
         = def:minq

    maxq : type:maxq
         = def:maxq

    negq_minq : type:negq_minq

    negq_maxq : type:negq_maxq

    maxq_as_minq : type:maxq_as_minq

    minq_as_maxq : type:minq_as_maxq

    minq_commute : type:minq_commute

    maxq_commute : type:maxq_commute

    minq_assoc : type:minq_assoc

    maxq_assoc : type:maxq_assoc

    minq_leq_l : type:minq_leq_l

    minq_leq_r : type:minq_leq_r

    maxq_leq_l : type:maxq_leq_l

    maxq_leq_r : type:maxq_leq_r

    minq_glb : type:minq_glb

    maxq_lub : type:maxq_lub

    minq_eq_l : type:minq_eq_l

    minq_eq_r : type:minq_eq_r

    maxq_eq_l : type:maxq_eq_l

    maxq_eq_r : type:maxq_eq_r

    minq_idem : type:minq_idem

    maxq_idem : type:maxq_idem

    minq_dist_maxq_l : type:minq_dist_maxq_l

    minq_dist_maxq_r : type:minq_dist_maxq_r

    maxq_dist_minq_l : type:maxq_dist_minq_l

    maxq_dist_minq_r : type:maxq_dist_minq_r

    plusq_dist_minq_l : type:plusq_dist_minq_l

    plusq_dist_minq_r : type:plusq_dist_minq_r

    plusq_dist_maxq_l : type:plusq_dist_maxq_l

    plusq_dist_maxq_r : type:plusq_dist_maxq_r

    minz_to_rational : type:minz_to_rational

    maxz_to_rational : type:maxz_to_rational


### Absolute value

    absq : type:absq
         = def:absq

    absq_nonneg : type:absq_nonneg

    absq_of_nonneg : type:absq_of_nonneg

    absq_of_nonpos : type:absq_of_nonpos

    absq_ub : type:absq_ub

    absq_idem : type:absq_idem

    absq_negq : type:absq_negq

    absq_timesq : type:absq_timesq

    absq_plusq_leqq : type:absq_plusq_leqq

    absq_minusq_leqq : type:absq_minusq_leqq

    absz_to_rational : type:absz_to_rational

    absq_zero : type:absq_zero

    absq_one : type:absq_one

    absq_minus_one : type:absq_minus_one

    absq_minusq_commute : type:absq_minusq_commute

    absq_minusq_upper_bound : type:absq_minusq_upper_bound

    absq_minusq_lower_bound : type:absq_minusq_lower_bound

    absq_minusq_absq : type:absq_minusq_absq


### Floor and Ceiling

    floor : type:floor

    ceiling : type:ceiling
            = def:ceiling

    floor_lb : type:floor_lb

    floor_glb : type:floor_glb

    ceiling_ub : type:ceiling_ub

    ceiling_lub : type:ceiling_lub

    floor_mono : type:floor_mono

    ceiling_mono : type:ceiling_mono

    floor_integer_to_rational : type:floor_integer_to_rational

    ceiling_integer_to_rational : type:ceiling_integer_to_rational

    floor_plus_r : type:floor_plus_r

    floor_plus_l : type:floor_plus_l

    ceiling_plus_r : type:ceiling_plus_r

    ceiling_plus_l : type:ceiling_plus_l

    floor_mono_lt : type:floor_mono_lt

    ceiling_mono_lt : type:ceiling_mono_lt

    floor_negq : type:floor_negq

    ceiling_negq : type:ceiling_negq

    floor_nonneg : type:floor_nonneg

    floor_nonpos : type:floor_nonpos

    ceiling_nonneg : type:ceiling_nonneg

    ceiling_nonpos : type:ceiling_nonpos

    floor_from_bounds : type:floor_from_bounds

    ceiling_from_bounds : type:ceiling_from_bounds

    floor_ceiling_leqz : type:floor_ceiling_leqz


### Miscellaneous

    rational_dense : type:rational_dense

    leqq_from_upper_bounds : type:leqq_from_upper_bounds

    rational_total : type:rational_total

    rational_strict : type:rational_strict
