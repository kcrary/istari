open:Nat
# `Nat`

The `nat` type is primitive, but aliased in the `Nat` module:

    nat : type:nat
    zero : type:zero
    succ : type:succ

The iterator for natural numbers:

    nat_iter : type:nat_iter

    nat_iter _ z _ (zero) --> z
    nat_iter a z s (succ n) --> s n (nat_iter a z s n)

A simpler case-analysis operation:

    natcase : type:natcase

    natcase (zero) z s --> z
    natcase (succ n) z s --> s n


### Equality

    eq_0_succ_not : type:eq_0_succ_not

    eq_succ_0_not : type:eq_succ_0_not

    succ_inj : type:succ_inj


### Inequalities

    leq : type:leq

    lt : type:lt

    leq_inhabitant : type:leq_inhabitant

    lt_inhabitant : type:lt_inhabitant

    leq_0_min : type:leq_0_min

    leq_succ_0_not : type:leq_succ_0_not

    leq_succ_succ : type:leq_succ_succ

    leq_succ_invert : type:leq_succ_invert

    leq_succ : type:leq_succ

    leq_refl : type:leq_refl

    leq_refl_eq : type:leq_refl_eq

    leq_trans : type:leq_trans

    leq_antisymm : type:leq_antisymm

This one gives transitivity in the form needed for rewriting:

    leq_implication : type:leq_implication

    lt_impl_leq : type:lt_impl_leq

    lt_succ_succ : type:lt_succ_succ

    lt_succ_invert : type:lt_succ_invert

    lt_succ : type:lt_succ

    lt_irrefl : type:lt_irrefl

    lt_trans : type:lt_trans

    leq_lt_trans : type:leq_lt_trans

    lt_leq_trans : type:lt_leq_trans

    lt_0_succ : type:lt_0_succ

    lt_0_not : type:lt_0_not

    not_leq : type:not_leq

    not_lt : type:not_lt

    lt_from_leq_neq : type:lt_from_leq_neq

Strong induction for natural numbers:

    lt_well_founded : type:lt_well_founded


### Addition

    plus : type:plus

    plus (zero) n --> n
    plus (succ m) n --> succ (plus m n)

    plus_0_l : type:plus_0_l

    plus_0_r : type:plus_0_r

    plus_assoc : type:plus_assoc

    plus_shift_r : type:plus_shift_r

    plus_commute : type:plus_commute

    plus_leq_l : type:plus_leq_l

    plus_leq_r : type:plus_leq_r

    plus_leq : type:plus_leq

    plus_cancel_leq_l : type:plus_cancel_leq_l

    plus_cancel_leq_r : type:plus_cancel_leq_r

    plus_cancel_leq_leq_l : type:plus_cancel_leq_leq_l

    plus_cancel_leq_leq_r : type:plus_cancel_leq_leq_r

    plus_lt_r : type:plus_lt_r

    plus_cancel_l : type:plus_cancel_l

    plus_cancel_l_eq : type:plus_cancel_l_eq

    plus_cancel_r : type:plus_cancel_r

    plus_cancel_r_eq : type:plus_cancel_r_eq

    plus_compat : type:plus_compat


### Subtraction

    minus : type:minus

    minus m (zero) --> m
    minus m (succ n) --> natcase m zero (fn m' . minus m' n)

    plus_minus_cancel_l : type:plus_minus_cancel_l

    plus_minus_cancel_r : type:plus_minus_cancel_r

    minus_swap : type:minus_swap

    minus_plus_cancel : type:minus_plus_cancel

    minus_0_l : type:minus_0_l

    minus_0_r : type:minus_0_r

    minus_proper : type:minus_proper

    minus_assoc : type:minus_assoc

    minus_succ : type:minus_succ

    minus_leq_l : type:minus_leq_l

    minus_leq : type:minus_leq

    minus_self : type:minus_self

    minus_succ_l_leq : type:minus_succ_l_leq

    minus_succ_l_eq : type:minus_succ_l_eq

    plus_minus_swap : type:plus_minus_swap

    plus_minus_assoc : type:plus_minus_assoc

    plus_minus_assoc_swap : type:plus_minus_assoc_swap

    minus_plus_assoc : type:minus_plus_assoc

    minus_compat : type:minus_compat


### Multiplication

    times : type:times

    times (zero) _ --> zero ;
    times (succ m) n --> plus n (times m n) ;

    times_0_l : type:times_0_l

    times_0_r : type:times_0_r

    times_1_l : type:times_1_l

    times_1_r : type:times_1_r

    times_commute : type:times_commute

    times_assoc : type:times_assoc

    times_dist_succ_r : type:times_dist_succ_r

    times_dist_plus_l : type:times_dist_plus_l

    times_dist_plus_r : type:times_dist_plus_r

    times_leq : type:times_leq

    times_dist_minus_l : type:times_dist_minus_l

    times_dist_minus_r : type:times_dist_minus_r

    nat_integral_domain : type:nat_integral_domain

    times_compat : type:times_compat


### Minimum

    min : type:min

    min_commute : type:min_commute

    min_assoc : type:min_assoc

    min_ann_l : type:min_ann_l

    min_ann_r : type:min_ann_r

    min_succ : type:min_succ

    min_leq_l : type:min_leq_l

    min_leq_r : type:min_leq_r

    min_glb : type:min_glb

    min_eq_l : type:min_eq_l

    min_eq_r : type:min_eq_r


### Maximum

    max : type:max

    max_commute : type:max_commute

    max_assoc : type:max_assoc

    max_id_l : type:max_id_l

    max_id_r : type:max_id_r

    max_succ : type:max_succ

    max_leq_l : type:max_leq_l

    max_leq_r : type:max_leq_r

    max_lub : type:max_lub

    max_eq_l : type:max_eq_l

    max_eq_r : type:max_eq_r


### Effective comparisons

    eqb : type:eqb

    istrue_eqb : type:istrue_eqb

    leqb : type:leqb

    istrue_leqb : type:istrue_leqb

    ltb : type:ltb
        = def:ltb

    istrue_ltb : type:istrue_ltb


### Decidability

    eq_nat_decide : type:eq_nat_decide

    leq_decide : type:leq_decide

    lt_decide : type:lt_decide

    eq_nat_stable : type:eq_nat_stable

    leq_stable : type:leq_stable

    lt_stable : type:lt_stable

    leq_iff_lt_or_eq : type:leq_iff_lt_or_eq

    nat_trichotomy : type:nat_trichotomy

    nat_dichotomy : type:nat_dichotomy

    nat_dichotomy_neq : type:nat_dichotomy_neq
