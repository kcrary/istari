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

    leq_trans : type:leq_trans

    leq_antisymm : type:leq_antisymm

    leq_implication : type:leq_implication

    lt_impl_leq : type:lt_impl_leq

    lt_succ : type:lt_succ

    lt_irrefl : type:lt_irrefl

    lt_trans : type:lt_trans

    leq_lt_trans : type:leq_lt_trans

    lt_leq_trans : type:lt_leq_trans

    lt_0_succ : type:lt_0_succ

    lt_succ_succ : type:lt_succ_succ

Strong induction for natural numbers:

    lt_well_founded : type:lt_well_founded


### Addition and Subtraction

    plus : type:plus

    plus (zero) n --> n
    plus (succ m) n --> succ (plus m n)

    minus : type:minus

    minus m (zero) --> m
    minus m (succ n) --> natcase m zero (fn m' . minus m' n)

    plus_0_l : type:plus_0_l

    plus_0_r : type:plus_0_r

    plus_assoc : type:plus_assoc

    plus_shift_r : type:plus_shift_r

    plus_commute : type:plus_commute

    plus_leq_l : type:plus_leq_l

    plus_leq_r : type:plus_leq_r

    plus_leq : type:plus_leq

    plus_lt_r : type:plus_lt_r

    plus_minus_cancel_l : type:plus_minus_cancel_l

    plus_minus_cancel_r : type:plus_minus_cancel_r

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


### Maximum

    max : type:max

    max_id_l : type:max_id_l

    max_id_r : type:max_id_r

    max_succ : type:max_succ

    max_leq_l : type:max_leq_l

    max_leq_r : type:max_leq_r

    max_lub : type:max_lub

    max_eq_l : type:max_eq_l

    max_eq_r : type:max_eq_r
