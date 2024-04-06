open:Integer
# `Integer`

The `integer` type is primitive but aliased in the `Integer` module:

    integer : type:integer

Integer literals are written using a `` z` `` parsing directive.  For
example, zero is ``z`0``.


### Plus and negation

    (* +z *)
    plusz : type:plusz

    (* ~z *)
    negz : type:negz

    (* -z *)
    minusz : type:minusz
           = def:minusz

    neq_0_1 : type:neq_0_1

    neq_0_neg1 : type:neq_0_neg1

    plusz_commute : type:plusz_commute

    plusz_assoc : type:plusz_assoc

    plusz_id_l : type:plusz_id_l

    plusz_id_r : type:plusz_id_r

    plusz_inverse_l : type:plusz_inverse_l

    plusz_inverse_r : type:plusz_inverse_r

    negz_invol : type:negz_invol

    negz_plusz : type:negz_plusz

    plusz_cancel_l : type:plusz_cancel_l

    plusz_cancel_r : type:plusz_cancel_r

    plusz_shift_l : type:plusz_shift_l

    plusz_shift_r : type:plusz_shift_r

    plusz_shift_lr : type:plusz_shift_lr

    plusz_shift_rl : type:plusz_shift_rl

    plusz_compat : type:plusz_compat

    negz_compat : type:negz_compat


### Inequalities

    (* <z= *)
    leqz : type:leqz

    (* <z *)
    ltz : type:ltz
        = def:ltz

    leqz_inhabitant : type:leqz_inhabitant

    ltz_inhabitant : type:ltz_inhabitant

    leqz_0_1 : type:leqz_0_1

    ltz_0_1 : type:ltz_0_1

    leqz_neg1_0 : type:leqz_neg1_0

    ltz_neg1_0 : type:ltz_neg1_0

    leqz_refl : type:leqz_refl

    leqz_refl_eq : type:leqz_refl_eq

    leqz_trans : type:leqz_trans

    leqz_antisymm : type:leqz_antisymm

This one gives transitivity in the form needed for rewriting:

    leqz_implication : type:leqz_implication

    ltz_impl_leqz : type:ltz_impl_leqz

    ltz_irrefl : type:ltz_irrefl

    ltz_trans : type:ltz_trans

    leqz_ltz_trans : type:leqz_ltz_trans

    ltz_leqz_trans : type:ltz_leqz_trans

    ltz_succ : type:ltz_succ

    leqz_succ : type:leqz_succ

    plusz_leqz : type:plusz_leqz

    plusz_cancel_leqz_l : type:plusz_cancel_leqz_l

    plusz_cancel_leqz_r : type:plusz_cancel_leqz_r

    plusz_cancel_leqz_leqz_l : type:plusz_cancel_leqz_leqz_l

    plusz_cancel_leqz_leqz_r : type:plusz_cancel_leqz_leqz_r

    plusz_shift_leqz_l : type:plusz_shift_leqz_l

    plusz_shift_leqz_r : type:plusz_shift_leqz_r

    plusz_shift_leqz_lr : type:plusz_shift_leqz_lr

    plusz_shift_leqz_rl : type:plusz_shift_leqz_rl

    plusz_ltz_l : type:plusz_ltz_l

    plusz_ltz_r : type:plusz_ltz_r

    plusz_ltz : type:plusz_ltz

    plusz_cancel_ltz_l : type:plusz_cancel_ltz_l

    plusz_cancel_ltz_r : type:plusz_cancel_ltz_r

    plusz_shift_ltz_l : type:plusz_shift_ltz_l

    plusz_shift_ltz_r : type:plusz_shift_ltz_r

    plusz_shift_ltz_lr : type:plusz_shift_ltz_lr

    plusz_shift_ltz_rl : type:plusz_shift_ltz_rl

    negz_leqz : type:negz_leqz

    negz_leqz' : type:negz_leqz'

    negz_ltz : type:negz_ltz

    negz_ltz' : type:negz_ltz'

    not_leqz : type:not_leqz

    not_ltz : type:not_ltz

    ltz_from_leqz_neq : type:ltz_from_leqz_neq

    ltz_as_leqz_l : type:ltz_as_leqz_l

    ltz_as_leqz_r : type:ltz_as_leqz_r

    leqz_as_ltz_l : type:leqz_as_ltz_l

    leqz_as_ltz_r : type:leqz_as_ltz_r



### Effective comparisons

    eqzb : type:eqzb

    leqzb : type:leqzb

    ltzb : type:ltzb
         = def:ltzb

    neqzb : type:neqzb
          = def:neqzb

    istrue_eqzb : type:istrue_eqzb

    istrue_neqzb : type:istrue_neqzb

    istrue_leqzb : type:istrue_leqzb

    istrue_ltzb : type:istrue_ltzb

    notb_eqzb : type:notb_eqzb

    notb_neqzb : type:notb_neqzb

    notb_leqzb : type:notb_leqzb

    notb_ltzb : type:notb_ltzb


### Induction

We say that `a` is smaller than `b` when `b` < `a` &le; 0 or 0 &le; `a` < `b`:

    smaller : type:smaller
            = def:smaller


Smaller is well-founded, giving us strong induction for integers:

    smaller_well_founded : type:smaller_well_founded


As a corollary, we can build an iterator for integers.  It has three
cases: a base case for zero, a negative case that works downwards, and a
positive case that works upwards.

    integer_iter : type:integer_iter
                 =rec= defrec:integer_iter


### Relation to natural numbers

    nat_to_integer : type:nat_to_integer
                   =rec= defrec:nat_to_integer

    nat_to_integer (zero) --> z`0
    nat_to_integer (succ n) --> plusz z`1 (nat_to_integer n)

    integer_to_nat : type:integer_to_nat
                   =rec= defrec:integer_to_nat

    nat_to_integer_inv : type:nat_to_integer_inv

    integer_to_nat_inv : type:integer_to_nat_inv

    nat_to_integer_nonneg : type:nat_to_integer_nonneg

    nat_to_integer_mono : type:nat_to_integer_mono

    nat_to_integer_mono_lt : type:nat_to_integer_mono_lt

    integer_to_nat_zero : type:integer_to_nat_zero

    integer_to_nat_succ : type:integer_to_nat_succ

    integer_to_nat_mono : type:integer_to_nat_mono

    integer_to_nat_mono_lt : type:integer_to_nat_mono_lt

    succ_to_integer : type:succ_to_integer

    plus_to_integer : type:plus_to_integer

    plusz_to_nat : type:plusz_to_nat

    pred_to_integer : type:pred_to_integer

    minus_to_integer : type:minus_to_integer

    minusz_to_nat : type:minusz_to_nat


### Decidability

    eq_integer_decide : type:eq_integer_decide

    neq_integer_decide : type:neq_integer_decide

    leqz_decide : type:leqz_decide

    ltz_decide : type:ltz_decide

    eq_integer_stable : type:eq_integer_stable

    neq_integer_stable : type:neq_integer_stable

    leqz_stable : type:leqz_stable

    ltz_stable : type:ltz_stable

    leqz_iff_ltz_or_eq : type:leqz_iff_ltz_or_eq

    integer_trichotomy : type:integer_trichotomy

    integer_dichotomy : type:integer_dichotomy

    integer_dichotomy_weak : type:integer_dichotomy_weak

    integer_dichotomy_neq : type:integer_dichotomy_neq


### Multiplication

    (* *z *)
    timesz : type:timesz

    timesz_id_l : type:timesz_id_l

    timesz_id_r : type:timesz_id_r

    timesz_ann_l : type:timesz_ann_l

    timesz_ann_r : type:timesz_ann_r

    timesz_commute : type:timesz_commute

    timesz_assoc : type:timesz_assoc

    timesz_dist_plusz_l : type:timesz_dist_plusz_l

    timesz_dist_plusz_r : type:timesz_dist_plusz_r

    negz_dist_timesz_l : type:negz_dist_timesz_l

    negz_dist_timesz_r : type:negz_dist_timesz_r

    negz_as_timesz : type:negz_as_timesz

    timesz_compat : type:timesz_compat

    timesz_leqz : type:timesz_leqz

    (* an alias for timesz_leqz *)
    timesz_leqz_pos_pos : type:timesz_leqz_pos_pos

    timesz_leqz_neg_neg : type:timesz_leqz_neg_neg

    timesz_leqz_pos_neg : type:timesz_leqz_pos_neg

    timesz_leqz_neg_pos : type:timesz_leqz_neg_pos

    timesz_leqz_l : type:timesz_leqz_l

    timesz_leqz_r : type:timesz_leqz_r

    timesz_leqz_l_neg : type:timesz_leqz_l_neg

    timesz_leqz_r_neg : type:timesz_leqz_r_neg

    timesz_ltz_zero : type:timesz_ltz_zero

    (* an alias for timesz_ltz_zero *)
    timesz_ltz_zero_pos_pos : type:timesz_ltz_zero_pos_pos

    timesz_ltz_zero_pos_neg : type:timesz_ltz_zero_pos_neg

    timesz_ltz_zero_neg_pos : type:timesz_ltz_zero_neg_pos

    timesz_ltz_zero_neg_neg : type:timesz_ltz_zero_neg_neg

    integer_integral_domain : type:integer_integral_domain

    timesz_ltz_zero_invert : type:timesz_ltz_zero_invert

    times_to_integer : type:times_to_integer

    timesz_to_nat : type:timesz_to_nat

    timesz_ltz_l : type:timesz_ltz_l

    timesz_ltz_r : type:timesz_ltz_r

    timesz_cancel_leqz_l : type:timesz_cancel_leqz_l

    timesz_cancel_leqz_r : type:timesz_cancel_leqz_r

    timesz_cancel_leqz_l_remainder : type:timesz_cancel_leqz_l_remainder

    timesz_cancel_leqz_r_remainder : type:timesz_cancel_leqz_r_remainder


### Minimum/Maximum

    minz : type:minz
         = def:minz

    maxz : type:maxz
         = def:maxz

    negz_minz : type:negz_minz

    negz_maxz : type:negz_maxz

    maxz_as_minz : type:maxz_as_minz

    minz_as_maxz : type:minz_as_maxz

    minz_commute : type:minz_commute

    maxz_commute : type:maxz_commute

    minz_assoc : type:minz_assoc

    maxz_assoc : type:maxz_assoc

    minz_leq_l : type:minz_leq_l

    minz_leq_r : type:minz_leq_r

    maxz_leq_l : type:maxz_leq_l

    maxz_leq_r : type:maxz_leq_r

    minz_glb : type:minz_glb

    maxz_lub : type:maxz_lub

    minz_eq_l : type:minz_eq_l

    minz_eq_r : type:minz_eq_r

    maxz_eq_l : type:maxz_eq_l

    maxz_eq_r : type:maxz_eq_r

    minz_idem : type:minz_idem

    maxz_idem : type:maxz_idem

    minz_dist_maxz_l : type:minz_dist_maxz_l

    minz_dist_maxz_r : type:minz_dist_maxz_r

    maxz_dist_minz_l : type:maxz_dist_minz_l

    maxz_dist_minz_r : type:maxz_dist_minz_r

    plusz_dist_minz_l : type:plusz_dist_minz_l

    plusz_dist_minz_r : type:plusz_dist_minz_r

    plusz_dist_maxz_l : type:plusz_dist_maxz_l

    plusz_dist_maxz_r : type:plusz_dist_maxz_r

    min_to_integer : type:min_to_integer

    max_to_integer : type:max_to_integer

    minz_to_nat : type:minz_to_nat

    maxz_to_nat : type:maxz_to_nat
