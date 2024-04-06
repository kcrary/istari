open:Natural
# `Natural`

A doppleganger of the `Nat` module, but using "native" arithmetic to
implement natural numbers instead of a datatype.

    natural : type:natural

Zero is written `` z`0 ``.

    succn : type:succn
          = def:succn

The iterator for natural numbers:

    natural_iter : type:natural_iter

In lieu of reductions (such as `nat_iter _ hz _ (zero) --> hz`), the
library has equality lemmas:

       natural_iter_zeron : type:natural_iter_zeron

       natural_iter_succn : type:natural_iter_succn

A simpler case-analysis operation:

    natural_case : type:natural_case

       natural_case_zeron : type:natural_case_zeron

       natural_case_succn : type:natural_case_succn


### Equality

    eq_0_succn_not : type:eq_0_succn_not

    eq_succn_0_not : type:eq_succn_0_not

    succn_inj : type:succn_inj


### Inequalities

    (* <N= *)
    leqn : type:leqn

    (* <N *)
    ltn : type:ltn

    leqn_inhabitant : type:leqn_inhabitant

    ltn_inhabitant : type:ltn_inhabitant

    leqn_0_min : type:leqn_0_min

    leqn_succn_0_not : type:leqn_succn_0_not

    leqn_succn_succn : type:leqn_succn_succn

    leqn_succn_invert : type:leqn_succn_invert

    leqn_succn : type:leqn_succn

    leqn_refl : type:leqn_refl

    leqn_refl_eq : type:leqn_refl_eq

    leqn_trans : type:leqn_trans

    leqn_antisymm : type:leqn_antisymm

    leqn_implication : type:leqn_implication

    ltn_impl_leqn : type:ltn_impl_leqn

    ltn_succn_succn : type:ltn_succn_succn

    ltn_succn_invert : type:ltn_succn_invert

    ltn_succn : type:ltn_succn

    ltn_irrefl : type:ltn_irrefl

    ltn_trans : type:ltn_trans

    leqn_ltn_trans : type:leqn_ltn_trans

    ltn_leqn_trans : type:ltn_leqn_trans

    ltn_0_succn : type:ltn_0_succn

    ltn_0_not : type:ltn_0_not

    not_leqn : type:not_leqn

    not_ltn : type:not_ltn

    leqn_iff_ltn_succn : type:leqn_iff_ltn_succn

    ltn_from_leqn_neq : type:ltn_from_leqn_neq

Strong induction for natural numbers:

    ltn_well_founded : type:ltn_well_founded


### Addition

    (* +N *)
    plusn : type:plusn

       plusn_zeron : type:plusn_zeron

       plusn_succn : type:plusn_succn

    (* an alias for plusz_zeron *)
    plusn_0_l : type:plusn_0_l

    plusn_0_r : type:plusn_0_r

    plusn_assoc : type:plusn_assoc

    plusn_shift_r : type:plusn_shift_r

    plusn_commute : type:plusn_commute

    plusn_leqn_l : type:plusn_leqn_l

    plusn_leqn_r : type:plusn_leqn_r

    plusn_leqn : type:plusn_leqn

    plusn_cancel_leqn_l : type:plusn_cancel_leqn_l

    plusn_cancel_leqn_r : type:plusn_cancel_leqn_r

    plusn_cancel_leqn_leqn_l : type:plusn_cancel_leqn_leqn_l

    plusn_cancel_leqn_leqn_r : type:plusn_cancel_leqn_leqn_r

    plusn_ltn_r : type:plusn_ltn_r

    plusn_cancel_l : type:plusn_cancel_l

    plusn_cancel_l_eq : type:plusn_cancel_l_eq

    plusn_cancel_r : type:plusn_cancel_r

    plusn_cancel_r_eq : type:plusn_cancel_r_eq

    plusn_compat : type:plusn_compat


### Subtraction

    predn : type:predn
          = def:predn

       predn_zeron : type:predn_zeron

       predn_succn : type:predn_succn

    (* -N *)
    minusn : type:minusn

       minusn_zeron : type:minusn_zeron

       minusn_succn_r : type:minusn_succn_r

    plusn_minusn_cancel_l : type:plusn_minusn_cancel_l

    plusn_minusn_cancel_r : type:plusn_minusn_cancel_r

    minusn_swap : type:minusn_swap

    minusn_plusn_cancel : type:minusn_plusn_cancel

    minusn_0_l : type:minusn_0_l

    (* an alias for minusn_zeron *)
    minusn_0_r : type:minusn_0_r

    minusn_proper : type:minusn_proper

    minusn_assoc : type:minusn_assoc

    minusn_succn : type:minusn_succn

    predn_leqn : type:predn_leqn

    minusn_leqn_l : type:minusn_leqn_l

    minusn_leqn : type:minusn_leqn

    minusn_self : type:minusn_self

    minusn_succn_l_leqn : type:minusn_succn_l_leqn

    minusn_succn_l_eq : type:minusn_succn_l_eq

    plusn_minusn_swap : type:plusn_minusn_swap

    plusn_minusn_assoc : type:plusn_minusn_assoc

    plusn_minusn_assoc_swap : type:plusn_minusn_assoc_swap

    minusn_plusn_assoc : type:minusn_plusn_assoc

    minusn_compat : type:minusn_compat


### Multiplication

    (* *N *)
    timesn : type:timesn

       timesn_zeron : type:timesn_zeron
    
       timesn_succn : type:timesn_succn

    (* an alias for timesn_zeron *)
    timesn_0_l : type:timesn_0_l

    timesn_0_r : type:timesn_0_r

    timesn_1_l : type:timesn_1_l

    timesn_1_r : type:timesn_1_r

    timesn_commute : type:timesn_commute

    timesn_assoc : type:timesn_assoc

    timesn_dist_succn_r : type:timesn_dist_succn_r

    timesn_dist_plusn_l : type:timesn_dist_plusn_l

    timesn_dist_plusn_r : type:timesn_dist_plusn_r

    timesn_leqn : type:timesn_leqn

    timesn_dist_predn_l : type:timesn_dist_predn_l

    timesn_dist_predn_r : type:timesn_dist_predn_r

    timesn_dist_minusn_l : type:timesn_dist_minusn_l

    timesn_dist_minusn_r : type:timesn_dist_minusn_r

    natural_integral_domain : type:natural_integral_domain

    timesn_compat : type:timesn_compat


### Minimum

    minn : type:minn

    minn_commute : type:minn_commute

    minn_assoc : type:minn_assoc

    minn_ann_l : type:minn_ann_l

    minn_ann_r : type:minn_ann_r

    minn_succn : type:minn_succn

    minn_leqn_l : type:minn_leqn_l

    minn_leqn_r : type:minn_leqn_r

    minn_glb : type:minn_glb

    minn_leqn : type:minn_leqn

    minn_eq_l : type:minn_eq_l

    minn_eq_r : type:minn_eq_r

    minn_idem : type:minn_idem

    plusn_dist_minn_l : type:plusn_dist_minn_l

    plusn_dist_minn_r : type:plusn_dist_minn_r


### Maximum

    maxn : type:maxn

    maxn_commute : type:maxn_commute

    maxn_assoc : type:maxn_assoc

    maxn_id_l : type:maxn_id_l

    maxn_id_r : type:maxn_id_r

    maxn_succn : type:maxn_succn

    maxn_leqn_l : type:maxn_leqn_l

    maxn_leqn_r : type:maxn_leqn_r

    maxn_lub : type:maxn_lub

    maxn_leqn : type:maxn_leqn

    maxn_eq_l : type:maxn_eq_l

    maxn_eq_r : type:maxn_eq_r

    maxn_idem : type:maxn_idem

    plusn_dist_maxn_l : type:plusn_dist_maxn_l

    plusn_dist_maxn_r : type:plusn_dist_maxn_r

    minn_dist_maxn_l : type:minn_dist_maxn_l

    minn_dist_maxn_r : type:minn_dist_maxn_r

    maxn_dist_minn_l : type:maxn_dist_minn_l

    maxn_dist_minn_r : type:maxn_dist_minn_r

    minn_maxn_same : type:minn_maxn_same

    maxn_minn_same : type:maxn_minn_same


### Effective comparisons

    eqnb : type:eqnb

    leqnb : type:leqnb

    ltnb : type:ltnb

    neqnb : type:neqnb
         = def:neqnb

    istrue_eqnb : type:istrue_eqnb

    istrue_neqnb : type:istrue_neqnb

    istrue_leqnb : type:istrue_leqnb

    istrue_ltnb : type:istrue_ltnb

    notb_eqnb : type:notb_eqnb

    notb_neqnb : type:notb_neqnb

    notb_leqnb : type:notb_leqnb

    notb_ltnb : type:notb_ltnb


### Decidability

    eq_natural_decide : type:eq_natural_decide

    neq_natural_decide : type:neq_natural_decide

    leqn_decide : type:leqn_decide

    ltn_decide : type:ltn_decide

    eq_natural_stable : type:eq_natural_stable

    neq_natural_stable : type:neq_natural_stable

    leqn_stable : type:leqn_stable

    ltn_stable : type:ltn_stable

    leqn_iff_ltn_or_eq : type:leqn_iff_ltn_or_eq

    natural_trichotomy : type:natural_trichotomy

    natural_dichotomy : type:natural_dichotomy

    natural_dichotomy_weak : type:natural_dichotomy_weak

    natural_dichotomy_neq : type:natural_dichotomy_neq


### Relation to `nat`

    nat_to_natural : type:nat_to_natural

    natural_to_nat : type:natural_to_nat

    nat_to_natural_inv : type:nat_to_natural_inv

    natural_to_nat_inv : type:natural_to_nat_inv

    nat_to_natural_mono : type:nat_to_natural_mono

    natural_to_nat_mono : type:natural_to_nat_mono

    nat_to_natural_mono_lt : type:nat_to_natural_mono_lt

    natural_to_nat_mono_lt : type:natural_to_nat_mono_lt

    plusn_to_nat : type:plusn_to_nat

    plus_to_natural : type:plus_to_natural

    minusn_to_nat : type:minusn_to_nat

    minus_to_natural : type:minus_to_natural

    timesn_to_nat : type:timesn_to_nat

    times_to_natural : type:times_to_natural

    minn_to_nat : type:minn_to_nat

    min_to_natural : type:min_to_natural

    maxn_to_nat : type:maxn_to_nat

    max_to_natural : type:max_to_natural


### Relation to `integer`

    natural_to_integer : type:natural_to_integer

    integer_to_natural : type:integer_to_natural

    natural_to_integer_inv : type:natural_to_integer_inv

    integer_to_natural_inv : type:integer_to_natural_inv

    natural_to_integer_nonneg : type:natural_to_integer_nonneg

    natural_to_integer_mono : type:natural_to_integer_mono

    natural_to_integer_mono_lt : type:natural_to_integer_mono_lt

    integer_to_natural_zero : type:integer_to_natural_zero

    integer_to_natural_succ : type:integer_to_natural_succ

    integer_to_natural_mono : type:integer_to_natural_mono

    integer_to_natural_mono_lt : type:integer_to_natural_mono_lt

    plusn_to_integer : type:plusn_to_integer

    plusz_to_natural : type:plusz_to_natural

    predn_to_integer : type:predn_to_integer

    minusn_to_integer : type:minusn_to_integer

    minusz_to_natural : type:minusz_to_natural

    timesn_to_integer : type:timesn_to_integer

    timesz_to_natural : type:timesz_to_natural

    minn_to_integer : type:minn_to_integer

    maxn_to_integer : type:maxn_to_integer

    minz_to_natural : type:minz_to_natural

    maxz_to_natural : type:maxz_to_natural
