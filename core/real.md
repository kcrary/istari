open:Real
overload:real
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

    real : type:real

    nonzero_real : type:nonzero_real
                 = def:nonzero_real


### Inequalities

    (* <r *)
    ltr : type:ltr

    (* <r= *)
    leqr : type:leqr
         = def:leqr

    ltr_inhabitant : type:ltr_inhabitant

    leqr_inhabitant : type:leqr_inhabitant

    ltr_ext : type:ltr_ext

    leqr_ext : type:leqr_ext

    ltr_impl_leqr : type:ltr_impl_leqr
    
    ltr_irrefl : type:ltr_irrefl
    
    ltr_impl_neq : type:ltr_impl_neq
    
    leqr_refl : type:leqr_refl
    
    leqr_refl' : type:leqr_refl'
    
    leqr_antisymm : type:leqr_antisymm
    
    leqr_ltr_trans : type:leqr_ltr_trans
    
    ltr_leqr_trans : type:ltr_leqr_trans
    
    ltr_trans : type:ltr_trans
    
    leqr_trans : type:leqr_trans
    
This one gives transitivity in the form needed for rewriting:

    leqr_implication : type:leqr_implication

    ltr_implication : type:ltr_implication

    not_leqr : type:not_leqr
    
    not_ltr : type:not_ltr
    
    ltr_from_leqr_neq : type:ltr_from_leqr_neq

These lemmas are convenient for rewriting under `invr`:

    eq_nonzero_real : type:eq_nonzero_real

    eq_nonzero_real' : type:eq_nonzero_real'


### Plus and negation

    (* +r *)
    plusr : type:plusr
    
    (* ~r *)
    negr : type:negr
    
    (* -r *)
    minusr : type:minusr
           = def:minusr


    plusr_commute : type:plusr_commute
    
    plusr_assoc : type:plusr_assoc
    
    minusr_assoc : type:minusr_assoc
    
    plusr_minusr_assoc : type:plusr_minusr_assoc
    
    minusr_plusr_assoc : type:minusr_plusr_assoc
    
    plusr_id_l : type:plusr_id_l
    
    plusr_id_r : type:plusr_id_r
    
    minusr_id_l : type:minusr_id_l
    
    minusr_id_r : type:minusr_id_r
    
    plusr_inverse_l : type:plusr_inverse_l
    
    plusr_inverse_r : type:plusr_inverse_r
    
    negr_invol : type:negr_invol
    
    negr_injective : type:negr_injective
    
    negr_plusr : type:negr_plusr
    
    negr_minusr : type:negr_minusr
    
    minusr_self : type:minusr_self
    
    plusr_commute3 : type:plusr_commute3
    
    plusr_rotate : type:plusr_rotate
    
    plusr_rotate4 : type:plusr_rotate4

    plusr_cancel_l : type:plusr_cancel_l

    plusr_cancel_r : type:plusr_cancel_r

In each of the `plusr` and `timesr` shift lemmas, the negation/inverse
term is the on the right of the `<->`.  Then the first letter
indicates which direction the negated/inverted term is moving, the
second indicates which operand it is before moving, and the third is
which operand it is after moving.

    plusr_shift_lll : type:plusr_shift_lll

    plusr_shift_lrr : type:plusr_shift_lrr

    plusr_shift_llr : type:plusr_shift_llr

    plusr_shift_lrl : type:plusr_shift_lrl

    plusr_shift_rrr : type:plusr_shift_rrr

    plusr_shift_rll : type:plusr_shift_rll

    plusr_shift_rlr : type:plusr_shift_rlr

    plusr_shift_rrl : type:plusr_shift_rrl

    negr_minusr : type:negr_minusr

    minusr_cancel_r : type:minusr_cancel_r

    minusr_cancel_l : type:minusr_cancel_l

In each of the `minusr` shift lemmas, the subtraction term is on the
right of the `<->`.  Then the first letter indicates which direction
the subtrahend is moving, the second indicates which operand it is
before moving.  It is always the right-hand operand after moving.

    minusr_shift_ll : type:minusr_shift_ll

    minusr_shift_lr : type:minusr_shift_lr

    minusr_shift_rr : type:minusr_shift_rr

    minusr_shift_rl : type:minusr_shift_rl

    plusr_compat : type:plusr_compat

    minusr_compat : type:minusr_compat

    negr_compat : type:negr_compat

    plusr_ltr : type:plusr_ltr

    plusr_leqr : type:plusr_leqr

    plusr_ltr_l : type:plusr_ltr_l

    plusr_ltr_r : type:plusr_ltr_r

    negr_ltr : type:negr_ltr

    negr_ltr' : type:negr_ltr'

    negr_leqr : type:negr_leqr

    negr_leqr' : type:negr_leqr'

    plusr_cancel_leqr_l : type:plusr_cancel_leqr_l

    plusr_cancel_leqr_r : type:plusr_cancel_leqr_r

    plusr_cancel_leqr_leqr_l : type:plusr_cancel_leqr_leqr_l

    plusr_cancel_leqr_leqr_r : type:plusr_cancel_leqr_leqr_r

    plusr_shift_leqr_lll : type:plusr_shift_leqr_lll

    plusr_shift_leqr_lrr : type:plusr_shift_leqr_lrr

    plusr_shift_leqr_llr : type:plusr_shift_leqr_llr

    plusr_shift_leqr_lrl : type:plusr_shift_leqr_lrl

    plusr_shift_leqr_rrr : type:plusr_shift_leqr_rrr

    plusr_shift_leqr_rll : type:plusr_shift_leqr_rll

    plusr_shift_leqr_rlr : type:plusr_shift_leqr_rlr

    plusr_shift_leqr_rrl : type:plusr_shift_leqr_rrl

    plusr_cancel_ltr_l : type:plusr_cancel_ltr_l

    plusr_cancel_ltr_r : type:plusr_cancel_ltr_r

    plusr_shift_ltr_lll : type:plusr_shift_ltr_lll

    plusr_shift_ltr_lrr : type:plusr_shift_ltr_lrr

    plusr_shift_ltr_llr : type:plusr_shift_ltr_llr

    plusr_shift_ltr_lrl : type:plusr_shift_ltr_lrl

    plusr_shift_ltr_rrr : type:plusr_shift_ltr_rrr

    plusr_shift_ltr_rll : type:plusr_shift_ltr_rll

    plusr_shift_ltr_rlr : type:plusr_shift_ltr_rlr

    plusr_shift_ltr_rrl : type:plusr_shift_ltr_rrl

    minusr_leqr : type:minusr_leqr

    minusr_cancel_leqr_l : type:minusr_cancel_leqr_l

    minusr_cancel_leqr_r : type:minusr_cancel_leqr_r

    minusr_cancel_ltr_l : type:minusr_cancel_ltr_l

    minusr_cancel_ltr_r : type:minusr_cancel_ltr_r

    minusr_shift_leqr_ll : type:minusr_shift_leqr_ll

    minusr_shift_leqr_lr : type:minusr_shift_leqr_lr

    minusr_shift_leqr_rr : type:minusr_shift_leqr_rr

    minusr_shift_leqr_rl : type:minusr_shift_leqr_rl

    minusr_shift_ltr_ll : type:minusr_shift_ltr_ll

    minusr_shift_ltr_lr : type:minusr_shift_ltr_lr

    minusr_shift_ltr_rr : type:minusr_shift_ltr_rr

    minusr_shift_ltr_rl : type:minusr_shift_ltr_rl

    minusr_swap : type:minusr_swap

    plusr_minusr_swap : type:plusr_minusr_swap

    plusr_minusr_cancel_r : type:plusr_minusr_cancel_r

    plusr_minusr_cancel_l : type:plusr_minusr_cancel_l

    negr_zero : type:negr_zero

    negr_nonzero : type:negr_nonzero


### Times and inverse

    (* *r *)
    timesr : type:timesr

    invr : type:invr

    (* |r *)
    divr : type:divr
         = def:divr


    timesr_commute : type:timesr_commute

    timesr_assoc : type:timesr_assoc

    divr_assoc : type:divr_assoc

    timesr_divr_assoc : type:timesr_divr_assoc

    divr_timesr_assoc : type:divr_timesr_assoc

    timesr_id_l : type:timesr_id_l

    timesr_id_r : type:timesr_id_r

    divr_id_l : type:divr_id_l

    divr_id_r : type:divr_id_r

    timesr_inverse_l : type:timesr_inverse_l

    timesr_inverse_r : type:timesr_inverse_r

    invr_nonzero : type:invr_nonzero

    invr_invol : type:invr_invol

    invr_timesr : type:invr_timesr

    invr_injective : type:invr_injective

    real_integral_domain : type:real_integral_domain

    timesr_neq_zero : type:timesr_neq_zero

    timesr_neq_zero_invert : type:timesr_neq_zero_invert

    timesr_ltr_zero_invert : type:timesr_ltr_zero_invert

    timesr_ltr_zero_invert_neg : type:timesr_ltr_zero_invert_neg

    square_nonnegative : type:square_nonnegative

    invr_positive : type:invr_positive

    invr_negative : type:invr_negative

    divr_self : type:divr_self

    timesr_commute3 : type:timesr_commute3

    timesr_rotate : type:timesr_rotate

    timesr_rotate4 : type:timesr_rotate4

    timesr_cancel_l : type:timesr_cancel_l

    timesr_cancel_r : type:timesr_cancel_r

    timesr_shift_lll : type:timesr_shift_lll

    timesr_shift_lrr : type:timesr_shift_lrr

    timesr_shift_llr : type:timesr_shift_llr

    timesr_shift_lrl : type:timesr_shift_lrl

    timesr_shift_rrr : type:timesr_shift_rrr

    timesr_shift_rll : type:timesr_shift_rll

    timesr_shift_rlr : type:timesr_shift_rlr

    timesr_shift_rrl : type:timesr_shift_rrl

    divr_cancel_l : type:divr_cancel_l

    divr_cancel_r : type:divr_cancel_r

    divr_shift_ll : type:divr_shift_ll

    divr_shift_lr : type:divr_shift_lr

    divr_shift_rr : type:divr_shift_rr

    divr_shift_rl : type:divr_shift_rl

    timesr_compat : type:timesr_compat

    invr_compat : type:invr_compat

    timesr_leqr : type:timesr_leqr

    (* an alias for timesr_leqr *)
    timesr_leqr_pos_pos : type:timesr_leqr_pos_pos

    timesr_leqr_neg_neg : type:timesr_leqr_neg_neg

    timesr_leqr_pos_neg : type:timesr_leqr_pos_neg

    timesr_leqr_neg_neg : type:timesr_leqr_neg_neg

    timesr_leqr_zero : type:timesr_leqr_zero

    (* an alias for timesq_leqq_zero *)
    timesr_leqr_zero_pos_pos : type:timesr_leqr_zero_pos_pos

    timesr_leqr_zero_pos_neg : type:timesr_leqr_zero_pos_neg

    timesr_leqr_zero_neg_pos : type:timesr_leqr_zero_neg_pos

    timesr_leqr_zero_neg_neg : type:timesr_leqr_zero_neg_neg

    timesr_leqr_l : type:timesr_leqr_l

    timesr_leqr_r : type:timesr_leqr_r

    timesr_leqr_l_neg : type:timesr_leqr_l_neg

    timesr_leqr_r_neg : type:timesr_leqr_r_neg

    timesr_ltr_leqr : type:timesr_ltr_leqr

    timesr_leqr_ltr : type:timesr_leqr_ltr

    timesr_ltr : type:timesr_ltr

    timesr_ltr_l : type:timesr_ltr_l

    timesr_ltr_r : type:timesr_ltr_r

    timesr_ltr_l_neg : type:timesr_ltr_l_neg

    timesr_ltr_r_neg : type:timesr_ltr_r_neg

    timesr_ltr_zero : type:timesr_ltr_zero

    (* an alias for timesr_ltr_zero *)
    timesr_ltr_zero_pos_pos : type:timesr_ltr_zero_pos_pos

    timesr_ltr_zero_pos_neg : type:timesr_ltr_zero_pos_neg

    timesr_ltr_zero_neg_pos : type:timesr_ltr_zero_neg_pos

    timesr_ltr_zero_neg_neg : type:timesr_ltr_zero_neg_neg

    timesr_cancel_leqr_l : type:timesr_cancel_leqr_l

    timesr_cancel_leqr_r : type:timesr_cancel_leqr_r

    timesr_cancel_ltr_l : type:timesr_cancel_ltr_l

    timesr_cancel_ltr_r : type:timesr_cancel_ltr_r

    timesr_cancel_leqr_l_neg : type:timesr_cancel_leqr_l_neg

    timesr_cancel_leqr_r_neg : type:timesr_cancel_leqr_r_neg

    timesr_cancel_ltr_l_neg : type:timesr_cancel_ltr_l_neg

    timesr_cancel_ltr_r_neg : type:timesr_cancel_ltr_r_neg

    timesr_shift_leqr_lll : type:timesr_shift_leqr_lll

    timesr_shift_leqr_lrr : type:timesr_shift_leqr_lrr

    timesr_shift_leqr_llr : type:timesr_shift_leqr_llr

    timesr_shift_leqr_lrl : type:timesr_shift_leqr_lrl

    timesr_shift_leqr_rrr : type:timesr_shift_leqr_rrr

    timesr_shift_leqr_rll : type:timesr_shift_leqr_rll

    timesr_shift_leqr_rlr : type:timesr_shift_leqr_rlr

    timesr_shift_leqr_rrl : type:timesr_shift_leqr_rrl

    timesr_shift_ltr_lll : type:timesr_shift_ltr_lll

    timesr_shift_ltr_lrr : type:timesr_shift_ltr_lrr

    timesr_shift_ltr_llr : type:timesr_shift_ltr_llr

    timesr_shift_ltr_lrl : type:timesr_shift_ltr_lrl

    timesr_shift_ltr_rrr : type:timesr_shift_ltr_rrr

    timesr_shift_ltr_rll : type:timesr_shift_ltr_rll

    timesr_shift_ltr_rlr : type:timesr_shift_ltr_rlr

    timesr_shift_ltr_rrl : type:timesr_shift_ltr_rrl

In the negative multiplicative shifts, the naming is as though the
inequality did not reverse on the right.

    timesr_shift_leqr_lll_neg : type:timesr_shift_leqr_lll_neg

    timesr_shift_leqr_lrr_neg : type:timesr_shift_leqr_lrr_neg

    timesr_shift_leqr_llr_neg : type:timesr_shift_leqr_llr_neg

    timesr_shift_leqr_lrl_neg : type:timesr_shift_leqr_lrl_neg

    timesr_shift_leqr_rrr_neg : type:timesr_shift_leqr_rrr_neg

    timesr_shift_leqr_rll_neg : type:timesr_shift_leqr_rll_neg

    timesr_shift_leqr_rlr_neg : type:timesr_shift_leqr_rlr_neg

    timesr_shift_leqr_rrl_neg : type:timesr_shift_leqr_rrl_neg

    timesr_shift_ltr_lll_neg : type:timesr_shift_ltr_lll_neg

    timesr_shift_ltr_lrr_neg : type:timesr_shift_ltr_lrr_neg

    timesr_shift_ltr_llr_neg : type:timesr_shift_ltr_llr_neg

    timesr_shift_ltr_lrl_neg : type:timesr_shift_ltr_lrl_neg

    timesr_shift_ltr_rrr_neg : type:timesr_shift_ltr_rrr_neg

    timesr_shift_ltr_rll_neg : type:timesr_shift_ltr_rll_neg

    timesr_shift_ltr_rlr_neg : type:timesr_shift_ltr_rlr_neg

    timesr_shift_ltr_rrl_neg : type:timesr_shift_ltr_rrl_neg

    divr_shift_leqr_ll : type:divr_shift_leqr_ll

    divr_shift_leqr_lr : type:divr_shift_leqr_lr

    divr_shift_leqr_rr : type:divr_shift_leqr_rr

    divr_shift_leqr_rl : type:divr_shift_leqr_rl

    divr_shift_ltr_ll : type:divr_shift_ltr_ll

    divr_shift_ltr_lr : type:divr_shift_ltr_lr

    divr_shift_ltr_rr : type:divr_shift_ltr_rr

    divr_shift_ltr_rl : type:divr_shift_ltr_rl

    divr_shift_leqr_ll_neg : type:divr_shift_leqr_ll_neg

    divr_shift_leqr_lr_neg : type:divr_shift_leqr_lr_neg

    divr_shift_leqr_rr_neg : type:divr_shift_leqr_rr_neg

    divr_shift_leqr_rl_neg : type:divr_shift_leqr_rl_neg

    divr_shift_ltr_ll_neg : type:divr_shift_ltr_ll_neg

    divr_shift_ltr_lr_neg : type:divr_shift_ltr_lr_neg

    divr_shift_ltr_rr_neg : type:divr_shift_ltr_rr_neg

    divr_shift_ltr_rl_neg : type:divr_shift_ltr_rl_neg

    divr_leqr_zero : type:divr_leqr_zero

    (* an alias for divr_leq_zero *)
    divr_leqr_zero_pos_pos : type:divr_leqr_zero_pos_pos
    
    divr_leqr_zero_pos_neg : type:divr_leqr_zero_pos_neg

    divr_leqr_zero_neg_pos : type:divr_leqr_zero_neg_pos

    divr_leqr_zero_neg_neg : type:divr_leqr_zero_neg_neg

    divr_ltr_zero : type:divr_ltr_zero

    (* an alias for divr_leq_zero *)
    divr_ltr_zero_pos_pos : type:divr_ltr_zero_pos_pos

    divr_ltr_zero_pos_neg : type:divr_ltr_zero_pos_neg

    divr_ltr_zero_neg_pos : type:divr_ltr_zero_neg_pos

    divr_ltr_zero_neg_neg : type:divr_ltr_zero_neg_neg

    invr_leqr_pos : type:invr_leqr_pos

    invr_leqr_neg : type:invr_leqr_neg

    invr_ltr_pos : type:invr_ltr_pos

    invr_ltr_neg : type:invr_ltr_neg

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

    invr_leqr_samesign : type:invr_leqr_samesign

    invr_ltr_samesign : type:invr_ltr_samesign

    invr_one : type:invr_one


### Distributivity

    timesr_dist_plusr_r : type:timesr_dist_plusr_r

    timesr_dist_plusr_l : type:timesr_dist_plusr_l

    timesr_ann_l : type:timesr_ann_l

    timesr_ann_r : type:timesr_ann_r

    plusr_self : type:plusr_self

    negr_as_timesr : type:negr_as_timesr

    negr_dist_timesr_l : type:negr_dist_timesr_l

    negr_dist_timesr_r : type:negr_dist_timesr_r

    timesr_dist_minusr_r : type:timesr_dist_minusr_r

    timesr_dist_minusr_l : type:timesr_dist_minusr_l

    negr_dist_invr : type:negr_dist_invr

    negr_dist_divr_l : type:negr_dist_divr_l

    negr_dist_divr_r : type:negr_dist_divr_r


### Relation to rationals

    rational_to_real : type:rational_to_real


    rational_to_real_injective : type:rational_to_real_injective

    rational_to_real_neq : type:rational_to_real_neq

    rational_to_real_nonzero : type:rational_to_real_nonzero

    rational_to_real_mono : type:rational_to_real_mono

    rational_to_real_mono_conv : type:rational_to_real_mono_conv

    rational_to_real_mono_lt : type:rational_to_real_mono_lt

    rational_to_real_mono_lt_conv : type:rational_to_real_mono_lt_conv

    plusq_to_real : type:plusq_to_real

    negq_to_real : type:negq_to_real

    minusq_to_real : type:minusq_to_real

    timesq_to_real : type:timesq_to_real

    invq_to_real : type:invq_to_real

    divq_to_real : type:divq_to_real


### Relation to integers

    integer_to_real : type:integer_to_real
                    = def:integer_to_real

    integer_to_real_injective : type:integer_to_real_injective

    integer_to_real_neq : type:integer_to_real_neq

    integer_to_real_nonzero : type:integer_to_real_nonzero

    integer_to_real_mono : type:integer_to_real_mono

    integer_to_real_mono_conv : type:integer_to_real_mono_conv

    integer_to_real_mono_lt : type:integer_to_real_mono_lt

    integer_to_real_mono_lt_conv : type:integer_to_real_mono_lt_conv

    plusz_to_real : type:plusz_to_real

    negz_to_real : type:negz_to_real

    minusz_to_real : type:minusz_to_real

    timesz_to_real : type:timesz_to_real


### Relation to natural numbers

    nat_to_real : type:nat_to_real
                = def:nat_to_real

    nat_to_real_injective : type:nat_to_real_injective

    nat_to_real_neq : type:nat_to_real_neq

    nat_to_real_nonzero : type:nat_to_real_nonzero

    nat_to_real_mono : type:nat_to_real_mono

    nat_to_real_mono_conv : type:nat_to_real_mono_conv

    nat_to_real_mono_lt : type:nat_to_real_mono_lt

    nat_to_real_mono_lt_conv : type:nat_to_real_mono_lt_conv

    plus_to_real : type:plus_to_real

    times_to_real : type:times_to_real


### Significant numbers

    ltr_0_1 : type:ltr_0_1

    leqr_0_1 : type:leqr_0_1

    neqr_0_1 : type:neqr_0_1

    ltr_neg1_0 : type:ltr_neg1_0

    leqr_neg1_0 : type:leqr_neg1_0

    neqr_neg1_0 : type:neqr_neg1_0

    negr_one : type:negr_one

    negr_minus_one : type:negr_minus_one


### Stability and limited decidability

    eq_real_stable : type:eq_real_stable

    ltr_stable : type:ltr_stable

    leqr_stable : type:leqr_stable

    ltr_sqstable : type:ltr_sqstable

    leqr_sqstable : type:leqr_sqstable

    real_dichotomy_neq : type:real_dichotomy_neq

    real_trichotomy_if_stable : type:real_trichotomy_if_stable

    real_dichotomy_if_stable : type:real_dichotomy_if_stable

    real_dichotomy_weak_if_stable : type:real_dichotomy_weak_if_stable

These lemmas (and others) require a [`squish`](squish.html) in their
result, since the disjunct returned can depend on the representations
of their inputs:

    plusr_positive_invert : type:plusr_positive_invert

    plusr_positive_invert_squash : type:plusr_positive_invert_squash

    overlapping_ranges : type:overlapping_ranges

    overlapping_ranges_squash : type:overlapping_ranges_squash


### Absolute value

    absr : type:absr


    absr_nonneg : type:absr_nonneg

    absr_of_nonneg : type:absr_of_nonneg

    absr_of_nonpos : type:absr_of_nonpos

    absr_negr : type:absr_negr

    absr_timesr : type:absr_timesr

    absr_plusr_leqr : type:absr_plusr_leqr

    absr_minusr_leqr : type:absr_minusr_leqr

    absr_preserves_nonzero : type:absr_preserves_nonzero

    absr_ub : type:absr_ub

    absr_idem : type:absr_idem

    absr_invr : type:absr_invr

    absr_zero : type:absr_zero

    absr_one : type:absr_one

    absr_minus_one : type:absr_minus_one

    absr_positive_iff_nonzero : type:absr_positive_iff_nonzero

    absr_minusr_commute : type:absr_minusr_commute

    absr_minusr_upper_bound : type:absr_minusr_upper_bound

    absr_minusr_lower_bound : type:absr_minusr_lower_bound

    absr_minusr_absr : type:absr_minusr_absr

    absr_minusr_leqr_lower : type:absr_minusr_leqr_lower

    absq_to_real : type:absq_to_real

    absz_to_real : type:absz_to_real


### Maximum and minimum

    maxr : type:maxr

    minr : type:minr
         = def:minr


    maxr_commute : type:maxr_commute

    minr_commute : type:minr_commute

    maxr_assoc : type:maxr_assoc

    minr_assoc : type:minr_assoc

    maxr_leq_l : type:maxr_leq_l

    maxr_leq_r : type:maxr_leq_r

    minr_leq_l : type:minr_leq_l

    minr_leq_r : type:minr_leq_r

    maxr_lub : type:maxr_lub

    minr_glb : type:minr_glb

    maxr_lub_strict : type:maxr_lub_strict

    minr_glb_strict : type:minr_glb_strict

    maxr_eq_l : type:maxr_eq_l

    maxr_eq_r : type:maxr_eq_r

    minr_eq_l : type:minr_eq_l

    minr_eq_r : type:minr_eq_r

    negr_maxr : type:negr_maxr

    minr_as_maxr : type:minr_as_maxr

    negr_minr : type:negr_minr

    minr_as_maxr : type:minr_as_maxr

    maxr_idem : type:maxr_idem

    minr_idem : type:minr_idem

    minr_dist_maxr_l : type:minr_dist_maxr_l

    minr_dist_maxr_r : type:minr_dist_maxr_r

    maxr_dist_minr_l : type:maxr_dist_minr_l

    maxr_dist_minr_r : type:maxr_dist_minr_r

    plusr_dist_minr_l : type:plusr_dist_minr_l

    plusr_dist_minr_r : type:plusr_dist_minr_r

    plusr_dist_maxr_l : type:plusr_dist_maxr_l

    plusr_dist_maxr_r : type:plusr_dist_maxr_r

    absr_minusr_maxr : type:absr_minusr_maxr

    maxq_to_real : type:maxq_to_real

    minq_to_real : type:minq_to_real

    maxz_to_real : type:maxz_to_real

    minz_to_real : type:minz_to_real


### Miscellaneous

    rational_dense_within_real : type:rational_dense_within_real

    rational_dense_within_real_squash : type:rational_dense_within_real_squash

    real_upper_bound : type:real_upper_bound

    real_upper_bound_squash : type:real_upper_bound_squash

    real_upper_bound_nat : type:real_upper_bound_nat

    real_upper_bound_nat_squash : type:real_upper_bound_nat_squash

    infinitely_close : type:infinitely_close

    real_total : type:real_total

    real_strict : type:real_strict


### Prereals

A few lemmas require the inputs' unquotiented representation to
produce a deterministic result.

    prereal : type:prereal

    realintro : type:realintro

    real_to_prereal : type:real_to_prereal

    real_to_prereal_squash : type:real_to_prereal_squash

    real_sequence_to_prereal_sequence : type:real_sequence_to_prereal_sequence

    real_sequence_to_prereal_sequence_squash : type:real_sequence_to_prereal_sequence_squash

    rational_to_prereal : type:rational_to_prereal

    integer_to_prereal : type:integer_to_prereal
                       = def:integer_to_prereal

    preplusr : type:preplusr

    prenegr : type:prenegr

    pretimesr : type:pretimesr

    preinvr : type:preinvr

    rational_to_prereal_to_real : type:rational_to_prereal_to_real

    integer_to_prereal_to_real : type:integer_to_prereal_to_real

    preplusr_to_real : type:preplusr_to_real

    prenegr_to_real : type:prenegr_to_real

    pretimesr_to_real : type:pretimesr_to_real

    preinvr_to_real : type:preinvr_to_real

    plusq_to_prereal : type:plusq_to_prereal

    negq_to_prereal : type:negq_to_prereal

    timesq_to_prereal : type:timesq_to_prereal

    invq_to_prereal : type:invq_to_prereal

    plusz_to_prereal : type:plusz_to_prereal

    negz_to_prereal : type:negz_to_prereal

    timesz_to_prereal : type:timesz_to_prereal

    plusr_positive_invert_prereal : type:plusr_positive_invert_prereal

    overlapping_ranges_prereal : type:overlapping_ranges_prereal

    rational_dense_within_real_prereal : type:rational_dense_within_real_prereal

    real_upper_bound_prereal : type:real_upper_bound_prereal

    real_upper_bound_nat_prereal : type:real_upper_bound_nat_prereal

---

[1] Errett Bishop and Douglas Bridges.  *Constructive Analysis.*
Springer, 1985.
