open:Division
# `Division` (natural number division)

Since divisors must be nonzero, we define `pos` as an abbreviation
(*i.e.,* a soft constant):

    pos : type:pos
        = def:pos


### Div and Mod

    div : type:div
        =rec= defrec:div

    mod : type:mod
        =rec= defrec:mod

To save the expense of computing the recursion twice, `divmod` does
both at the same time:

    divmod : type:divmod
           =rec= defrec:divmod

    divmod_equal : type:divmod_equal

The defining properties of `div` and `mod`:

    mod_lt_r : type:mod_lt_r

    div_prop : type:div_prop

The latter, restated in two different ways:

    div_prop' : type:div_prop'

    mod_prop : type:mod_prop

The quotient and remainder are uniquely defined:

    division_property : type:division_property

    division_unique : type:division_unique

    div_leq_l : type:div_leq_l

    mod_leq_l : type:mod_leq_l

    div_times_r : type:div_times_r

    div_times_l : type:div_times_l

    mod_times_r : type:mod_times_r

    mod_times_l : type:mod_times_l

    div_0 : type:div_0

    mod_0 : type:mod_0

    div_1 : type:div_1

    mod_1 : type:mod_1

    div_self : type:div_self

    mod_self : type:mod_self

    div_operands_lt : type:div_operands_lt

    mod_operands_lt : type:mod_operands_lt

    div_mono : type:div_mono

    mod_idem : type:mod_idem

    div_plus_r : type:div_plus_r

    div_plus_l : type:div_plus_l

    mod_plus_r : type:mod_plus_r

    mod_plus_l : type:mod_plus_l

    times_div_r : type:times_div_r

    times_div_l : type:times_div_l

    div_assoc : type:div_assoc

This relates the remainders of the divisions in `div_assoc`:

    div_assoc_remainder : type:div_assoc_remainder

    mod_plus_alt : type:mod_plus_alt

    mod_plus_alt2 : type:mod_plus_alt2

    mod_times_alt : type:mod_times_alt

    mod_times_alt2 : type:mod_times_alt2

    div_times_alt : type:div_times_alt


### Divides predicate

    divides : type:divides
            = def:divides

    divides_iff_modulus : type:divides_iff_modulus

    divides_1 : type:divides_1

    divides_0 : type:divides_0

    divides_refl : type:divides_refl

    divides_trans : type:divides_trans

    divides_antisymm : type:divides_antisymm

    divides_product_r : type:divides_product_r

    divides_product_l : type:divides_product_l

    divides_plus : type:divides_plus

    divides_minus : type:divides_minus

    divides_times_times_r : type:divides_times_times_r

    divides_times_times_l : type:divides_times_times_l

    divides_times_r : type:divides_times_r

    divides_times_l : type:divides_times_l

    divides_mod : type:divides_mod

    divides_div : type:divides_div

    divides_impl_leq : type:divides_impl_leq

    modulus_implies_mod_eq : type:modulus_implies_mod_eq


### Greatest common divisor

    gcd : type:gcd
        =rec= defrec:gcd

    gcd_positive : type:gcd_positive

    gcd_divides_l : type:gcd_divides_l

    gcd_divides_r : type:gcd_divides_r

    gcd_glb : type:gcd_glb

    gcd_commute : type:gcd_commute

    gcd_assoc : type:gcd_assoc

    gcd_ann_r : type:gcd_ann_r

    gcd_ann_l : type:gcd_ann_l


### Logarithms

    exp : type:exp
        = def:exp

    exp_positive : type:exp_positive

    exp_plus : type:exp_plus

    exp_times : type:exp_times

    exp_mono_base : type:exp_mono_base

    exp_mono_exponent : type:exp_mono_exponent

    exp_mono : type:exp_mono

We arbitrarily set `log2 0 = 0`, so that `log2` can be defined for every natural number.

    log2 : type:log2
         =rec= defrec:log2

    log2_mono : type:log2_mono

    log2_one : type:log2_one

    log2_even : type:log2_even

    log2_odd : type:log2_odd

    log2_two : type:log2_two

    log2_exp_inverse : type:log2_exp_inverse

    log2_spec : type:log2_spec

    log2_unique : type:log2_unique

    log2_property : type:log2_property

    log2_lower : type:log2_lower

    log2_upper : type:log2_upper

    log2_times_leq : type:log2_times_leq


### Relation to integers

    div_to_integer : type:div_to_integer

    mod_to_integer : type:mod_to_integer
