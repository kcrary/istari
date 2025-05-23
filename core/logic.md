open:Logic
# `Logic`

### Negation

    not : type:not
        = def:not

    not_inhabitant : type:not_inhabitant

    not_compat_arrow : type:not_compat_arrow


### If-and-only-if

    iff : type:iff
        = def:iff

    iff_refl : type:iff_refl

    iff_refl' : type:iff_refl'

    iff_symm : type:iff_symm

    iff_trans : type:iff_trans

    iff_compat : type:iff_compat

    iff_compat_1 : type:iff_compat_1

    iff_compat_2 : type:iff_compat_2

    not_compat_iff : type:not_compat_iff

    prod_compat_iff : type:prod_compat_iff

    sum_compat_iff : type:sum_compat_iff


##### Rewriting propositions

    prod_commute : type:prod_commute

    prod_assoc : type:prod_assoc

    prod_id_l : type:prod_id_l

    prod_id_r : type:prod_id_r

    prod_ann_l : type:prod_ann_l

    prod_ann_r : type:prod_ann_r

    sum_commute : type:sum_commute

    sum_assoc : type:sum_assoc

    sum_id_l : type:sum_id_l

    sum_id_r : type:sum_id_r

    sum_ann_l : type:sum_ann_l

    sum_ann_r : type:sum_ann_r

    true_iff_unit : type:true_iff_unit

    false_iff_void : type:false_iff_void


### Equality

    eq_refl : type:eq_refl

    eq_symm : type:eq_symm

    eq_symm_iff : type:eq_symm_iff

    eq_trans : type:eq_trans


### Not equal

    (* != *)
    neq : type:neq
        = def:neq

    neq_symm : type:neq_symm

    neq_symm_iff : type:neq_symm_iff


### Transport

In Istari's type theory, if the types `A` and `B` are equal, the
members of `A` are also members of `B`.  It is not type-theoretically
necessary to transport terms from `A` to `B`.  However, putting an
explicit transport into a term can make things easier for the
typechecker.

    transport : type:transport
              = def:transport
              imp:transport              

Note that `transport` can be folded into or out of existence, as
desired.

    subtransport : type:subtransport
                 = def:subtransport
                 imp:subtransport              


### Constructive choice

    function_description : type:function_description

    function_description_nondep : type:function_description_nondep
