open:Function
# `Function`

### Composition and identity

    identity : type:identity
             = def:identity

    compose : type:compose
            = def:compose

    compose_id_l : type:compose_id_l

    compose_id_r : type:compose_id_r

    compose_assoc : type:compose_assoc



### Bijections, etc.

    injective : type:injective
               = def:injective
               imp:injective

    split_injective : type:split_injective
              = def:split_injective
              imp:split_injective

Classically, every injective function with a nonempty domain is
split-injective, but constructively we cannot compute the inverse.

    surjective : type:surjective
               = def:surjective
               imp:surjective

    bijective : type:bijective
              = def:bijective
              imp:bijective

    split_injective_impl_injective : type:split_injective_impl_injective

    bijective_impl_split_injective : type:bijective_impl_split_injective

    bijective_impl_surjective : type:bijective_impl_surjective

    bijective_impl_injective : type:bijective_impl_injective

    split_injective_and_surjective_impl_bijective : type:split_injective_and_surjective_impl_bijective

    split_injective_inverse : type:split_injective_inverse

    surjective_inverse : type:surjective_inverse

    bijective_inverse : type:bijective_inverse

    injective_identity : type:injective_identity

    split_injective_identity : type:split_injective_identity

    surjective_identity : type:surjective_identity

    bijective_identity : type:bijective_identity

    injective_compose : type:injective_compose

    split_injective_compose : type:split_injective_compose

    surjective_compose : type:surjective_compose

    bijective_compose : type:bijective_compose



### Equipollence

    equipollent : type:equipollent
                = def:equipollent

    equipollent_refl : type:equipollent_refl

    eeqtp_impl_equipollent : type:eeqtp_impl_equipollent

    equipollent_symm : type:equipollent_symm

    equipollent_trans : type:equipollent_trans

    equipollent_arrow : type:equipollent_arrow

    equipollent_prod : type:equipollent_prod

    equipollent_sum : type:equipollent_sum

    equipollent_forall : type:equipollent_forall

    equipollent_exists : type:equipollent_exists

    equipollent_future : type:equipollent_future

    equipollent_set : type:equipollent_set

    equipollent_iset : type:equipollent_iset

    equipollent_set_iset : type:equipollent_set_iset

    equipollent_squash : type:equipollent_squash

    equipollent_isquash : type:equipollent_isquash

    equipollent_squash_isquash : type:equipollent_squash_isquash

    equipollent_set_constraint : type:equipollent_set_constraint

    equipollent_iset_constraint : type:equipollent_iset_constraint

    equipollent_set_elim : type:equipollent_set_elim

    equipollent_iset_elim : type:equipollent_iset_elim

    equipollent_squash_unit : type:equipollent_squash_unit

    equipollent_isquash_unit : type:equipollent_isquash_unit



### Subpollence

    subpollent : type:subpollent
                = def:subpollent

    subpollent_refl : type:subpollent_refl

    equipollent_impl_subpollent : type:equipollent_impl_subpollent

    subpollent_trans : type:subpollent_trans

Antisymmetry is the Schroeder-Bernstein theorem, which does not hold constructively.

    eeqtp_impl_subpollent : type:eeqtp_impl_subpollent

    subpollent_arrow : type:subpollent_arrow

Note that when it comes to subpollence, arrow is covariant in both arguments.

    subpollent_prod : type:subpollent_prod

    subpollent_sum : type:subpollent_sum

    subpollent_forall : type:subpollent_forall

    subpollent_exists : type:subpollent_exists

    subpollent_future : type:subpollent_future

    subpollent_set : type:subpollent_set

    subpollent_iset : type:subpollent_iset
