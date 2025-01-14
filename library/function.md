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

    one_to_one : type:one_to_one
               = def:one_to_one
               imp:one_to_one

    injective : type:injective
              = def:injective
              imp:injective

Although `one-to-one` and `injective` are classically equivalent,
injectivity has computational content while one-to-one does not.

    surjective : type:surjective
               = def:surjective
               imp:surjective

    bijective : type:bijective
              = def:bijective
              imp:bijective

    injective_impl_one_to_one : type:injective_impl_one_to_one

    bijective_impl_injective : type:bijective_impl_injective

    bijective_impl_surjective : type:bijective_impl_surjective

    bijective_impl_one_to_one : type:bijective_impl_one_to_one

    injective_and_surjective_impl_bijective : type:injective_and_surjective_impl_bijective

    injective_inverse : type:injective_inverse

    surjective_inverse : type:surjective_inverse

    bijective_inverse : type:bijective_inverse

    one_to_one_identity : type:one_to_one_identity

    injective_identity : type:injective_identity

    surjective_identity : type:surjective_identity

    bijective_identity : type:bijective_identity

    one_to_one_compose : type:one_to_one_compose

    injective_compose : type:injective_compose

    surjective_compose : type:surjective_compose

    bijective_compose : type:bijective_compose

