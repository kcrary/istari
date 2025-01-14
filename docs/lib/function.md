# `Function`

### Composition and identity

    identity : intersect (i : level) (a : U i) . a -> a
             = fn x . x

    compose : intersect (i : level) (a b c : U i) . (b -> c) -> (a -> b) -> a -> c
            = fn f g x . f (g x)

    compose_id_l : forall (i : level) (a b : U i) (f : a -> b) . compose identity f = f : (a -> b)

    compose_id_r : forall (i : level) (a b : U i) (f : a -> b) . compose f identity = f : (a -> b)

    compose_assoc : forall (i : level) (a b c d : U i) (f : c -> d) (g : b -> c) (h : a -> b) .
                       compose (compose f g) h = compose f (compose g h) : (a -> d)



### Bijections, etc.

    one_to_one : intersect (i : level) . forall (a b : U i) . (a -> b) -> U i
               = fn a b f . forall (x y : a) . f x = f y : b -> x = y : a
               (2 implicit arguments)

    injective : intersect (i : level) . forall (a b : U i) . (a -> b) -> U i
              = fn a b f . exists (g : b -> a) . forall (x : a) . g (f x) = x : a
              (2 implicit arguments)

Although `one-to-one` and `injective` are classically equivalent,
injectivity has computational content while one-to-one does not.

    surjective : intersect (i : level) . forall (a b : U i) . (a -> b) -> U i
               = fn a b f . exists (g : b -> a) . forall (x : b) . f (g x) = x : b
               (2 implicit arguments)

    bijective : intersect (i : level) . forall (a b : U i) . (a -> b) -> U i
              = fn a b f .
                   exists (g : b -> a) .
                     (forall (x : a) . g (f x) = x : a) & (forall (x : b) . f (g x) = x : b)
              (2 implicit arguments)

    injective_impl_one_to_one : forall (i : level) (a b : U i) (f : a -> b) .
                                   injective f -> one_to_one f

    bijective_impl_injective : forall (i : level) (a b : U i) (f : a -> b) .
                                  bijective f -> injective f

    bijective_impl_surjective : forall (i : level) (a b : U i) (f : a -> b) .
                                   bijective f -> surjective f

    bijective_impl_one_to_one : forall (i : level) (a b : U i) (f : a -> b) .
                                   bijective f -> one_to_one f

    injective_and_surjective_impl_bijective : forall (i : level) (a b : U i) (f : a -> b) .
                                                 injective f -> surjective f -> bijective f

    injective_inverse : forall (i : level) (a b : U i) (f : a -> b) .
                           injective f
                           -> exists (g : b -> a) .
                                surjective g & compose g f = identity : (a -> a)

    surjective_inverse : forall (i : level) (a b : U i) (f : a -> b) .
                            surjective f
                            -> exists (g : b -> a) .
                                 injective g & compose f g = identity : (b -> b)

    bijective_inverse : forall (i : level) (a b : U i) (f : a -> b) .
                           bijective f
                           -> exists (g : b -> a) .
                                bijective g
                                & compose g f = identity : (a -> a)
                                & compose f g = identity : (b -> b)

    one_to_one_identity : forall (i : level) (a : U i) . one_to_one identity

    injective_identity : forall (i : level) (a : U i) . injective identity

    surjective_identity : forall (i : level) (a : U i) . surjective identity

    bijective_identity : forall (i : level) (a : U i) . bijective identity

    one_to_one_compose : forall (i : level) (a b c : U i) (f : b -> c) (g : a -> b) .
                            one_to_one f -> one_to_one g -> one_to_one (compose f g)

    injective_compose : forall (i : level) (a b c : U i) (f : b -> c) (g : a -> b) .
                           injective f -> injective g -> injective (compose f g)

    surjective_compose : forall (i : level) (a b c : U i) (f : b -> c) (g : a -> b) .
                            surjective f -> surjective g -> surjective (compose f g)

    bijective_compose : forall (i : level) (a b c : U i) (f : b -> c) (g : a -> b) .
                           bijective f -> bijective g -> bijective (compose f g)

