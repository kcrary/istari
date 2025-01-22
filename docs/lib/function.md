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

    injective : intersect (i : level) . forall (a b : U i) . (a -> b) -> U i
               = fn a b f . forall (x y : a) . f x = f y : b -> x = y : a
               (2 implicit arguments)

    split_injective : intersect (i : level) . forall (a b : U i) . (a -> b) -> U i
              = fn a b f . exists (g : b -> a) . forall (x : a) . g (f x) = x : a
              (2 implicit arguments)

Classically, every injective function with a nonempty domain is
split-injective, but constructively we cannot compute the inverse.

    surjective : intersect (i : level) . forall (a b : U i) . (a -> b) -> U i
               = fn a b f . exists (g : b -> a) . forall (x : b) . f (g x) = x : b
               (2 implicit arguments)

    bijective : intersect (i : level) . forall (a b : U i) . (a -> b) -> U i
              = fn a b f .
                   exists (g : b -> a) .
                     (forall (x : a) . g (f x) = x : a) & (forall (x : b) . f (g x) = x : b)
              (2 implicit arguments)

    split_injective_impl_injective : forall (i : level) (a b : U i) (f : a -> b) .
                                        split_injective f -> injective f

    bijective_impl_split_injective : forall (i : level) (a b : U i) (f : a -> b) .
                                        bijective f -> split_injective f

    bijective_impl_surjective : forall (i : level) (a b : U i) (f : a -> b) .
                                   bijective f -> surjective f

    bijective_impl_injective : forall (i : level) (a b : U i) (f : a -> b) .
                                  bijective f -> injective f

    split_injective_and_surjective_impl_bijective : forall (i : level) (a b : U i) (f : a -> b) .
                                                       split_injective f
                                                       -> surjective f
                                                       -> bijective f

    split_injective_inverse : forall (i : level) (a b : U i) (f : a -> b) .
                                 split_injective f
                                 -> exists (g : b -> a) .
                                      surjective g & compose g f = identity : (a -> a)

    surjective_inverse : forall (i : level) (a b : U i) (f : a -> b) .
                            surjective f
                            -> exists (g : b -> a) .
                                 split_injective g & compose f g = identity : (b -> b)

    bijective_inverse : forall (i : level) (a b : U i) (f : a -> b) .
                           bijective f
                           -> exists (g : b -> a) .
                                bijective g
                                & compose g f = identity : (a -> a)
                                & compose f g = identity : (b -> b)

    injective_identity : forall (i : level) (a : U i) . injective identity

    split_injective_identity : forall (i : level) (a : U i) . split_injective identity

    surjective_identity : forall (i : level) (a : U i) . surjective identity

    bijective_identity : forall (i : level) (a : U i) . bijective identity

    injective_compose : forall (i : level) (a b c : U i) (f : b -> c) (g : a -> b) .
                           injective f -> injective g -> injective (compose f g)

    split_injective_compose : forall (i : level) (a b c : U i) (f : b -> c) (g : a -> b) .
                                 split_injective f
                                 -> split_injective g
                                 -> split_injective (compose f g)

    surjective_compose : forall (i : level) (a b c : U i) (f : b -> c) (g : a -> b) .
                            surjective f -> surjective g -> surjective (compose f g)

    bijective_compose : forall (i : level) (a b c : U i) (f : b -> c) (g : a -> b) .
                           bijective f -> bijective g -> bijective (compose f g)



### Equipollence

    equipollent : intersect (i : level) . U i -> U i -> U i
                = fn a b . exists (f : a -> b) . bijective f

    equipollent_refl : forall (i : level) (a : U i) . equipollent a a

    eeqtp_impl_equipollent : forall (i : level) (a b : U i) . a <:> b -> equipollent a b

    equipollent_symm : forall (i : level) (a b : U i) . equipollent a b -> equipollent b a

    equipollent_trans : forall (i : level) (a b c : U i) .
                           equipollent a b -> equipollent b c -> equipollent a c

    equipollent_arrow : forall (i : level) (a a' b b' : U i) .
                           equipollent a a' -> equipollent b b' -> equipollent (a -> b) (a' -> b')

    equipollent_prod : forall (i : level) (a a' b b' : U i) .
                          equipollent a a' -> equipollent b b' -> equipollent (a & b) (a' & b')

    equipollent_sum : forall (i : level) (a a' b b' : U i) .
                         equipollent a a' -> equipollent b b' -> equipollent (a % b) (a' % b')

    equipollent_forall : forall (i : level) (a : U i) (b b' : a -> U i) .
                            (forall (x : a) . equipollent (b x) (b' x))
                            -> equipollent (forall (x : a) . b x) (forall (x : a) . b' x)

    equipollent_exists : forall (i : level) (a : U i) (b b' : a -> U i) .
                            (forall (x : a) . equipollent (b x) (b' x))
                            -> equipollent (exists (x : a) . b x) (exists (x : a) . b' x)

    equipollent_future : forall (i : level) (a b : future (U i)) .
                            future (equipollent (a #prev) (b #prev))
                            -> equipollent (future (a #prev)) (future (b #prev))

    equipollent_set : forall (i : level) (a : U i) (b b' : a -> U i) .
                         (forall (a1 : a) . b a1 <-> b' a1)
                         -> equipollent { x : a | b x } { x : a | b' x }

    equipollent_iset : forall (i : level) (a : U i) (b b' : a -> U i) .
                          (forall (a1 : a) . b a1 <-> b' a1)
                          -> equipollent (iset (x : a) . b x) (iset (x : a) . b' x)

    equipollent_set_iset : forall (i : level) (a : U i) (P : a -> U i) .
                              equipollent { x : a | P x } (iset (x : a) . P x)

    equipollent_squash : forall (i : level) (a b : U i) . a <-> b -> equipollent { a } { b }

    equipollent_isquash : forall (i : level) (a b : U i) .
                             a <-> b -> equipollent (isquash a) (isquash b)

    equipollent_squash_isquash : forall (i : level) (a : U i) . equipollent { a } (isquash a)

    equipollent_set_constraint : forall (i : level) (a : U i) (P : a -> U i) .
                                    equipollent { x : a | P x } (exists (x : a) . { P x })

    equipollent_iset_constraint : forall (i : level) (a : U i) (P : a -> U i) .
                                     equipollent
                                       (iset (x : a) . P x)
                                       (exists (x : a) . isquash (P x))

    equipollent_set_elim : forall (i : level) (a : U i) (b : a -> U i) .
                              (forall (x : a) . { b x }) -> equipollent { x : a | b x } a

    equipollent_iset_elim : forall (i : level) (a : U i) (b : a -> U i) .
                               (forall (x : a) . isquash (b x))
                               -> equipollent (iset (x : a) . b x) a

    equipollent_squash_unit : forall (i : level) (a : U i) . { a } -> equipollent { a } unit

    equipollent_isquash_unit : forall (i : level) (a : U i) .
                                  isquash a -> equipollent (isquash a) unit



### Subpollence

    subpollent : intersect (i : level) . U i -> U i -> U i
                = fn a b . exists (f : a -> b) . split_injective f

    subpollent_refl : forall (i : level) (a : U i) . subpollent a a

    equipollent_impl_subpollent : forall (i : level) (a b : U i) .
                                     equipollent a b -> subpollent a b

    subpollent_trans : forall (i : level) (a b c : U i) .
                          subpollent a b -> subpollent b c -> subpollent a c

Antisymmetry is the Schroeder-Bernstein theorem, which does not hold constructively.

    eeqtp_impl_subpollent : forall (i : level) (a b : U i) . a <:> b -> subpollent a b

    subpollent_arrow : forall (i : level) (a a' b b' : U i) .
                          subpollent a a' -> subpollent b b' -> subpollent (a -> b) (a' -> b')

Note that when it comes to subpollence, arrow is covariant in both arguments.

    subpollent_prod : forall (i : level) (a a' b b' : U i) .
                         subpollent a a' -> subpollent b b' -> subpollent (a & b) (a' & b')

    subpollent_sum : forall (i : level) (a a' b b' : U i) .
                        subpollent a a' -> subpollent b b' -> subpollent (a % b) (a' % b')

    subpollent_forall : forall (i : level) (a : U i) (b b' : a -> U i) .
                           (forall (x : a) . subpollent (b x) (b' x))
                           -> subpollent (forall (x : a) . b x) (forall (x : a) . b' x)

    subpollent_exists : forall (i : level) (a : U i) (b b' : a -> U i) .
                           (forall (x : a) . subpollent (b x) (b' x))
                           -> subpollent (exists (x : a) . b x) (exists (x : a) . b' x)

    subpollent_future : forall (i : level) (a b : future (U i)) .
                           future (subpollent (a #prev) (b #prev))
                           -> subpollent (future (a #prev)) (future (b #prev))

    subpollent_set : forall (i : level) (a : U i) (b b' : a -> U i) .
                        (forall (a1 : a) . b a1 <-> b' a1)
                        -> subpollent { x : a | b x } { x : a | b' x }

    subpollent_iset : forall (i : level) (a : U i) (b b' : a -> U i) .
                         (forall (a1 : a) . b a1 <-> b' a1)
                         -> subpollent (iset (x : a) . b x) (iset (x : a) . b' x)
