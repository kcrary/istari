# `Sqstable`

    sqstable : intersect (i : level) . U i -> U i
             = fn P . { P } -> P

    sqstable_and : intersect (i : level) (P Q : U i) .
                      sqstable P -> sqstable Q -> sqstable (P & Q)

    sqstable_implies : intersect (i : level) (P Q : U i) . sqstable Q -> sqstable (P -> Q)

    sqstable_forall : intersect (i : level) (A : U i) (P : A -> U i) .
                         (forall (x : A) . sqstable (P x)) -> sqstable (`forall A P)

    sqstable_forallfut : intersect (i : level) .
                            intersectfut (A : U i) .
                              intersect (P : forallfut (v0 : A) . U i) .
                                (forallfut (x : A) . sqstable (P x)) -> sqstable (`forallfut A P)

    sqstable_intersect : intersect (i : level) (A : U i) (P : A -> U i) .
                            (intersect (x : A) . sqstable (P x)) -> sqstable (`intersect A P)

    sqstable_intersectfut : intersect (i : level) .
                               intersectfut (A : U i) .
                                 intersect (P : forallfut (v0 : A) . U i) .
                                   (intersectfut (x : A) . sqstable (P x))
                                   -> sqstable (`intersectfut A P)

    sqstable_parametric : intersect (i : level) (A : U i) (P : A -> U i) .
                             (parametric (x : A) . sqstable (P x)) -> sqstable (`parametric A P)

    sqstable_parametricfut : intersect (i : level) .
                                intersectfut (A : U i) .
                                  intersect (P : forallfut (v0 : A) . U i) .
                                    (parametricfut (x : A) . sqstable (P x))
                                    -> sqstable (`parametricfut A P)

    sqstable_future : intersect (i : level) .
                         intersectfut (P : U i) . future (sqstable P) -> sqstable (future P)

    sqstable_letnext : intersect (i : level) .
                          intersectfut (A : U i) .
                            forall (m : future A) .
                              intersect (B : forallfut (v0 : A) . U i) .
                                (forallfut (x : A) . sqstable (B x))
                                -> sqstable (let next x = m in B x)

    sqstable_true : sqstable unit

    sqstable_false : sqstable void

    sqstable_equal : intersect (i : level) (A : U i) (x y : A) . sqstable (x = y : A)

    sqstable_subtype : intersect (i : level) (A B : U i) . sqstable (A <: B)

    sqstable_squash : intersect (i : level) (A : U i) . sqstable { A }

    sqstable_isquash : intersect (i : level) (A : U i) . sqstable (isquash A)

    sqstable_not : intersect (i : level) (P : U i) . sqstable (not P)

    sqstable_iff : intersect (i : level) (P Q : U i) .
                      sqstable P -> sqstable Q -> sqstable (P <-> Q)

    sqstable_equiv : intersect (i : level) (P Q : U i) . P <-> Q -> sqstable P -> sqstable Q

    decidable_impl_sqstable : intersect (i : level) (P : U i) .
                                 Decidable.decidable P -> sqstable P

    stable_impl_sqstable : forall (i : level) (P : U i) . Stable.stable P -> sqstable P

    sqstable_elim : intersect (i : level) (P : U i) . sqstable P -> { P } -> P

    sqstable_elim_isquash : intersect (i : level) (P : U i) . sqstable P -> isquash P -> P
