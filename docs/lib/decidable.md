# `Decidable`

    decidable : intersect (i : level) . U i -> U i
              = fn P . P % not P

    decidable_equiv : forall (i : level) (P Q : U i) . P <-> Q -> decidable P -> decidable Q

    decidable_compat_iff : forall (i : level) (P Q : U i) . P <-> Q -> decidable P <-> decidable Q

    decidable_and : forall (i : level) (P Q : U i) .
                       decidable P -> decidable Q -> decidable (P & Q)

    decidable_or : forall (i : level) (P Q : U i) .
                      decidable P -> decidable Q -> decidable (P % Q)

    decidable_implies : forall (i : level) (P Q : U i) .
                           decidable P -> decidable Q -> decidable (P -> Q)

    decidable_and_dep : forall (i : level) (P Q : U i) .
                           decidable P -> (P -> decidable Q) -> decidable (P & Q)

    decidable_or_dep : forall (i : level) (P Q : U i) .
                          decidable P -> (not P -> decidable Q) -> decidable (P % Q)

    decidable_implies_dep : forall (i : level) (P Q : U i) .
                               decidable P -> (P -> decidable Q) -> decidable (P -> Q)

    decidable_true : decidable unit

    decidable_false : decidable void

    decidable_not : forall (i : level) (P : U i) . decidable P -> decidable (not P)

    decidable_iff : forall (i : level) (P Q : U i) .
                       decidable P -> decidable Q -> decidable (P <-> Q)

    decidable_eq_bool : forall (b c : bool) . decidable (b = c : bool)

    decidable_istrue : forall (b : bool) . decidable (Bool.istrue b)

    decidable_from_bool : forall (i : level) (P : U i) (b : bool) .
                             Bool.istrue b <-> P -> decidable P

    decidable_eq_pair : forall (i : level) (a b : U i) .
                           (forall (x y : a) . decidable (x = y : a))
                           -> (forall (x y : b) . decidable (x = y : b))
                           -> forall (x y : a & b) . decidable (x = y : (a & b))

    decidable_forall_unique : forall (i : level) (a : U i) (P Q : a -> U i) .
                                 decidable (exists (x : a) . P x)
                                 -> (forall (x y : a) . P x -> P y -> x = y : a)
                                 -> (forall (x : a) . decidable (Q x))
                                 -> decidable (forall (x : a) . P x -> Q x)

    decidable_exists_unique : forall (i : level) (a : U i) (P Q : a -> U i) .
                                 decidable (exists (x : a) . P x)
                                 -> (forall (x y : a) . P x -> P y -> x = y : a)
                                 -> (forall (x : a) . P x -> decidable (Q x))
                                 -> decidable (exists (x : a) . P x & Q x)

    decidable_exists_unique2 : forall (i : level) (a b : U i) (P Q : a -> b -> U i) .
                                  decidable (exists (x : a) (y : b) . P x y)
                                  -> (forall (x x' : a) (y y' : b) .
                                        P x y -> P x' y' -> x = x' : a & y = y' : b)
                                  -> (forall (x : a) (y : b) . P x y -> decidable (Q x y))
                                  -> decidable (exists (x : a) (y : b) . P x y & Q x y)

    decidable_exists_unique3 : forall (i : level) (a b c : U i) (P Q : a -> b -> c -> U i) .
                                  decidable (exists (x : a) (y : b) (z : c) . P x y z)
                                  -> (forall (x x' : a) (y y' : b) (z z' : c) .
                                        P x y z
                                        -> P x' y' z'
                                        -> x = x' : a & y = y' : b & z = z' : c)
                                  -> (forall (x : a) (y : b) (z : c) .
                                        P x y z -> decidable (Q x y z))
                                  -> decidable (exists (x : a) (y : b) (z : c) . P x y z & Q x y z)
