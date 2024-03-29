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
