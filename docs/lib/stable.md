# `Stable`

    stable : intersect (i : level) . U i -> U i
           = fn P . not (not P) -> P

    stable_and : forall (i : level) (P Q : U i) . stable P -> stable Q -> stable (P & Q)

    stable_implies : forall (i : level) (P Q : U i) . stable Q -> stable (P -> Q)

    stable_forall : forall (i : level) (A : U i) (P : A -> U i) .
                       (forall (x : A) . stable (P x)) -> stable (forall (x : A) . P x)

    stable_true : stable unit

    stable_false : stable void

    stable_not : forall (i : level) (P : U i) . stable (not P)

    stable_iff : forall (i : level) (P Q : U i) . stable P -> stable Q -> stable (P <-> Q)

    decidable_impl_stable : forall (i : level) (P : U i) . Decidable.decidable P -> stable P

    stable_eq_bool : forall (b c : bool) . stable (b = c : bool)

    stable_istrue : forall (b : bool) . stable (Bool.istrue b)

    dneg_elim_if_stable : forall (i j : level) (P : U i) (Q : U j) .
                             stable Q -> not (not P) -> (P -> Q) -> Q

    not_not_excluded_middle : forall (i : level) (P : U i) . not (not (Decidable.decidable P))

    excluded_middle_if_stable : forall (i j : level) (P : U i) (Q : U j) .
                                   stable Q -> (Decidable.decidable P -> Q) -> Q
