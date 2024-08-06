# `Finite`

A form of Kuratowski finiteness:

    finite : intersect (i : level) . forall (a : U i) . (a -> U i) -> U i
           = fn a P . exists (L : List.list a) . forall (x : a) . P x -> List.In a x L
           (1 implicit argument)

Note that the list may contain a superset of the elements satisfying
`P`.  This makes the definition easier to work with.  For example, the
simple form of the `finite_subset` lemma depends on it.

    finite_subset : forall (i : level) (a : U i) (P Q : a -> U i) .
                       (forall (x : a) . P x -> Q x) -> finite Q -> finite P

    decidable_forall_finite : forall (i : level) (a : U i) (P Q : a -> U i) .
                                 finite P
                                 -> (forall (x : a) . Decidable.decidable (P x))
                                 -> (forall (x : a) . P x -> Decidable.decidable (Q x))
                                 -> Decidable.decidable (forall (x : a) . P x -> Q x)

    decidable_exists_finite : forall (i : level) (a : U i) (P Q : a -> U i) .
                                 finite P
                                 -> (forall (x : a) . Decidable.decidable (P x))
                                 -> (forall (x : a) . P x -> Decidable.decidable (Q x))
                                 -> Decidable.decidable (exists (x : a) . P x & Q x)

    decidable_exists_finite_simple : forall (i : level) (a : U i) (P : a -> U i) .
                                        finite P
                                        -> (forall (x : a) . Decidable.decidable (P x))
                                        -> Decidable.decidable (exists (x : a) . P x)
