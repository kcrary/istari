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

When the underlying type changes, we can show that a set is finite
by showing that its image through a function is finite, provided that
function is injective.  It is convenient to establish the function is
injective by requiring a left inverse.

    map_through_finite : forall
                            (i : level)
                            (a b : U i)
                            (P : a -> U i)
                            (Q : b -> U i)
                            (f : a -> b)
                            (g : b -> a) .
                            (forall (x : a) . P x -> Q (f x))
                            -> (forall (x : a) . P x -> g (f x) = x : a)
                            -> finite Q
                            -> finite P

We only actually need the function to apply for elements of `P`.

    map_through_finite_gen : forall
                                (i : level)
                                (a b : U i)
                                (P : a -> U i)
                                (Q : b -> U i)
                                (f : forall (x : a) . P x -> b)
                                (g : b -> a) .
                                (forall (x : a) (h : P x) . Q (f x h))
                                -> (forall (x : a) (h : P x) . g (f x h) = x : a)
                                -> finite Q
                                -> finite P

    finite_exists : forall (i : level) (a b : U i) (P : a -> U i) (Q : a -> b -> U i) .
                       finite P
                       -> (forall (x : a) . finite (Q x))
                       -> finite (fn y . exists (x : a) . P x & Q x y)

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

We can show that a set of functions is finite if the functions only
vary on a finite and decidable portion of the domain, and each varying
domain element maps to finitely many results.

    finite_function_dep : forall
                             (i : level)
                             (a : U i)
                             (b P : a -> U i)
                             (Q : forall (x : a) . b x -> U i)
                             (g : forall (x : a) . b x) .
                             finite P
                             -> (forall (x : a) . Decidable.decidable (P x))
                             -> (forall (x : a) . P x -> finite (Q x))
                             -> (forall (x : a) (y : b x) . not (P x) -> Q x y -> y = g x : b x)
                             -> finite (fn f . forall (x : a) . Q x (f x))

    finite_function : forall
                         (i : level)
                         (a b : U i)
                         (P : a -> U i)
                         (Q : a -> b -> U i)
                         (g : a -> b) .
                         finite P
                         -> (forall (x : a) . Decidable.decidable (P x))
                         -> (forall (x : a) . P x -> finite (Q x))
                         -> (forall (x : a) (y : b) . not (P x) -> Q x y -> y = g x : b)
                         -> finite (fn f . forall (x : a) . Q x (f x))

Finiteness allows the list to contain a superset, but if the predicate
is also decidable, we can obtain a precise list.

    enumerate_finite : forall (i : level) (a : U i) (P : a -> U i) .
                          (forall (x : a) . Decidable.decidable (P x))
                          -> finite P
                          -> exists (L : List.list a) . forall (x : a) . P x <-> List.In a x L
