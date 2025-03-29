# `FiniteMap`

### Simple finite maps

A finite map from `A` into `B` (`finite_map A B`) is a mapping from
`A` to `option B`, in which only finitely many arguments map to
anything other than `None`.

    finite_map : intersect (i : level) . U i -> U i -> U i

The operations on a finite map are `lookup`, `empty`, `update`,
`remove`, and `merge`:

    lookup : intersect (i : level) . forall (A B : U i) . finite_map A B -> A -> option B
           (2 implicit arguments)

    empty : intersect (i : level) . forall (A B : U i) . eqtest A -> finite_map A B
          (2 implicit arguments)

    update : intersect (i : level) .
                forall (A B : U i) . finite_map A B -> A -> B -> finite_map A B
           (2 implicit arguments)

    remove : intersect (i : level) . forall (A B : U i) . finite_map A B -> A -> finite_map A B
           (2 implicit arguments)

    merge : intersect (i : level) .
               forall (A B : U i) . finite_map A B -> finite_map A B -> finite_map A B
          (2 implicit arguments)

The update operation `update f a b` produces a new finite map that
maps `a` to `Some b`.  If `a` was already in `f`'s domain, it
overwrites `a`'s old mapping.  The merge operation `merge f g`
combines the two finite maps into one; if an argument is in both
domains, the left-hand mapping takes precedence.

To build a finite map requires the domain type to have decidable
equality.  The equality test is supplied to the `empty` operation.

    eqtest : intersect (i : level) . U i -> U i
           = fn A . { e : A -> A -> bool | forall (x y : A) . x = y : A <-> Bool.istrue (e x y) }

    finite_map_impl_eqtest : intersect (i : level) .
                                forall (A B : U i) . finite_map A B -> eqtest A

A recommended way to use `empty` is to define `eqt : eqtest A`, then
define `myempty` to be `empty eqt`.  If `myempty` is then made a [soft
constant](../terms.html#opacity), the lemmas that follow will work
with `myempty` without any additional effort.

Finite maps have extensional equality:

    finite_map_ext : forall (i : level) (A B : U i) (f g : finite_map A B) .
                        (forall (a : A) . lookup f a = lookup g a : option B)
                        -> f = g : finite_map A B

Several principles determine how the operations interact with lookup:

    lookup_empty : forall (i : level) (A B : U i) (e : eqtest A) (a : A) .
                      lookup (empty e) a = None : option B

    lookup_update : forall (i : level) (A B : U i) (f : finite_map A B) (a : A) (b : B) .
                       lookup (update f a b) a = Some b : option B

    lookup_update_neq : forall
                           (i : level)
                           (A B : U i)
                           (f : finite_map A B)
                           (a : A)
                           (b : B)
                           (a' : A) .
                           a != a' : A -> lookup (update f a b) a' = lookup f a' : option B

    lookup_remove : forall (i : level) (A B : U i) (f : finite_map A B) (a : A) .
                       lookup (remove f a) a = None : option B

    lookup_remove_neq : forall (i : level) (A B : U i) (f : finite_map A B) (a a' : A) .
                           a != a' : A -> lookup (remove f a) a' = lookup f a' : option B

    lookup_merge_left : forall (i : level) (A B : U i) (f g : finite_map A B) (a : A) (b : B) .
                           lookup f a = Some b : option B
                           -> lookup (merge f g) a = Some b : option B

    lookup_merge_right : forall (i : level) (A B : U i) (f g : finite_map A B) (a : A) .
                            lookup f a = None : option B
                            -> lookup (merge f g) a = lookup g a : option B

We can obtain other corollaries about finite maps using the above and
extensional equality:

    update_update : forall (i : level) (A B : U i) (f : finite_map A B) (a : A) (b b' : B) .
                       update (update f a b) a b' = update f a b' : finite_map A B

    update_update_neq : forall
                           (i : level)
                           (A B : U i)
                           (f : finite_map A B)
                           (a : A)
                           (b : B)
                           (a' : A)
                           (b' : B) .
                           a != a' : A
                           -> update (update f a b) a' b'
                                = update (update f a' b') a b
                                : finite_map A B

    remove_empty : forall (i : level) (A B : U i) (e : eqtest A) (a : A) .
                      remove (empty e) a = empty e : finite_map A B

    remove_update : forall (i : level) (A B : U i) (f : finite_map A B) (a : A) (b : B) .
                       remove (update f a b) a = remove f a : finite_map A B

    remove_update_neq : forall
                           (i : level)
                           (A B : U i)
                           (f : finite_map A B)
                           (a : A)
                           (b : B)
                           (a' : A) .
                           a != a' : A
                           -> remove (update f a b) a' = update (remove f a') a b : finite_map A B

    remove_absent : forall (i : level) (A B : U i) (f : finite_map A B) (a : A) .
                       lookup f a = None : option B -> remove f a = f : finite_map A B

    merge_empty_left : forall (i : level) (A B : U i) (e : eqtest A) (f : finite_map A B) .
                          merge (empty e) f = f : finite_map A B

    merge_empty_right : forall (i : level) (A B : U i) (e : eqtest A) (f : finite_map A B) .
                           merge f (empty e) = f : finite_map A B

    update_merge_left : forall (i : level) (A B : U i) (f g : finite_map A B) (a : A) (b : B) .
                           update (merge f g) a b = merge (update f a b) g : finite_map A B

    update_merge_right : forall (i : level) (A B : U i) (f g : finite_map A B) (a : A) (b : B) .
                            lookup f a = None : option B
                            -> update (merge f g) a b = merge f (update g a b) : finite_map A B

    remove_merge : forall (i : level) (A B : U i) (f g : finite_map A B) (a : A) .
                      remove (merge f g) a = merge (remove f a) (remove g a) : finite_map A B

The derived notion of membership is useful:

    member : intersect (i : level) . forall (A B : U i) . finite_map A B -> A -> U i
           = fn A B f a . exists (b : B) . lookup f a = Some b : option B
           (2 implicit arguments)

    remove_absent' : forall (i : level) (A B : U i) (f : finite_map A B) (a : A) .
                        not (member f a) -> remove f a = f : finite_map A B

    lookup_merge_left' : forall (i : level) (A B : U i) (f g : finite_map A B) (a : A) .
                            member f a -> lookup (merge f g) a = lookup f a : option B

    lookup_merge_right' : forall (i : level) (A B : U i) (f g : finite_map A B) (a : A) .
                             not (member f a) -> lookup (merge f g) a = lookup g a : option B

    decidable_member : forall (i : level) (A B : U i) (f : finite_map A B) (a : A) .
                          Decidable.decidable (member f a)



##### Mapping over finite maps


    map : intersect (i : level) .
             forall (A B C : U i) . (A -> B -> C) -> finite_map A B -> finite_map A C

    map_identity : forall (i : level) (A B : U i) (f : finite_map A B) .
                      map (fn v0 x . x) f = f : finite_map A B

    map_compose : forall
                     (i : level)
                     (A B C D : U i)
                     (g : A -> C -> D)
                     (h : A -> B -> C)
                     (f : finite_map A B) .
                     map g (map h f) = map (fn x y . g x (h x y)) f : finite_map A D

    lookup_map : forall (i : level) (A B C : U i) (g : A -> B -> C) (f : finite_map A B) (a : A) .
                    lookup (map g f) a = Option.map (g a) (lookup f a) : option C

    map_empty : forall (i : level) (A B C : U i) (g : A -> B -> C) (e : eqtest A) .
                   map g (empty e) = empty e : finite_map A C

    map_update : forall
                    (i : level)
                    (A B C : U i)
                    (g : A -> B -> C)
                    (f : finite_map A B)
                    (a : A)
                    (b : B) .
                    map g (update f a b) = update (map g f) a (g a b) : finite_map A C

    map_remove : forall (i : level) (A B C : U i) (g : A -> B -> C) (f : finite_map A B) (a : A) .
                    map g (remove f a) = remove (map g f) a : finite_map A C

    map_merge : forall (i : level) (A B C : U i) (g : A -> B -> C) (f f' : finite_map A B) .
                   map g (merge f f') = merge (map g f) (map g f') : finite_map A C

    member_map : forall (i : level) (A B C : U i) (a : A) (g : A -> B -> C) (f : finite_map A B) .
                    member (map g f) a <-> member f a



##### Combination (a.k.a. symmetric merge)

    combine : intersect (i : level) .
                 forall (A B : U i) .
                   finite_map A B -> finite_map A B -> (A -> B -> B -> B) -> finite_map A B
            = fn A B f g h .
                 merge (map (fn a b . (fnind option_fn : forall (v0 : option [B]) . B of
                                       | None . b
                                       | Some b' . h a b b') (lookup g a)) f) g
            (2 implicit arguments)

    combine_transpose : forall
                           (i : level)
                           (A B : U i)
                           (f g : finite_map A B)
                           (h : A -> B -> B -> B) .
                           combine f g h = combine g f (fn a b b' . h a b' b) : finite_map A B

    lookup_combine_left : forall
                             (i : level)
                             (A B : U i)
                             (f g : finite_map A B)
                             (h : A -> B -> B -> B)
                             (a : A) .
                             lookup g a = None : option B
                             -> lookup (combine f g h) a = lookup f a : option B

    lookup_combine_right : forall
                              (i : level)
                              (A B : U i)
                              (f g : finite_map A B)
                              (h : A -> B -> B -> B)
                              (a : A) .
                              lookup f a = None : option B
                              -> lookup (combine f g h) a = lookup g a : option B

    lookup_combine_both : forall
                             (i : level)
                             (A B : U i)
                             (f g : finite_map A B)
                             (h : A -> B -> B -> B)
                             (a : A)
                             (b b' : B) .
                             lookup f a = Some b : option B
                             -> lookup g a = Some b' : option B
                             -> lookup (combine f g h) a = Some (h a b b') : option B

    combine_empty_left : forall
                            (i : level)
                            (A B : U i)
                            (e : eqtest A)
                            (f : finite_map A B)
                            (h : A -> B -> B -> B) .
                            combine (empty e) f h = f : finite_map A B

    combine_empty_right : forall
                             (i : level)
                             (A B : U i)
                             (e : eqtest A)
                             (f : finite_map A B)
                             (h : A -> B -> B -> B) .
                             combine f (empty e) h = f : finite_map A B

    combine_update_left_absent : forall
                                    (i : level)
                                    (A B : U i)
                                    (f g : finite_map A B)
                                    (h : A -> B -> B -> B)
                                    (a : A)
                                    (b : B) .
                                    lookup g a = None : option B
                                    -> combine (update f a b) g h
                                         = update (combine f g h) a b
                                         : finite_map A B

    combine_update_right_absent : forall
                                     (i : level)
                                     (A B : U i)
                                     (f g : finite_map A B)
                                     (h : A -> B -> B -> B)
                                     (a : A)
                                     (b : B) .
                                     lookup f a = None : option B
                                     -> combine f (update g a b) h
                                          = update (combine f g h) a b
                                          : finite_map A B

    combine_update_left_present : forall
                                     (i : level)
                                     (A B : U i)
                                     (f g : finite_map A B)
                                     (h : A -> B -> B -> B)
                                     (a : A)
                                     (b b' : B) .
                                     lookup g a = Some b' : option B
                                     -> combine (update f a b) g h
                                          = update (combine f g h) a (h a b b')
                                          : finite_map A B

    combine_update_right_present : forall
                                      (i : level)
                                      (A B : U i)
                                      (f g : finite_map A B)
                                      (h : A -> B -> B -> B)
                                      (a : A)
                                      (b b' : B) .
                                      lookup f a = Some b' : option B
                                      -> combine f (update g a b) h
                                           = update (combine f g h) a (h a b' b)
                                           : finite_map A B

    combine_remove_left_absent : forall
                                    (i : level)
                                    (A B : U i)
                                    (f g : finite_map A B)
                                    (h : A -> B -> B -> B)
                                    (a : A) .
                                    lookup g a = None : option B
                                    -> combine (remove f a) g h
                                         = remove (combine f g h) a
                                         : finite_map A B

    combine_remove_right_absent : forall
                                     (i : level)
                                     (A B : U i)
                                     (f g : finite_map A B)
                                     (h : A -> B -> B -> B)
                                     (a : A) .
                                     lookup f a = None : option B
                                     -> combine f (remove g a) h
                                          = remove (combine f g h) a
                                          : finite_map A B

    combine_remove_left_present : forall
                                     (i : level)
                                     (A B : U i)
                                     (f g : finite_map A B)
                                     (h : A -> B -> B -> B)
                                     (a : A)
                                     (b : B) .
                                     lookup g a = Some b : option B
                                     -> combine (remove f a) g h
                                          = update (combine f g h) a b
                                          : finite_map A B

    combine_remove_right_present : forall
                                      (i : level)
                                      (A B : U i)
                                      (f g : finite_map A B)
                                      (h : A -> B -> B -> B)
                                      (a : A)
                                      (b : B) .
                                      lookup f a = Some b : option B
                                      -> combine f (remove g a) h
                                           = update (combine f g h) a b
                                           : finite_map A B

    map_combine : forall
                     (i : level)
                     (A B C : U i)
                     (k : A -> B -> C)
                     (f g : finite_map A B)
                     (h : A -> B -> B -> B)
                     (h' : A -> C -> C -> C) .
                     (forall (a : A) (b b' : B) . k a (h a b b') = h' a (k a b) (k a b') : C)
                     -> map k (combine f g h) = combine (map k f) (map k g) h' : finite_map A C



#### Finite map domains

Finite maps have finite domains, but it is difficult to obtain them
without a canonical ordering on the domain's type.  One version gives
the list quotiented by rearrangement:

    finite_map_domain_quotient : forall (i : level) (A B : U i) (f : finite_map A B) .
                                    quotient (L L'
                                                : { L : List.list A
                                                  | forall (a : A) . member f a <-> List.In A a L }) .
                                      (forall (a : A) . List.In A a L <-> List.In A a L')

Another version gives the list quotiented by permutation:

    finite_map_domain_quotient_perm : forall (i : level) (A B : U i) (f : finite_map A B) .
                                         quotient (L L'
                                                     : { L : List.list A
                                                       | List.Forall_dist (fn x y . x != y : A) L
                                                         & (forall (a : A) .
                                                              member f a <-> List.In A a L) }) .
                                           Permutation.Perm L L'

Still another version returns the domain unquotiented but squashed:

    finite_map_domain_squash : forall (i : level) (A B : U i) (f : finite_map A B) .
                                  { exists (L : List.list A) .
                                      forall (a : A) . member f a <-> List.In A a L }

Finally, although the domain (as a list) is underdetermined, its
length is determined:

    finite_map_domain_size : forall (i : level) (A B : U i) (f : finite_map A B) .
                                exists (n : nat) .
                                  { exists (L : List.list A) .
                                      List.length L = n : nat
                                      & List.Forall_dist (fn x y . x != y : A) L
                                      & (forall (a : A) . member f a <-> List.In A a L) }



#### Generic finite maps

The submodule [`Class`](finite-map-class.html) defines a generic class
determining what it means to be a finite map.  It is used in the
implementation of the simple finite maps above.

The simple finite maps are defined using tools from the `Class`
submodule.  The discrepancy between the types of `empty` versus `emp`
(*q.v.*) is mediated using the `finite_map_impl_eqtest` lemma (above)
that extracts an equality test from a finite map.  (By definition, all
equality tests at the same type are equal.)

    FiniteMap_finite_map : forall (i : level) (A B : U i) (e : eqtest A) .
                              Class.FiniteMap i A B (finite_map A B) (empty e) lookup update remove

    FiniteMap_finite_map' : forall (i : level) (A B : U i) (f : finite_map A B) .
                               Class.FiniteMap
                                 i
                                 A
                                 B
                                 (finite_map A B)
                                 (empty (finite_map_impl_eqtest A B f))
                                 lookup
                                 update
                                 remove



#### Miscellaneous

    finite_map_subtype : forall (i : level) (A B C : U i) .
                            B <: C -> finite_map A B <: finite_map A C

    equipollent_finite_map : forall (i : level) (A B C : U i) .
                                Function.equipollent B C
                                -> Function.equipollent (finite_map A B) (finite_map A C)

    subpollent_finite_map : forall (i : level) (A B C : U i) .
                               Function.subpollent B C
                               -> Function.subpollent (finite_map A B) (finite_map A C)

    kindlike_finite_map : forall (i : level) (A : U i) (B : U (1 + i)) .
                             B -> Kindlike.kindlike i B -> Kindlike.kindlike i (finite_map A B)
