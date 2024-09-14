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


#### Finite map domains

Finite maps have finite domains, but it is difficult to obtain them
without a canonical ordering on the domain's type.  One version gives
the list quotiented by rearrangement:

    finite_map_domain_quotient : forall (i : level) (A B : U i) (f : finite_map A B) .
                                    quotient (L L'
                                                : { L : list A
                                                  | forall (a : A) . member f a <-> In A a L }) .
                                      (forall (a : A) . In A a L <-> In A a L')

Another version returns the domain squashed:

    finite_map_domain_squash : forall (i : level) (A B : U i) (f : finite_map A B) .
                                  { exists (L : list A) . forall (a : A) . member f a <-> In A a L }


### Generic finite maps

We can define a generic class determining what it means to be a finite map:

    FiniteMap : forall (i : level) (A B T : U i) .
                   T -> (T -> A -> option B) -> (T -> A -> B -> T) -> (T -> A -> T) -> U i
              = fn i A B T emp look upd rem .
                   (forall (f g : T) .
                      (forall (a : A) . look f a = look g a : option B) -> f = g : T)
                   & (forall (a a' : A) . Decidable.decidable (a = a' : A))
                   & (forall (a : A) . look emp a = None : option B)
                   & (forall (f : T) (a : A) (b : B) . look (upd f a b) a = Some b : option B)
                   & (forall (f : T) (a : A) (b : B) (a' : A) .
                        a != a' : A -> look (upd f a b) a' = look f a' : option B)
                   & (forall (f : T) (a : A) . look (rem f a) a = None : option B)
                   & (forall (f : T) (a a' : A) .
                        a != a' : A -> look (rem f a) a' = look f a' : option B)
                   & unit

We can then prove properties about such maps similar to what we showed
above for simple finite maps:

    FiniteMap_look_emp : forall
                            (i : level)
                            (A B T : U i)
                            (emp : T)
                            (look : T -> A -> option B)
                            (upd : T -> A -> B -> T)
                            (rem : T -> A -> T) .
                            FiniteMap i A B T emp look upd rem
                            -> forall (a : A) . look emp a = None : option B

    FiniteMap_look_upd : forall
                            (i : level)
                            (A B T : U i)
                            (emp : T)
                            (look : T -> A -> option B)
                            (upd : T -> A -> B -> T)
                            (rem : T -> A -> T) .
                            FiniteMap i A B T emp look upd rem
                            -> forall (f : T) (a : A) (b : B) .
                                 look (upd f a b) a = Some b : option B

    FiniteMap_look_upd_neq : forall
                                (i : level)
                                (A B T : U i)
                                (emp : T)
                                (look : T -> A -> option B)
                                (upd : T -> A -> B -> T)
                                (rem : T -> A -> T) .
                                FiniteMap i A B T emp look upd rem
                                -> forall (f : T) (a : A) (b : B) (a' : A) .
                                     a != a' : A -> look (upd f a b) a' = look f a' : option B

    FiniteMap_look_rem : forall
                            (i : level)
                            (A B T : U i)
                            (emp : T)
                            (look : T -> A -> option B)
                            (upd : T -> A -> B -> T)
                            (rem : T -> A -> T) .
                            FiniteMap i A B T emp look upd rem
                            -> forall (f : T) (a : A) . look (rem f a) a = None : option B

    FiniteMap_look_rem_neq : forall
                                (i : level)
                                (A B T : U i)
                                (emp : T)
                                (look : T -> A -> option B)
                                (upd : T -> A -> B -> T)
                                (rem : T -> A -> T) .
                                FiniteMap i A B T emp look upd rem
                                -> forall (f : T) (a a' : A) .
                                     a != a' : A -> look (rem f a) a' = look f a' : option B

    FiniteMap_upd_upd : forall
                           (i : level)
                           (A B T : U i)
                           (emp : T)
                           (look : T -> A -> option B)
                           (upd : T -> A -> B -> T)
                           (rem : T -> A -> T) .
                           FiniteMap i A B T emp look upd rem
                           -> forall (f : T) (a : A) (b b' : B) .
                                upd (upd f a b) a b' = upd f a b' : T

    FiniteMap_upd_upd_neq : forall
                               (i : level)
                               (A B T : U i)
                               (emp : T)
                               (look : T -> A -> option B)
                               (upd : T -> A -> B -> T)
                               (rem : T -> A -> T) .
                               FiniteMap i A B T emp look upd rem
                               -> forall (f : T) (a : A) (b : B) (a' : A) (b' : B) .
                                    a != a' : A
                                    -> upd (upd f a b) a' b' = upd (upd f a' b') a b : T

    FiniteMap_rem_emp : forall
                           (i : level)
                           (A B T : U i)
                           (emp : T)
                           (look : T -> A -> option B)
                           (upd : T -> A -> B -> T)
                           (rem : T -> A -> T) .
                           FiniteMap i A B T emp look upd rem
                           -> forall (a : A) . rem emp a = emp : T

    FiniteMap_rem_upd : forall
                           (i : level)
                           (A B T : U i)
                           (emp : T)
                           (look : T -> A -> option B)
                           (upd : T -> A -> B -> T)
                           (rem : T -> A -> T) .
                           FiniteMap i A B T emp look upd rem
                           -> forall (f : T) (a : A) (b : B) . rem (upd f a b) a = rem f a : T

    FiniteMap_rem_upd_neq : forall
                               (i : level)
                               (A B T : U i)
                               (emp : T)
                               (look : T -> A -> option B)
                               (upd : T -> A -> B -> T)
                               (rem : T -> A -> T) .
                               FiniteMap i A B T emp look upd rem
                               -> forall (f : T) (a : A) (b : B) (a' : A) .
                                    a != a' : A -> rem (upd f a b) a' = upd (rem f a') a b : T

    FiniteMap_rem_absent : forall
                              (i : level)
                              (A B T : U i)
                              (emp : T)
                              (look : T -> A -> option B)
                              (upd : T -> A -> B -> T)
                              (rem : T -> A -> T) .
                              FiniteMap i A B T emp look upd rem
                              -> forall (f : T) (a : A) .
                                   look f a = None : option B -> rem f a = f : T

Note that generic finite maps require that the domain's equality is
decidable, and thus an equality test is not supplied to the `emp`
operation.


### Generic finite maps with merge

The `FiniteMap` class does not include a merge option.  The
`FiniteMapMerge` class adds one:

    FiniteMapMerge : forall (i : level) (A B T : U i) .
                        T
                        -> (T -> A -> option B)
                        -> (T -> A -> B -> T)
                        -> (T -> A -> T)
                        -> (T -> T -> T)
                        -> U i
                   = fn i A B T emp look upd rem mer .
                        FiniteMap i A B T emp look upd rem
                        & (forall (f g : T) (a : A) (b : B) .
                             look f a = Some b : option B -> look (mer f g) a = Some b : option B)
                        & (forall (f g : T) (a : A) .
                             look f a = None : option B -> look (mer f g) a = look g a : option B)
                        & unit

    FiniteMapMerge_look_mer_left : forall
                                      (i : level)
                                      (A B T : U i)
                                      (emp : T)
                                      (look : T -> A -> option B)
                                      (upd : T -> A -> B -> T)
                                      (rem : T -> A -> T)
                                      (mer : T -> T -> T) .
                                      FiniteMapMerge i A B T emp look upd rem mer
                                      -> forall (f g : T) (a : A) (b : B) .
                                           look f a = Some b : option B
                                           -> look (mer f g) a = Some b : option B

    FiniteMapMerge_look_mer_right : forall
                                       (i : level)
                                       (A B T : U i)
                                       (emp : T)
                                       (look : T -> A -> option B)
                                       (upd : T -> A -> B -> T)
                                       (rem : T -> A -> T)
                                       (mer : T -> T -> T) .
                                       FiniteMapMerge i A B T emp look upd rem mer
                                       -> forall (f g : T) (a : A) .
                                            look f a = None : option B
                                            -> look (mer f g) a = look g a : option B

    FiniteMapMerge_mer_emp_left : forall
                                     (i : level)
                                     (A B T : U i)
                                     (emp : T)
                                     (look : T -> A -> option B)
                                     (upd : T -> A -> B -> T)
                                     (rem : T -> A -> T)
                                     (mer : T -> T -> T) .
                                     FiniteMapMerge i A B T emp look upd rem mer
                                     -> forall (f : T) . mer emp f = f : T

    FiniteMapMerge_mer_emp_right : forall
                                      (i : level)
                                      (A B T : U i)
                                      (emp : T)
                                      (look : T -> A -> option B)
                                      (upd : T -> A -> B -> T)
                                      (rem : T -> A -> T)
                                      (mer : T -> T -> T) .
                                      FiniteMapMerge i A B T emp look upd rem mer
                                      -> forall (f : T) . mer f emp = f : T

    FiniteMapMerge_upd_mer_left : forall
                                     (i : level)
                                     (A B T : U i)
                                     (emp : T)
                                     (look : T -> A -> option B)
                                     (upd : T -> A -> B -> T)
                                     (rem : T -> A -> T)
                                     (mer : T -> T -> T) .
                                     FiniteMapMerge i A B T emp look upd rem mer
                                     -> forall (f g : T) (a : A) (b : B) .
                                          upd (mer f g) a b = mer (upd f a b) g : T

    FiniteMapMerge_upd_mer_right : forall
                                      (i : level)
                                      (A B T : U i)
                                      (emp : T)
                                      (look : T -> A -> option B)
                                      (upd : T -> A -> B -> T)
                                      (rem : T -> A -> T)
                                      (mer : T -> T -> T) .
                                      FiniteMapMerge i A B T emp look upd rem mer
                                      -> forall (f g : T) (a : A) (b : B) .
                                           look f a = None : option B
                                           -> upd (mer f g) a b = mer f (upd g a b) : T

    FiniteMapMerge_rem_mer : forall
                                (i : level)
                                (A B T : U i)
                                (emp : T)
                                (look : T -> A -> option B)
                                (upd : T -> A -> B -> T)
                                (rem : T -> A -> T)
                                (mer : T -> T -> T) .
                                FiniteMapMerge i A B T emp look upd rem mer
                                -> forall (f g : T) (a : A) .
                                     rem (mer f g) a = mer (rem f a) (rem g a) : T


### Generic finite maps minus extensionality

To assist in building finite maps, there is a class that leaves out
extensionality equality:

    PreFiniteMap : forall (i : level) (A B T : U i) .
                      T -> (T -> A -> option B) -> (T -> A -> B -> T) -> (T -> A -> T) -> U i
                 = fn i A B T emp look upd rem .
                      (forall (a a' : A) . Decidable.decidable (a = a' : A))
                      & (forall (a : A) . look emp a = None : option B)
                      & (forall (f : T) (a : A) (b : B) . look (upd f a b) a = Some b : option B)
                      & (forall (f : T) (a : A) (b : B) (a' : A) .
                           a != a' : A -> look (upd f a b) a' = look f a' : option B)
                      & (forall (f : T) (a : A) . look (rem f a) a = None : option B)
                      & (forall (f : T) (a a' : A) .
                           a != a' : A -> look (rem f a) a' = look f a' : option B)
                      & unit

Given a pre-finite-map, one can build a finite map by quotienting it:

    (* "quotient pre-finite-map" *)
    qpfm : intersect (i : level) . forall (A B T : U i) . (T -> A -> option B) -> U i
         = fn A B T look . quotient (f g : T) . (forall (a : A) . look f a = look g a : option B)

    quotient_emp : forall
                      (i : level)
                      (A B T : U i)
                      (emp : T)
                      (look : T -> A -> option B)
                      (upd : T -> A -> B -> T)
                      (rem : T -> A -> T) .
                      PreFiniteMap i A B T emp look upd rem -> emp : qpfm A B T look

    quotient_look : forall
                       (i : level)
                       (A B T : U i)
                       (emp : T)
                       (look : T -> A -> option B)
                       (upd : T -> A -> B -> T)
                       (rem : T -> A -> T) .
                       PreFiniteMap i A B T emp look upd rem
                       -> look : qpfm A B T look -> A -> option B

    quotient_upd : forall
                      (i : level)
                      (A B T : U i)
                      (emp : T)
                      (look : T -> A -> option B)
                      (upd : T -> A -> B -> T)
                      (rem : T -> A -> T) .
                      PreFiniteMap i A B T emp look upd rem
                      -> upd : qpfm A B T look -> A -> B -> qpfm A B T look

    quotient_rem : forall
                      (i : level)
                      (A B T : U i)
                      (emp : T)
                      (look : T -> A -> option B)
                      (upd : T -> A -> B -> T)
                      (rem : T -> A -> T) .
                      PreFiniteMap i A B T emp look upd rem
                      -> rem : qpfm A B T look -> A -> qpfm A B T look

    FiniteMap_qpfm : forall
                        (i : level)
                        (A B T : U i)
                        (emp : T)
                        (look : T -> A -> option B)
                        (upd : T -> A -> B -> T)
                        (rem : T -> A -> T) .
                        PreFiniteMap i A B T emp look upd rem
                        -> FiniteMap i A B (qpfm A B T look) emp look upd rem

Another class gives finite maps with merge but without extensionality:

    PreFiniteMapMerge : forall (i : level) (A B T : U i) .
                           T
                           -> (T -> A -> option B)
                           -> (T -> A -> B -> T)
                           -> (T -> A -> T)
                           -> (T -> T -> T)
                           -> U i
                      = fn i A B T emp look upd rem mer .
                           PreFiniteMap i A B T emp look upd rem
                           & (forall (f g : T) (a : A) (b : B) .
                                look f a = Some b : option B
                                -> look (mer f g) a = Some b : option B)
                           & (forall (f g : T) (a : A) .
                                look f a = None : option B
                                -> look (mer f g) a = look g a : option B)
                           & unit

    quotient_mer : forall
                      (i : level)
                      (A B T : U i)
                      (emp : T)
                      (look : T -> A -> option B)
                      (upd : T -> A -> B -> T)
                      (rem : T -> A -> T)
                      (mer : T -> T -> T) .
                      PreFiniteMapMerge i A B T emp look upd rem mer
                      -> mer : qpfm A B T look -> qpfm A B T look -> qpfm A B T look

    FiniteMapMerge_qpfm : forall
                             (i : level)
                             (A B T : U i)
                             (emp : T)
                             (look : T -> A -> option B)
                             (upd : T -> A -> B -> T)
                             (rem : T -> A -> T)
                             (mer : T -> T -> T) .
                             PreFiniteMapMerge i A B T emp look upd rem mer
                             -> FiniteMapMerge i A B (qpfm A B T look) emp look upd rem mer

The simple finite maps are defined using these tools.  The discrepancy
between the types of `empty` versus `emp` is mediated using a lemma
that extracts an equality test from a finite map:

    finite_map_impl_eqtest : intersect (i : level) .
                                forall (A B : U i) . finite_map A B -> eqtest A

(By definition, all equality tests at the same type are equal.)
