# `FiniteMap.Class`


### Generic finite maps

The module `FiniteMap.Class` defines a generic class determining what
it means to be a finite map:

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

The `FiniteMap` class does not include a merge operation.  The
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


### The factory

The `FiniteMap.Class.Factory` submodule provides tools to assist in
constructing finite maps.  First, there is a class of generic finite
maps *minus extensional equality.*

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

Another class gives finite maps with merge but minus extensionality:

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
