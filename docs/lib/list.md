# `List`

Lists are defined:

    datatype
      intersect (i : level) .
      forall (a : U i) .
      U i
    of
      list : type =
      | nil : list
      | cons : a -> list -> list

Producing:

    list : intersect (i : level) . forall (a : U i) . U i

    nil  : intersect (i : level) . forall (a : U i) . list a
         (1 implicit argument)

    cons : intersect (i : level) . forall (a : U i) . a -> list a -> list a
         (1 implicit argument)

The syntactic sugar `h :: t` is accepted for `` ` cons _ h t``, as usual.


The iterator for lists:

    list_iter : intersect (i : level) .
                   forall (a : U i) (v0 : list a -> U i) .
                     v0 nil
                     -> (forall (v1 : a) (v2 : list a) . v0 v2 -> v0 (v1 :: v2))
                     -> forall (v1 : list a) . v0 v1

    list_iter A P z s (nil _) --> z
    list_iter A P z s (cons _ h t) --> s h t (list_iter A P z s t)


A simpler case-analysis operation:

    list_case : intersect (i : level) .
                   forall (a b : U i) . list a -> b -> (a -> list a -> b) -> b
              = fn a b l mnil mcons . list_iter a (fn v0 . b) mnil (fn h t v0 . mcons h t) l
              (2 implicit arguments)

    list_case _ _ (nil _) z _ --> z
    list_case _ _ (cons _ h t) _ s --> s h t


### Append

    append : intersect (i : level) . forall (a : U i) . list a -> list a -> list a
           = fn a l1 l2 . list_iter a (fn v0 . list a) l2 (fn h v0 t . h :: t) l1
           (1 implicit argument)

    append _ (nil _) l --> l
    append A (cons _ h t) l --> cons A h (append A t l)

    append_id_l : forall (i : level) (a : U i) (l : list a) . append nil l = l : list a

    append_id_r : forall (i : level) (a : U i) (l : list a) . append l nil = l : list a

    append_assoc : forall (i : level) (a : U i) (l1 l2 l3 : list a) .
                      append (append l1 l2) l3 = append l1 (append l2 l3) : list a


### Length

    length : intersect (i : level) . forall (a : U i) . list a -> nat
           =rec= fn a l . list_case l 0 (fn v0 t . succ (length t))
           (1 implicit argument)

    length _ (nil _) --> 0
    length A (cons _ _ t) --> succ (length A t)

    length_append : forall (i : level) (a : U i) (l1 l2 : list a) .
                       length (append l1 l2) = length l1 + length l2 : nat


### Fold

    foldr : intersect (i : level) . forall (a b : U i) . b -> (a -> b -> b) -> list a -> b

    foldr _ _ z _ (nil _) --> z
    foldr a b z f (cons _ h t) --> f h (foldr a b z f t)


### Map

    map : intersect (i : level) . forall (a b : U i) . (a -> b) -> list a -> list b

    map _ b _ (nil _) --> nil b
    map a b f (cons _ h t) --> cons b (f h) (map a b f t)

    map_compose : forall (i : level) (a b c : U i) (f : b -> c) (g : a -> b) (l : list a) .
                     map f (map g l) = map (fn x . f (g x)) l : list c

    
### Universal and existential predicates over lists

    datatype
      intersect (i : level) .
      forall (a : U i) (P : a -> U i) .
      U i
    of
      Forall : list a -> type =
      | Forall_nil : Forall nil
      | Forall_cons : forall h t . P h -> Forall t -> Forall (h :: t)


    datatype
      intersect (i : level) .
      forall (a : U i) (P : a -> U i) .
      U i
    of
      Exists : list a -> type =
      | Exists_hit : forall h t . P h -> Exists (h :: t)
      | Exists_miss : forall h t . Exists t -> Exists (h :: t)

    Forall_as_foldr : forall (i : level) (a : U i) (P : a -> U i) (l : list a) .
                         Forall P l <-> foldr unit (fn h Q . P h & Q) l

    Exists_as_foldr : forall (i : level) (a : U i) (P : a -> U i) (l : list a) .
                         Exists P l <-> foldr void (fn h Q . P h % Q) l

    In : intersect (i : level) . forall (a : U i) . a -> list a -> U i

    In _ _ (nil _) --> void
    In a x (cons _ h t) --> x = h : a % In a x t

    In_as_exists : forall (i : level) (a : U i) (x : a) (l : list a) .
                      In a x l <-> Exists (fn y . x = y : a) l

    Forall_forall : forall (i : level) (a : U i) (P : a -> U i) (l : list a) .
                       Forall P l <-> (forall (x : a) . In a x l -> P x)

    Exists_exists : forall (i : level) (a : U i) (P : a -> U i) (l : list a) .
                       Exists P l <-> (exists (x : a) . In a x l & P x)
