open:List
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

    list : type:list

    nil  : type:nil
         imp:nil

    cons : type:cons
         imp:cons

The syntactic sugar `h :: t` is accepted for `` ` cons _ h t``, as usual.


The iterator for lists:

    list_iter : type:list_iter

    list_iter A P z s (nil _) --> z
    list_iter A P z s (cons _ h t) --> s h t (list_iter A P z s t)


A simpler case-analysis operation:

    list_case : type:list_case
              = def:list_case
              imp:list_case

    list_case _ _ (nil _) z _ --> z
    list_case _ _ (cons _ h t) _ s --> s h t


### Append

    append : type:append
           = def:append
           imp:append

    append _ (nil _) l --> l
    append A (cons _ h t) l --> cons A h (append A t l)

    append_id_l : type:append_id_l

    append_id_r : type:append_id_r

    append_assoc : type:append_assoc


### Length

    length : type:length
           =rec= defrec:length
           imp:length

    length _ (nil _) --> 0
    length A (cons _ _ t) --> succ (length A t)

    length_append : type:length_append


### Fold

    foldr : type:foldr

    foldr _ _ z _ (nil _) --> z
    foldr a b z f (cons _ h t) --> f h (foldr a b z f t)


### Map

    map : type:map

    map _ b _ (nil _) --> nil b
    map a b f (cons _ h t) --> cons b (f h) (map a b f t)

    map_compose : type:map_compose

    
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

    Forall_as_foldr : type:Forall_as_foldr

    Exists_as_foldr : type:Exists_as_foldr

    In : type:In

    In _ _ (nil _) --> void
    In a x (cons _ h t) --> x = h : a % In a x t

    In_as_exists : type:In_as_exists

    Forall_forall : type:Forall_forall

    Exists_exists : type:Exists_exists
