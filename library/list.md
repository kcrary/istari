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

The syntactic sugar `h :: t` is accepted for `` `cons _ h t ``, as usual.


The iterator for lists:

    list_iter : type:list_iter

    list_iter a P z s (nil _) --> z
    list_iter a P z s (cons _ h t) --> s h t (list_iter a P z s t)


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
    append a (cons _ h t) l --> cons a h (append a t l)

    append_id_l : type:append_id_l

    append_id_r : type:append_id_r

    append_assoc : type:append_assoc

    append_cons_assoc : type:append_cons_assoc

    append_eq_nil : type:append_eq_nil

    append_eq_cons : type:append_eq_cons


### Length

    length : type:length
           =rec= defrec:length
           imp:length

    length _ (nil _) --> 0
    length a (cons _ _ t) --> succ (length a t)

    length_append : type:length_append

    length_zero_form : type:length_zero_form

    length_succ_form : type:length_succ_form

    length_nonzero_form : type:length_nonzero_form


### Fold

    foldr : type:foldr
          imp:foldr
    foldr _ _ z _ (nil _) --> z
    foldr a b z f (cons _ h t) --> f h (foldr a b z f t)

    foldl : type:foldl
          imp:foldl          

    foldl _ _ z _ (nil _) --> z
    foldl a b z f (cons _ h t) --> foldl a b (f h z) f t

    foldr_append : type:foldr_append

    foldl_append : type:foldl_append


### Map

    map : type:map
        imp:map

    map _ b _ (nil _) --> nil b
    map a b f (cons _ h t) --> cons b (f h) (map a b f t)

    map_compose : type:map_compose

    map_append : type:map_append

    map_as_foldr : type:map_as_foldr

    length_map : type:length_map

    foldr_map : type:foldr_map

    foldl_map : type:foldl_map

    
### Reverse

    reverse : type:reverse
            imp:reverse

    reverse a (nil _) --> nil a
    reverse a (cons _ h t) --> append a (reverse a t) (cons a h (nil a))

    reverse_as_foldl : type:reverse_as_foldl

    reverse_append : type:reverse_append

    reverse_invol : type:reverse_invol

    length_reverse : type:length_reverse

    foldl_as_foldr : type:foldl_as_foldr

    foldr_as_foldl : type:foldr_as_foldl

    reverse_map : type:reverse_map
    

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

    Forall_nil_iff : type:Forall_nil_iff

    Exists_nil_iff : type:Exists_nil_iff

    Forall_cons_iff : type:Forall_cons_iff

    Exists_cons_iff : type:Exists_cons_iff

    Forall_append : type:Forall_append

    Exists_append_1 : type:Exists_append_1

    Exists_append_2 : type:Exists_append_2

    Forall_append_iff : type:Forall_append_iff

    Exists_append_iff : type:Exists_append_iff

    In_append : type:In_append

    Forall_implies : type:Forall_implies

    Exists_implies : type:Exists_implies

    Forall_map : type:Forall_map

    Exists_map : type:Exists_map

    In_map : type:In_map

    Forall_reverse : type:Forall_reverse

    Exists_reverse : type:Exists_reverse

    In_reverse : type:In_reverse


### Nth

    nth : type:nth
        imp:nth

    nth a (nil _) _ --> None a
    nth a (cons _ h t) i --> nat_case i (Some a h) (fn i' . nth a t i')

    nth_within_length : type:nth_within_length

    nth_outside_length : type:nth_outside_length

    nth_append_left : type:nth_append_left

    nth_append_right : type:nth_append_right

    nth_map : type:nth_map

    nth_In : type:nth_In


### Zip and Unzip

    zip : type:zip
        imp:zip

    zip a b (nil _) _ --> nil (a & b)
    zip a b (cons _ h1 t1) l2 --> list_case b (list (a & b)) 
                                    l2 
                                    (nil (a & b)) 
                                    (fn h2 t2 . cons (a & b) (h1 , h2) (zip a b t1 t2))

    unzip : type:unzip
          imp:unzip

    unzip a b (nil _) --> (nil a , nil b)
    unzip a b (cons _ h t) --> (cons a (h #1) (unzip a b t #1) , cons b (h #2) (unzip a b t #2))

    zip_unzip : type:zip_unzip

    unzip_zip : type:unzip_zip

    append_zip : type:append_zip

    append_unzip : type:append_unzip

    length_zip : type:length_zip

    length_unzip : type:length_unzip

    reverse_zip : type:reverse_zip

    reverse_unzip : type:reverse_unzip

    nth_zip : type:nth_zip

    nth_unzip : type:nth_unzip
