open:List
# `List`

Lists are defined:

    datatype
      intersect (i : level) .
      intermediate (a : U i) .
      U i
    of
      list : type =
      | nil : list
      | cons : a -> list -> list

Producing:

    list : type:list

    nil  : type:nil

    cons : type:cons



The iterator for lists:

    list_iter : type:list_iter

    list_iter a P z s (nil) --> z
    list_iter a P z s (cons h t) --> s h t (list_iter a P z s t)


A simpler case-analysis operation:

    list_case : type:list_case
              = def:list_case
              imp:list_case

    list_case _ _ (nil) z _ --> z
    list_case _ _ (cons h t) _ s --> s h t


### Append

    append : type:append
           = def:append
           imp:append

    append _ (nil) l --> l
    append a (cons h t) l --> cons h (append a t l)

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

    length _ (nil) --> 0
    length a (cons t) --> succ (length a t)

    length_append : type:length_append

    length_zero_form : type:length_zero_form

    length_succ_form : type:length_succ_form

    length_nonzero_form : type:length_nonzero_form


### Fold

    foldr : type:foldr
          imp:foldr
    foldr _ _ z _ (nil) --> z
    foldr a b z f (cons h t) --> f h (foldr a b z f t)

    foldl : type:foldl
          imp:foldl          

    foldl _ _ z _ (nil) --> z
    foldl a b z f (cons h t) --> foldl a b (f h z) f t

    foldr_append : type:foldr_append

    foldl_append : type:foldl_append


### Map

    map : type:map
        imp:map

    map _ b _ (nil) --> nil
    map a b f (cons h t) --> cons (f h) (map a b f t)

    map_compose : type:map_compose

    map_append : type:map_append

    map_as_foldr : type:map_as_foldr

    length_map : type:length_map

    foldr_map : type:foldr_map

    foldl_map : type:foldl_map

    
### Reverse

    reverse : type:reverse
            imp:reverse

    reverse a (nil) --> nil
    reverse a (cons h t) --> append a (reverse a t) (cons h nil)

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

    In _ _ (nil) --> void
    In a x (cons h t) --> x = h : a % In a x t

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

    decidable_Forall_dep : type:decidable_Forall_dep

    decidable_Forall : type:decidable_Forall

    decidable_Exists_dep : type:decidable_Exists_dep

    decidable_Exists : type:decidable_Exists

    decidable_In : type:decidable_In


### Nth

    nth : type:nth
        imp:nth

    nth a (nil) _ --> None
    nth a (cons h t) i --> nat_case i (Some h) (fn i' . nth a t i')

    nth_within_length : type:nth_within_length

    nth_outside_length : type:nth_outside_length

    nth_append_left : type:nth_append_left

    nth_append_right : type:nth_append_right

    nth_map : type:nth_map

    nth_In : type:nth_In


### Zip and Unzip

    zip : type:zip
        imp:zip

    zip a b (nil) _ --> nil
    zip a b (cons h1 t1) l2 --> list_case b (list (a & b)) 
                                  l2 
                                  nil
                                  (fn h2 t2 . cons (h1 , h2) (zip a b t1 t2))

    unzip : type:unzip
          imp:unzip

    unzip a b (nil) --> (nil , nil)
    unzip a b (cons h t) --> (cons (h #1) (unzip a b t #1) , cons (h #2) (unzip a b t #2))

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


### Drop

    drop : type:drop
         imp:drop

Dropping too many elements is permitted, and results in the empty list.

    drop _ zero l --> l
    drop a (succ n) l --> list_case a (list a) l nil (fn _ l' . drop n l')

    drop_nil : type:drop_nil

    length_drop : type:length_drop

    drop_append_leq : type:drop_append_leq

    drop_append_geq : type:drop_append_geq

    drop_append_eq : type:drop_append_eq

    drop_map : type:drop_map

    Forall_drop_weaken : type:Forall_drop_weaken

    Exists_drop_weaken : type:Exists_drop_weaken

    In_drop_weaken : type:In_drop_weaken

    nth_drop : type:nth_drop

    nth_as_drop : type:nth_as_drop


### Map_flat

    map_flat : type:map_flat
             imp:map

    map_flat _ b _ (nil) --> nil
    map_flat a b f (cons h t) --> append b (f h) (map_flat a b f t)

    In_map_flat : type:In_map_flat

    map_flat_as_foldr : type:map_flat_as_foldr
