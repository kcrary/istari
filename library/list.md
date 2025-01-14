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

    list_iter a P n c (nil) --> n
    list_iter a P n c (cons h t) --> c h t (list_iter a P n c t)

A simpler case-analysis operation:

    list_case : type:list_case

    list_case (nil) n c --> n
    list_case (cons h t) n c --> c h t

Lists are covariant:

    list_subtype : type:list_subtype


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

    length_leq_form : type:length_leq_form


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

    map_identity : type:map_identity

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

(The first argument, `a`, is implicit in `Forall`, `Exists`, and their
constructors.)

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

    list_eq_by_nth : type:list_eq_by_nth


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


### Keep

    keep : type:keep
         imp:keep

Keeping too many elements is permitted, and results in the full list.

    keep _ zero _ --> nil
    keep _ (succ _) nil --> nil
    keep a (succ n) (cons h t) --> cons h (keep a n t)

    keep_nil : type:keep_nil

    length_keep_min : type:length_keep_min

    length_keep_leq : type:length_keep_leq

    length_keep : type:length_keep

    keep_idem : type:keep_idem

    keep_append_leq : type:keep_append_leq

    keep_append_geq : type:keep_append_geq

    keep_append_eq : type:keep_append_eq

    keep_all : type:keep_all

    keep_map : type:keep_map

    Forall_keep_weaken : type:Forall_keep_weaken

    Exists_keep_weaken : type:Exists_keep_weaken

    In_keep_weaken : type:In_keep_weaken

    nth_keep : type:nth_keep


### Drop

    drop : type:drop
         imp:drop

Dropping too many elements is permitted, and results in the empty list.

    drop _ zero l --> l
    drop _ (succ _) nil --> nil
    drop _ (succ n) (cons h t) --> drop n t

    drop_nil : type:drop_nil

    length_drop : type:length_drop

    drop_plus : type:drop_plus

    drop_append_leq : type:drop_append_leq

    drop_append_geq : type:drop_append_geq

    drop_append_eq : type:drop_append_eq

    drop_all : type:drop_all

    drop_map : type:drop_map

    Forall_drop_weaken : type:Forall_drop_weaken

    Exists_drop_weaken : type:Exists_drop_weaken

    In_drop_weaken : type:In_drop_weaken

    nth_drop : type:nth_drop

    nth_as_drop : type:nth_as_drop

    split_list : type:split_list


### Map_flat

    map_flat : type:map_flat
             imp:map

    map_flat _ b _ (nil) --> nil
    map_flat a b f (cons h t) --> append b (f h) (map_flat a b f t)

    In_map_flat : type:In_map_flat

    map_flat_as_foldr : type:map_flat_as_foldr


### For all pairs of distinct elements

    datatype
      intersect (i : level) .
      forall (a : U i) (P : a -> a -> U i) .
      U i
    of
      Forall_dist : list a -> type =
  
      | Forall_dist_nil :
          Forall_dist nil
  
      | Forall_dist_cons :
          forall h t .
            Forall (P h) t
            -> Forall_dist t
            -> Forall_dist (cons h t)

(The first argument, `a`, is implicit in `Forall_dist` and its
constructors)

    Forall_dist_nil_iff : type:Forall_dist_nil_iff

    Forall_dist_cons_iff : type:Forall_dist_cons_iff

    Forall_dist_append : type:Forall_dist_append

    Forall_dist_append_iff : type:Forall_dist_append_iff

    Forall_dist_implies : type:Forall_dist_implies

    Forall_dist_map : type:Forall_dist_map

    Forall_dist_reverse : type:Forall_dist_reverse

    decidable_Forall_dist_dep : type:decidable_Forall_dist_dep

    decidable_Forall_dist : type:decidable_Forall_dist


### Boolean predicates

    Forallb : type:Forallb

    Forallb f (nil) --> true
    Forallb f (cons h t) --> Bool.andb (f h) (Forallb f t)

    Existsb : type:Existsb

    Existsb f (nil) --> false
    Existsb f (cons h t) --> Bool.orb (f h) (Existsb f t)

    Forall_distb : type:Forall_distb

    Forall_distb f (nil) --> true
    Forall_distb f (cons h t) --> Bool.andb (Forallb (f h) t) (Forall_distb f t)

    istrue_Forallb : type:istrue_Forallb

    istrue_Existsb : type:istrue_Existsb

    istrue_Forall_distb : type:istrue_Forall_distb


### Lists are covariant

    list_subtype : type:list_subtype

Note that this fact relies on `nil` and `cons`'s type argument being
invisible (*i.e.,* taken using `intersect`).
