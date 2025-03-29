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

    list : intersect (i : level) . forall (a : U i) . U i

    nil  : intersect (i : level) (a : U i) . list a

    cons : intersect (i : level) (a : U i) . a -> list a -> list a


The iterator for lists:

    list_iter : intersect (i : level) .
                   forall (a : U i) (P : list a -> U i) .
                     P nil
                     -> (forall (v0 : a) (v1 : list a) . P v1 -> P (v0 :: v1))
                     -> forall (v0 : list a) . P v0

    list_iter a P n c (nil) --> n
    list_iter a P n c (cons h t) --> c h t (list_iter a P n c t)

A simpler case-analysis operation:

    list_case : intersect (i : level) (a b : U i) . list a -> b -> (a -> list a -> b) -> b

    list_case (nil) n c --> n
    list_case (cons h t) n c --> c h t

Lists are covariant:

    list_subtype : forall (i : level) (a b : U i) . a <: b -> list a <: list b


### Append

    append : intersect (i : level) . forall (a : U i) . list a -> list a -> list a
           = fn a l1 l2 . (fnind list_fn : forall (v0 : list [a]) . list a of
                            | nil . l2
                            | cons h v0 . h :: list_fn v0) l1
           (1 implicit argument)

    append _ (nil) l --> l
    append a (cons h t) l --> cons h (append a t l)

    append_id_l : forall (i : level) (a : U i) (l : list a) . append nil l = l : list a

    append_id_r : forall (i : level) (a : U i) (l : list a) . append l nil = l : list a

    append_assoc : forall (i : level) (a : U i) (l1 l2 l3 : list a) .
                      append (append l1 l2) l3 = append l1 (append l2 l3) : list a

    append_cons_assoc : forall (i : level) (a : U i) (x : a) (l1 l2 : list a) .
                           append (x :: l1) l2 = x :: append l1 l2 : list a

    append_eq_nil : forall (i : level) (a : U i) (l1 l2 : list a) .
                       nil = append l1 l2 : list a -> l1 = nil : list a & l2 = nil : list a

    append_eq_cons : forall (i : level) (a : U i) (h : a) (t l1 l2 : list a) .
                        h :: t = append l1 l2 : list a
                        -> (exists (l1' : list a) .
                              l1 = h :: l1' : list a & t = append l1' l2 : list a)
                           % l1 = nil : list a & l2 = h :: t : list a


### Length

    length : intersect (i : level) . forall (a : U i) . list a -> nat
           =rec= fn a l . list_case l 0 (fn v0 t . succ (length t))
           (1 implicit argument)

    length _ (nil) --> 0
    length a (cons t) --> succ (length a t)

    length_append : forall (i : level) (a : U i) (l1 l2 : list a) .
                       length (append l1 l2) = length l1 + length l2 : nat

    length_zero_form : forall (i : level) (a : U i) (l : list a) .
                          length l = 0 : nat -> l = nil : list a

    length_succ_form : forall (i : level) (a : U i) (l : list a) (n : nat) .
                          length l = succ n : nat
                          -> exists (h : a) (t : list a) . l = h :: t : list a

    length_nonzero_form : forall (i : level) (a : U i) (l : list a) .
                             0 < length l -> exists (h : a) (t : list a) . l = h :: t : list a

    length_leq_form : forall (i : level) (a : U i) (l : list a) (n : nat) .
                         n <= length l
                         -> exists (l1 l2 : list a) .
                              l = append l1 l2 : list a & n = length l1 : nat


### Fold

    foldr : intersect (i : level) . forall (a b : U i) . b -> (a -> b -> b) -> list a -> b
          (2 implicit arguments)
    foldr _ _ z _ (nil) --> z
    foldr a b z f (cons h t) --> f h (foldr a b z f t)

    foldl : intersect (i : level) . forall (a b : U i) . b -> (a -> b -> b) -> list a -> b
          (2 implicit arguments)

    foldl _ _ z _ (nil) --> z
    foldl a b z f (cons h t) --> foldl a b (f h z) f t

    foldr_append : forall (i : level) (a b : U i) (z : b) (f : a -> b -> b) (l1 l2 : list a) .
                      foldr z f (append l1 l2) = foldr (foldr z f l2) f l1 : b

    foldl_append : forall (i : level) (a b : U i) (z : b) (f : a -> b -> b) (l1 l2 : list a) .
                      foldl z f (append l1 l2) = foldl (foldl z f l1) f l2 : b


### Map

    map : intersect (i : level) . forall (a b : U i) . (a -> b) -> list a -> list b
        (2 implicit arguments)

    map _ b _ (nil) --> nil
    map a b f (cons h t) --> cons (f h) (map a b f t)

    map_identity : forall (i : level) (a : U i) (l : list a) . map (fn x . x) l = l : list a

    map_compose : forall (i : level) (a b c : U i) (f : b -> c) (g : a -> b) (l : list a) .
                     map f (map g l) = map (fn x . f (g x)) l : list c

    map_append : forall (i : level) (a b : U i) (f : a -> b) (l1 l2 : list a) .
                    map f (append l1 l2) = append (map f l1) (map f l2) : list b

    map_as_foldr : forall (i : level) (a b : U i) (f : a -> b) (l : list a) .
                      map f l = foldr nil (fn h t . f h :: t) l : list b

    length_map : forall (i : level) (a b : U i) (f : a -> b) (l : list a) .
                    length (map f l) = length l : nat

    foldr_map : forall
                   (i : level)
                   (a b c : U i)
                   (z : c)
                   (f : b -> c -> c)
                   (g : a -> b)
                   (l : list a) .
                   foldr z f (map g l) = foldr z (fn h t . f (g h) t) l : c

    foldl_map : forall
                   (i : level)
                   (a b c : U i)
                   (z : c)
                   (f : b -> c -> c)
                   (g : a -> b)
                   (l : list a) .
                   foldl z f (map g l) = foldl z (fn h t . f (g h) t) l : c

    
### Reverse

    reverse : intersect (i : level) . forall (a : U i) . list a -> list a
            (1 implicit argument)

    reverse a (nil) --> nil
    reverse a (cons h t) --> append a (reverse a t) (cons h nil)

    reverse_as_foldl : forall (i : level) (a : U i) (l : list a) .
                          reverse l = foldl nil (fn h t . h :: t) l : list a

    reverse_append : forall (i : level) (a : U i) (l1 l2 : list a) .
                        reverse (append l1 l2) = append (reverse l2) (reverse l1) : list a

    reverse_invol : forall (i : level) (a : U i) (l : list a) . reverse (reverse l) = l : list a

    length_reverse : forall (i : level) (a : U i) (l : list a) .
                        length (reverse l) = length l : nat

    foldl_as_foldr : forall (i : level) (a b : U i) (z : b) (f : a -> b -> b) (l : list a) .
                        foldl z f l = foldr z f (reverse l) : b

    foldr_as_foldl : forall (i : level) (a b : U i) (z : b) (f : a -> b -> b) (l : list a) .
                        foldr z f l = foldl z f (reverse l) : b

    reverse_map : forall (i : level) (a b : U i) (f : a -> b) (l : list a) .
                     reverse (map f l) = map f (reverse l) : list b
    

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

    Forall_as_foldr : forall (i : level) (a : U i) (P : a -> U i) (l : list a) .
                         Forall P l <-> foldr unit (fn h Q . P h & Q) l

    Exists_as_foldr : forall (i : level) (a : U i) (P : a -> U i) (l : list a) .
                         Exists P l <-> foldr void (fn h Q . P h % Q) l

    In : intersect (i : level) . forall (a : U i) . a -> list a -> U i

    In _ _ (nil) --> void
    In a x (cons h t) --> x = h : a % In a x t

    In_as_exists : forall (i : level) (a : U i) (x : a) (l : list a) .
                      In a x l <-> Exists (fn y . x = y : a) l

    Forall_forall : forall (i : level) (a : U i) (P : a -> U i) (l : list a) .
                       Forall P l <-> (forall (x : a) . In a x l -> P x)

    Exists_exists : forall (i : level) (a : U i) (P : a -> U i) (l : list a) .
                       Exists P l <-> (exists (x : a) . In a x l & P x)

    Forall_nil_iff : forall (i : level) (a : U i) (P : a -> U i) . Forall P nil <-> unit

    Exists_nil_iff : forall (i : level) (a : U i) (P : a -> U i) . Exists P nil <-> void

    Forall_cons_iff : forall (i : level) (a : U i) (P : a -> U i) (x : a) (l : list a) .
                         Forall P (x :: l) <-> P x & Forall P l

    Exists_cons_iff : forall (i : level) (a : U i) (P : a -> U i) (x : a) (l : list a) .
                         Exists P (x :: l) <-> P x % Exists P l

    Forall_append : forall (i : level) (a : U i) (P : a -> U i) (l1 l2 : list a) .
                       Forall P l1 -> Forall P l2 -> Forall P (append l1 l2)

    Exists_append_1 : forall (i : level) (a : U i) (P : a -> U i) (l1 l2 : list a) .
                         Exists P l1 -> Exists P (append l1 l2)

    Exists_append_2 : forall (i : level) (a : U i) (P : a -> U i) (l1 l2 : list a) .
                         Exists P l2 -> Exists P (append l1 l2)

    Forall_append_iff : forall (i : level) (a : U i) (P : a -> U i) (l1 l2 : list a) .
                           Forall P (append l1 l2) <-> Forall P l1 & Forall P l2

    Exists_append_iff : forall (i : level) (a : U i) (P : a -> U i) (l1 l2 : list a) .
                           Exists P (append l1 l2) <-> Exists P l1 % Exists P l2

    In_append : forall (i : level) (a : U i) (x : a) (l1 l2 : list a) .
                   In a x (append l1 l2) <-> In a x l1 % In a x l2

    Forall_implies : forall (i : level) (a : U i) (P Q : a -> U i) (l : list a) .
                        (forall (x : a) . P x -> Q x) -> Forall P l -> Forall Q l

    Exists_implies : forall (i : level) (a : U i) (P Q : a -> U i) (l : list a) .
                        (forall (x : a) . P x -> Q x) -> Exists P l -> Exists Q l

    Forall_map : forall (i : level) (a b : U i) (P : b -> U i) (f : a -> b) (l : list a) .
                    Forall P (map f l) <-> Forall (fn x . P (f x)) l

    Exists_map : forall (i : level) (a b : U i) (P : b -> U i) (f : a -> b) (l : list a) .
                    Exists P (map f l) <-> Exists (fn x . P (f x)) l

    In_map : forall (i : level) (a b : U i) (f : a -> b) (x : b) (l : list a) .
                In b x (map f l) <-> (exists (y : a) . In a y l & x = f y : b)

    Forall_reverse : forall (i : level) (a : U i) (P : a -> U i) (l : list a) .
                        Forall P (reverse l) <-> Forall P l

    Exists_reverse : forall (i : level) (a : U i) (P : a -> U i) (l : list a) .
                        Exists P (reverse l) <-> Exists P l

    In_reverse : forall (i : level) (a : U i) (x : a) (l : list a) .
                    In a x (reverse l) <-> In a x l

    In_form : forall (i : level) (a : U i) (x : a) (l : list a) .
                 In a x l -> exists (l1 l2 : list a) . l = append l1 (x :: l2) : list a

    decidable_Forall_dep : forall (i : level) (a : U i) (P : a -> U i) (l : list a) .
                              (forall (x : a) . In a x l -> Decidable.decidable (P x))
                              -> Decidable.decidable (Forall P l)

    decidable_Forall : forall (i : level) (a : U i) (P : a -> U i) .
                          (forall (x : a) . Decidable.decidable (P x))
                          -> forall (l : list a) . Decidable.decidable (Forall P l)

    decidable_Exists_dep : forall (i : level) (a : U i) (P : a -> U i) (l : list a) .
                              (forall (x : a) . In a x l -> Decidable.decidable (P x))
                              -> Decidable.decidable (Exists P l)

    decidable_Exists : forall (i : level) (a : U i) (P : a -> U i) .
                          (forall (x : a) . Decidable.decidable (P x))
                          -> forall (l : list a) . Decidable.decidable (Exists P l)

    decidable_In : forall (i : level) (a : U i) .
                      (forall (x y : a) . Decidable.decidable (x = y : a))
                      -> forall (x : a) (l : list a) . Decidable.decidable (In a x l)


### Nth

    nth : intersect (lv : level) . forall (a : U lv) . list a -> nat -> Option.option a
        (1 implicit argument)

    nth a (nil) _ --> None
    nth a (cons h t) i --> nat_case i (Some h) (fn i' . nth a t i')

    nth_within_length : forall (lv : level) (a : U lv) (l : list a) (i : nat) .
                           i < length l
                             <-> (exists (x : a) . nth l i = Option.Some x : Option.option a)

    nth_outside_length : forall (lv : level) (a : U lv) (l : list a) (i : nat) .
                            length l <= i <-> nth l i = Option.None : Option.option a

    nth_append_left : forall (lv : level) (a : U lv) (l1 l2 : list a) (i : nat) .
                         i < length l1 -> nth (append l1 l2) i = nth l1 i : Option.option a

    nth_append_right : forall (lv : level) (a : U lv) (l1 l2 : list a) (i : nat) .
                          length l1 <= i
                          -> nth (append l1 l2) i = nth l2 (i - length l1) : Option.option a

    nth_map : forall (lv : level) (a b : U lv) (f : a -> b) (l : list a) (i : nat) .
                 nth (map f l) i = Option.map f (nth l i) : Option.option b

    nth_In : forall (lv : level) (a : U lv) (l : list a) (i : nat) .
                Option.option_case (nth l i) unit (fn x . In a x l)

    list_eq_by_nth : forall (i : level) (a : U i) (l l' : list a) .
                        length l = length l' : nat
                        -> (forall (j : nat) . j < length l -> nth l j = nth l' j : Option.option a)
                        -> l = l' : list a


### Zip and Unzip

    zip : intersect (i : level) . forall (a b : U i) . list a -> list b -> list (a & b)
        (2 implicit arguments)

    zip a b (nil) _ --> nil
    zip a b (cons h1 t1) l2 --> list_case b (list (a & b)) 
                                  l2 
                                  nil
                                  (fn h2 t2 . cons (h1 , h2) (zip a b t1 t2))

    unzip : intersect (i : level) . forall (a b : U i) . list (a & b) -> list a & list b
          (2 implicit arguments)

    unzip a b (nil) --> (nil , nil)
    unzip a b (cons h t) --> (cons (h #1) (unzip a b t #1) , cons (h #2) (unzip a b t #2))

    zip_unzip : forall (i : level) (a b : U i) (l : list (a & b)) .
                   zip (unzip l #1) (unzip l #2) = l : list (a & b)

    unzip_zip : forall (i : level) (a b : U i) (l1 : list a) (l2 : list b) .
                   length l1 = length l2 : nat -> unzip (zip l1 l2) = (l1, l2) : (list a & list b)

    append_zip : forall (i : level) (a b : U i) (l1 l1' : list a) (l2 l2' : list b) .
                    length l1 = length l2 : nat
                    -> append (zip l1 l2) (zip l1' l2')
                         = zip (append l1 l1') (append l2 l2')
                         : list (a & b)

    append_unzip : forall (i : level) (a b : U i) (l l' : list (a & b)) .
                      append (unzip l #1) (unzip l' #1) = unzip (append l l') #1 : list a
                      & append (unzip l #2) (unzip l' #2) = unzip (append l l') #2 : list b

    length_zip : forall (i : level) (a b : U i) (l1 : list a) (l2 : list b) .
                    length (zip l1 l2) = Nat.min (length l1) (length l2) : nat

    length_unzip : forall (i : level) (a b : U i) (l : list (a & b)) .
                      length (unzip l #1) = length l : nat & length (unzip l #2) = length l : nat

    reverse_zip : forall (i : level) (a b : U i) (l1 : list a) (l2 : list b) .
                     length l1 = length l2 : nat
                     -> reverse (zip l1 l2) = zip (reverse l1) (reverse l2) : list (a & b)

    reverse_unzip : forall (i : level) (a b : U i) (l : list (a & b)) .
                       reverse (unzip l #1) = unzip (reverse l) #1 : list a
                       & reverse (unzip l #2) = unzip (reverse l) #2 : list b

    nth_zip : forall (lv : level) (a b : U lv) (l1 : list a) (l2 : list b) (i : nat) .
                 nth (zip l1 l2) i
                   = Option.bind
                       (nth l1 i)
                       (fn x . Option.bind (nth l2 i) (fn y . Option.Some (x, y)))
                   : Option.option (a & b)

    nth_unzip : forall (lv : level) (a b : U lv) (l : list (a & b)) (i : nat) .
                   nth (unzip l #1) i = Option.map (fn x . x #1) (nth l i) : Option.option a
                   & nth (unzip l #2) i = Option.map (fn x . x #2) (nth l i) : Option.option b


### Keep

    keep : intersect (i : level) . forall (a : U i) . nat -> list a -> list a
         (1 implicit argument)

Keeping too many elements is permitted, and results in the full list.

    keep _ zero _ --> nil
    keep _ (succ _) nil --> nil
    keep a (succ n) (cons h t) --> cons h (keep a n t)

    keep_nil : forall (i : level) (a : U i) (n : nat) . keep n nil = nil : list a

    length_keep_min : forall (i : level) (a : U i) (n : nat) (l : list a) .
                         length (keep n l) = Nat.min n (length l) : nat

    length_keep_leq : forall (i : level) (a : U i) (n : nat) (l : list a) . length (keep n l) <= n

    length_keep : forall (i : level) (a : U i) (n : nat) (l : list a) .
                     n <= length l -> length (keep n l) = n : nat

    keep_idem : forall (i : level) (a : U i) (n : nat) (l : list a) .
                   keep n (keep n l) = keep n l : list a

    keep_append_leq : forall (i : level) (a : U i) (n : nat) (l1 l2 : list a) .
                         n <= length l1 -> keep n (append l1 l2) = keep n l1 : list a

    keep_append_geq : forall (i : level) (a : U i) (n : nat) (l1 l2 : list a) .
                         length l1 <= n
                         -> keep n (append l1 l2) = append l1 (keep (n - length l1) l2) : list a

    keep_append_eq : forall (i : level) (a : U i) (n : nat) (l1 l2 : list a) .
                        n = length l1 : nat -> keep n (append l1 l2) = l1 : list a

    keep_all : forall (i : level) (a : U i) (l : list a) . keep (length l) l = l : list a

    keep_map : forall (i : level) (a b : U i) (n : nat) (f : a -> b) (l : list a) .
                  keep n (map f l) = map f (keep n l) : list b

    Forall_keep_weaken : forall (i : level) (a : U i) (P : a -> U i) (n : nat) (l : list a) .
                            Forall P l -> Forall P (keep n l)

    Exists_keep_weaken : forall (i : level) (a : U i) (P : a -> U i) (n : nat) (l : list a) .
                            Exists P (keep n l) -> Exists P l

    In_keep_weaken : forall (i : level) (a : U i) (x : a) (n : nat) (l : list a) .
                        In a x (keep n l) -> In a x l

    nth_keep : forall (i : level) (a : U i) (m n : nat) (l : list a) .
                  n < m -> nth (keep m l) n = nth l n : Option.option a


### Drop

    drop : intersect (i : level) . forall (a : U i) . nat -> list a -> list a
         (1 implicit argument)

Dropping too many elements is permitted, and results in the empty list.

    drop _ zero l --> l
    drop _ (succ _) nil --> nil
    drop _ (succ n) (cons h t) --> drop n t

    drop_nil : forall (i : level) (a : U i) (n : nat) . drop n nil = nil : list a

    length_drop : forall (i : level) (a : U i) (n : nat) (l : list a) .
                     length (drop n l) = length l - n : nat

    drop_plus : forall (i : level) (a : U i) (l : list a) (m n : nat) .
                   drop n (drop m l) = drop (m + n) l : list a

    drop_append_leq : forall (i : level) (a : U i) (n : nat) (l1 l2 : list a) .
                         n <= length l1 -> drop n (append l1 l2) = append (drop n l1) l2 : list a

    drop_append_geq : forall (i : level) (a : U i) (n : nat) (l1 l2 : list a) .
                         length l1 <= n -> drop n (append l1 l2) = drop (n - length l1) l2 : list a

    drop_append_eq : forall (i : level) (a : U i) (n : nat) (l1 l2 : list a) .
                        n = length l1 : nat -> drop n (append l1 l2) = l2 : list a

    drop_all : forall (i : level) (a : U i) (l : list a) . drop (length l) l = nil : list a

    drop_map : forall (i : level) (a b : U i) (n : nat) (f : a -> b) (l : list a) .
                  drop n (map f l) = map f (drop n l) : list b

    Forall_drop_weaken : forall (i : level) (a : U i) (P : a -> U i) (n : nat) (l : list a) .
                            Forall P l -> Forall P (drop n l)

    Exists_drop_weaken : forall (i : level) (a : U i) (P : a -> U i) (n : nat) (l : list a) .
                            Exists P (drop n l) -> Exists P l

    In_drop_weaken : forall (i : level) (a : U i) (x : a) (n : nat) (l : list a) .
                        In a x (drop n l) -> In a x l

    nth_drop : forall (i : level) (a : U i) (m n : nat) (l : list a) .
                  nth (drop m l) n = nth l (m + n) : Option.option a

    nth_as_drop : forall (i : level) (a : U i) (l : list a) (n : nat) .
                     nth l n
                       = list_case (drop n l) Option.None (fn h v0 . Option.Some h)
                       : Option.option a

    split_list : forall (i : level) (a : U i) (n : nat) (l : list a) .
                    l = append (keep n l) (drop n l) : list a


### Map_flat

    map_flat : intersect (i : level) . forall (a b : U i) . (a -> list b) -> list a -> list b
             (2 implicit arguments)

    map_flat _ b _ (nil) --> nil
    map_flat a b f (cons h t) --> append b (f h) (map_flat a b f t)

    In_map_flat : forall (i : level) (a b : U i) (f : a -> list b) (x : b) (l : list a) .
                     In b x (map_flat f l) <-> (exists (y : a) . In a y l & In b x (f y))

    map_flat_as_foldr : forall (i : level) (a b : U i) (f : a -> list b) (l : list a) .
                           map_flat f l = foldr nil (fn h t . append (f h) t) l : list b


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

    Forall_dist_nil_iff : forall (i : level) (a : U i) (P : a -> a -> U i) .
                             Forall_dist P nil <-> unit

    Forall_dist_cons_iff : forall (i : level) (a : U i) (P : a -> a -> U i) (x : a) (l : list a) .
                              Forall_dist P (x :: l) <-> Forall (P x) l & Forall_dist P l

    Forall_dist_append : forall (i : level) (a : U i) (P : a -> a -> U i) (l1 l2 : list a) .
                            Forall (fn x . Forall (P x) l2) l1
                            -> Forall_dist P l1
                            -> Forall_dist P l2
                            -> Forall_dist P (append l1 l2)

    Forall_dist_append_iff : forall (i : level) (a : U i) (P : a -> a -> U i) (l1 l2 : list a) .
                                Forall_dist P (append l1 l2)
                                  <-> Forall (fn x . Forall (P x) l2) l1
                                      & Forall_dist P l1
                                      & Forall_dist P l2

    Forall_dist_implies : forall (i : level) (a : U i) (P Q : a -> a -> U i) (l : list a) .
                             (forall (x y : a) . P x y -> Q x y)
                             -> Forall_dist P l
                             -> Forall_dist Q l

    Forall_dist_map : forall
                         (i : level)
                         (a b : U i)
                         (P : b -> b -> U i)
                         (f : a -> b)
                         (l : list a) .
                         Forall_dist P (map f l) <-> Forall_dist (fn x y . P (f x) (f y)) l

    Forall_dist_reverse : forall (i : level) (a : U i) (P : a -> a -> U i) (l : list a) .
                             (forall (x y : a) . P x y -> P y x)
                             -> Forall_dist P (reverse l) <-> Forall_dist P l

    decidable_Forall_dist_dep : forall (i : level) (a : U i) (P : a -> a -> U i) (l : list a) .
                                   (forall (x y : a) .
                                      In a x l -> In a y l -> Decidable.decidable (P x y))
                                   -> Decidable.decidable (Forall_dist P l)

    decidable_Forall_dist : forall (i : level) (a : U i) (P : a -> a -> U i) (l : list a) .
                               (forall (x y : a) . Decidable.decidable (P x y))
                               -> Decidable.decidable (Forall_dist P l)


### Boolean predicates

    Forallb : intersect (i : level) (a : U i) . (a -> bool) -> list a -> bool

    Forallb f (nil) --> true
    Forallb f (cons h t) --> Bool.andb (f h) (Forallb f t)

    Existsb : intersect (i : level) (a : U i) . (a -> bool) -> list a -> bool

    Existsb f (nil) --> false
    Existsb f (cons h t) --> Bool.orb (f h) (Existsb f t)

    Forall_distb : intersect (i : level) (a : U i) . (a -> a -> bool) -> list a -> bool

    Forall_distb f (nil) --> true
    Forall_distb f (cons h t) --> Bool.andb (Forallb (f h) t) (Forall_distb f t)

    istrue_Forallb : forall (i : level) (a : U i) (f : a -> bool) (l : list a) .
                        Bool.istrue (Forallb f l) <-> Forall (fn x . Bool.istrue (f x)) l

    istrue_Existsb : forall (i : level) (a : U i) (f : a -> bool) (l : list a) .
                        Bool.istrue (Existsb f l) <-> Exists (fn x . Bool.istrue (f x)) l

    istrue_Forall_distb : forall (i : level) (a : U i) (f : a -> a -> bool) (l : list a) .
                             Bool.istrue (Forall_distb f l)
                               <-> Forall_dist (fn x y . Bool.istrue (f x y)) l


### Miscellaneous

    list_subtype : forall (i : level) (a b : U i) . a <: b -> list a <: list b

Note that the subtyping principle relies on `nil` and `cons`'s type
argument being invisible (*i.e.,* taken using `intersect`).

    list_eeqtp : forall (i : level) (a b : U i) . a <:> b -> list a <:> list b

    kindlike_list : forall (i : level) (a : U (1 + i)) .
                       a -> Kindlike.kindlike i a -> Kindlike.kindlike i (list a)
