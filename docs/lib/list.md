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

The syntactic sugar `h :: t` is accepted for `` `cons _ h t ``, as usual.


The iterator for lists:

    list_iter : intersect (i : level) .
                   forall (a : U i) (P : list a -> U i) .
                     P nil
                     -> (forall (v0 : a) (v1 : list a) . P v1 -> P (v0 :: v1))
                     -> forall (v0 : list a) . P v0

    list_iter a P z s (nil _) --> z
    list_iter a P z s (cons _ h t) --> s h t (list_iter a P z s t)


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
    append a (cons _ h t) l --> cons a h (append a t l)

    append_id_l : forall (i : level) (a : U i) (l : list a) . append nil l = l : list a

    append_id_r : forall (i : level) (a : U i) (l : list a) . append l nil = l : list a

    append_assoc : forall (i : level) (a : U i) (l1 l2 l3 : list a) .
                      append (append l1 l2) l3 = append l1 (append l2 l3) : list a

    append_cons_assoc : forall (i : level) (a : U i) (x : a) (l1 l2 : list a) .
                           append (x :: l1) l2 = x :: append l1 l2 : list a

    append_eq_cons : forall (i : level) (a : U i) (h : a) (t l1 l2 : list a) .
                        h :: t = append l1 l2 : list a
                        -> (exists (l1' : list a) .
                              l1 = h :: l1' : list a & t = append l1' l2 : list a)
                           % l1 = nil : list a & l2 = h :: t : list a


### Length

    length : intersect (i : level) . forall (a : U i) . list a -> nat
           =rec= fn a l . list_case l 0 (fn v0 t . succ (length t))
           (1 implicit argument)

    length _ (nil _) --> 0
    length a (cons _ _ t) --> succ (length a t)

    length_append : forall (i : level) (a : U i) (l1 l2 : list a) .
                       length (append l1 l2) = length l1 + length l2 : nat

    length_zero_form : forall (i : level) (a : U i) (l : list a) .
                          length l = 0 : nat -> l = nil : list a

    length_succ_form : forall (i : level) (a : U i) (l : list a) (n : nat) .
                          length l = succ n : nat
                          -> exists (h : a) (t : list a) . l = h :: t : list a

    length_nonzero_form : forall (i : level) (a : U i) (l : list a) .
                             0 < length l -> exists (h : a) (t : list a) . l = h :: t : list a


### Fold

    foldr : intersect (i : level) . forall (a b : U i) . b -> (a -> b -> b) -> list a -> b

    foldr _ _ z _ (nil _) --> z
    foldr a b z f (cons _ h t) --> f h (foldr a b z f t)

    foldl : intersect (i : level) . forall (a b : U i) . b -> (a -> b -> b) -> list a -> b

    foldl _ _ z _ (nil _) --> z
    foldl a b z f (cons _ h t) --> foldl a b (f h z) f t

    foldr_append : forall (i : level) (a b : U i) (z : b) (f : a -> b -> b) (l1 l2 : list a) .
                      foldr z f (append l1 l2) = foldr (foldr z f l2) f l1 : b

    foldl_append : forall (i : level) (a b : U i) (z : b) (f : a -> b -> b) (l1 l2 : list a) .
                      foldl z f (append l1 l2) = foldl (foldl z f l1) f l2 : b


### Map

    map : intersect (i : level) . forall (a b : U i) . (a -> b) -> list a -> list b

    map _ b _ (nil _) --> nil b
    map a b f (cons _ h t) --> cons b (f h) (map a b f t)

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

    reverse a (nil _) --> nil a
    reverse a (cons _ h t) --> append a (reverse a t) (cons a h (nil a))

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

    Forall_nil_iff : forall (i : level) (a : U i) (P : a -> U i) . Forall P nil <-> unit

    Exists_nil_iff : forall (i : level) (a : U i) (P : a -> U i) . Exists P nil <-> void

    Forall_cons_iff : forall (i : level) (a : U i) (P : a -> U i) (x : a) (l : list a) .
                         Forall P (x :: l) <-> P x & Forall P l

    Exists_cons_iff : forall (i : level) (a : U i) (P : a -> U i) (x : a) (l : list a) .
                         Exists P (x :: l) <-> P x % Exists P l

    Forall_append : forall (i : level) (a : U i) (P : a -> U i) (l1 l2 : list a) .
                       Forall P (append l1 l2) <-> Forall P l1 & Forall P l2

    Exists_append : forall (i : level) (a : U i) (P : a -> U i) (l1 l2 : list a) .
                       Exists P (append l1 l2) <-> Exists P l1 % Exists P l2

    In_append : forall (i : level) (a : U i) (x : a) (l1 l2 : list a) .
                   In a x (append l1 l2) <-> In a x l1 % In a x l2

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


### Nth

    nth : intersect (lv : level) . forall (a : U lv) . list a -> nat -> option a

    nth a (nil _) _ --> None a
    nth a (cons _ h t) i --> nat_case i (Some a h) (fn i' . nth a t i')

    nth_within_length : forall (lv : level) (a : U lv) (l : list a) (i : nat) .
                           i < length l <-> (exists (x : a) . nth l i = Some x : option a)

    nth_outside_length : forall (lv : level) (a : U lv) (l : list a) (i : nat) .
                            length l <= i <-> nth l i = None : option a

    nth_append_left : forall (lv : level) (a : U lv) (l1 l2 : list a) (i : nat) .
                         i < length l1 -> nth (append l1 l2) i = nth l1 i : option a

    nth_append_right : forall (lv : level) (a : U lv) (l1 l2 : list a) (i : nat) .
                          length l1 <= i
                          -> nth (append l1 l2) i = nth l2 (i - length l1) : option a

    nth_map : forall (lv : level) (a b : U lv) (f : a -> b) (l : list a) (i : nat) .
                 nth (map f l) i = Option.map f (nth l i) : option b

    nth_In : forall (lv : level) (a : U lv) (l : list a) (i : nat) .
                Option.option_case (nth l i) unit (fn x . In a x l)
