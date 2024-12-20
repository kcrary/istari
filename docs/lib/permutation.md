# `Permutation`

The module provides predicates for expressing permuations and partial
permutations of lists.


### Permutations

The `Perm l l'` predicate expresses that `l` and `l'` are permuations
of one another:

    datatype
      intersect (i : level) .
      forall (a : U i) .
      U i
    of
      Perm : list a -> list a -> type =
      
      | Perm_nil :
          Perm nil nil
  
      | Perm_cons :
          forall h t t' .
            Perm t t'
            -> Perm (h :: t) (h :: t')
  
      | Perm_swap :
          forall x y t .
            Perm (x :: y :: t) (y :: x :: t)
  
      | Perm_trans :
          forall l1 l2 l3 .
            Perm l1 l2
            -> Perm l2 l3
            -> Perm l1 l3

Producing:

    Perm : intersect (i : level) . forall (a : U i) . list a -> list a -> U i
         (1 implicit argument)

    Perm_nil : intersect (i : level) . forall (a : U i) . Perm nil nil

    Perm_cons : intersect (i : level) .
                   forall (a : U i) (h : a) (t t' : list a) . Perm t t' -> Perm (h :: t) (h :: t')

    Perm_swap : intersect (i : level) .
                   forall (a : U i) (x y : a) (t : list a) . Perm (x :: y :: t) (y :: x :: t)

    Perm_trans : intersect (i : level) .
                    forall (a : U i) (l1 l2 l3 : list a) . Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3


Operations on permutations:

    Perm_refl : intersect (i : level) . forall (a : U i) (l : list a) . Perm l l

    Perm_symm : intersect (i : level) .
                   forall (a : U i) (l1 l2 : list a) . Perm l1 l2 -> Perm l2 l1

    Perm_append_right : forall (i : level) (a : U i) (l1 l1' l2 : list a) .
                           Perm l1 l1' -> Perm (append l1 l2) (append l1' l2)

    Perm_append_left : forall (i : level) (a : U i) (l1 l2 l2' : list a) .
                          Perm l2 l2' -> Perm (append l1 l2) (append l1 l2')

    Perm_append : forall (i : level) (a : U i) (l1 l1' l2 l2' : list a) .
                     Perm l1 l1' -> Perm l2 l2' -> Perm (append l1 l2) (append l1' l2')

    Perm_cons_snoc : forall (i : level) (a : U i) (h : a) (t : list a) .
                        Perm (h :: t) (append t (h :: nil))

    Perm_snoc_cons : forall (i : level) (a : U i) (h : a) (t : list a) .
                        Perm (append t (h :: nil)) (h :: t)

    Perm_cons_middle : forall (i : level) (a : U i) (x : a) (l1 l2 : list a) .
                          Perm (x :: append l1 l2) (append l1 (x :: l2))

    Perm_middle_cons : forall (i : level) (a : U i) (x : a) (l1 l2 : list a) .
                          Perm (append l1 (x :: l2)) (x :: append l1 l2)

    Perm_append_swap : forall (i : level) (a : U i) (l1 l2 : list a) .
                          Perm (append l1 l2) (append l2 l1)


If two lists in permuation contain the same element, then the rest of
the lists are in permutation:

    Perm_middle_invert : forall (i : level) (a : U i) (x : a) (l1 l1' l2 l2' : list a) .
                            Perm (append l1 (x :: l2)) (append l1' (x :: l2'))
                            -> Perm (append l1 l2) (append l1' l2')

It is proven using the lemma:

    Perm_middle_form : forall (i : level) (a : U i) (x : a) (l1 l2 m : list a) .
                          Perm (append l1 (x :: l2)) m
                          -> exists (m1 m2 : list a) .
                               m = append m1 (x :: m2) : list a
                               & Perm (append l1 l2) (append m1 m2)

A corollary is when the distinguished element is first:

    Perm_cons_invert : forall (i : level) (a : U i) (x : a) (l l' : list a) .
                          Perm (x :: l) (x :: l') -> Perm l l'


The effect of permutations on other list-related concepts:

    Perm_implies_In : forall (i : level) (a : U i) (l l' : list a) .
                         Perm l l' -> forall (x : a) . In a x l -> In a x l'

    Perm_implies_In_iff : forall (i : level) (a : U i) (l l' : list a) .
                             Perm l l' -> forall (x : a) . In a x l <-> In a x l'

    length_Perm : forall (i : level) (a : U i) (l l' : list a) .
                     Perm l l' -> length l = length l' : nat

    Forall_Perm : forall (i : level) (a : U i) (P : a -> U i) (l l' : list a) .
                     Perm l l' -> Forall P l -> Forall P l'

    Forall_Perm_Iff : forall (i : level) (a : U i) (P : a -> U i) (l l' : list a) .
                         Perm l l' -> Forall P l <-> Forall P l'

    Exists_Perm : forall (i : level) (a : U i) (P : a -> U i) (l l' : list a) .
                     Perm l l' -> Exists P l -> Exists P l'

    Exists_Perm_iff : forall (i : level) (a : U i) (P : a -> U i) (l l' : list a) .
                         Perm l l' -> Exists P l <-> Exists P l'

    Perm_reverse : forall (i : level) (a : U i) (l : list a) . Perm l (reverse l)

    reverse_Perm : forall (i : level) (a : U i) (l l' : list a) .
                      Perm l l' -> Perm (reverse l) (reverse l')

    Perm_map : forall (i : level) (a b : U i) (f : a -> b) (l l' : list a) .
                  Perm l l' -> Perm (map f l) (map f l')

    foldr_Perm : forall (i : level) (a b : U i) (z : b) (f : a -> b -> b) .
                    (forall (x x' : a) (y : b) . f x (f x' y) = f x' (f x y) : b)
                    -> forall (l l' : list a) . Perm l l' -> foldr z f l = foldr z f l' : b

    foldl_Perm : forall (i : level) (a b : U i) (z : b) (f : a -> b -> b) .
                    (forall (x x' : a) (y : b) . f x (f x' y) = f x' (f x y) : b)
                    -> forall (l l' : list a) . Perm l l' -> foldl z f l = foldl z f l' : b

    Forall_dist_Perm : forall (i : level) (a : U i) (P : a -> a -> U i) (l l' : list a) .
                          (forall (x y : a) . P x y -> P y x)
                          -> Perm l l'
                          -> Forall_dist P l
                          -> Forall_dist P l'

    Forall_dist_Perm_iff : forall (i : level) (a : U i) (P : a -> a -> U i) (l l' : list a) .
                              (forall (x y : a) . P x y -> P y x)
                              -> Perm l l'
                              -> Forall_dist P l <-> Forall_dist P l'

We can isolate a permutation as its own object:

    datatype
      intersect (i : level) .
      U i
    of
      perm : type =
      | perm_refl : perm
      | perm_cons : perm -> perm
      | perm_swap : perm
      | perm_trans : perm -> perm -> perm

The `permute` operation applies a permutation to a list:

    permute : intersect (i : level) (a : U i) . perm -> list a -> list a

    permute (perm_refl) l --> l
  
    permute (perm_cons p) nil --> nil

    permute (perm_cons p) (cons h t) --> cons h (permute p t)

    permute (perm_swap) nil --> nil

    permute (perm_swap) (cons x nil) --> cons x nil

    permute (perm_swap) (cons x (cons y t)) --> cons y (cons x t)

    permute (perm_trans p1 p2) l --> permute p2 (permute p1 l)

Note that when a list is too short for `permute` to perform its usual
action, it does nothing.

Lists are permutations of one another exactly when one can be obtained
from the other by a permutation:

    Perm_permute : forall (i : level) (a : U i) (p : perm) (l : list a) . Perm l (permute p l)

    Perm_impl_permute : forall (i : level) (a : U i) (l l' : list a) .
                           Perm l l' -> exists (p : perm) . permute p l = l' : list a


### Partial permutations

We can recapitulate most of the above for partial permutations.

    datatype
      intersect (i : level) .
      forall (a : U i) .
      U i
    of
      PPerm : list a -> list a -> type =
      
      | PPerm_nil :
          PPerm nil nil
  
      | PPerm_cons :
          forall h t t' .
            PPerm t t'
            -> PPerm (h :: t) (h :: t')
  
      | PPerm_swap :
          forall x y t .
            PPerm (x :: y :: t) (y :: x :: t)
  
      | PPerm_trans :
          forall l1 l2 l3 .
            PPerm l1 l2
            -> PPerm l2 l3
            -> PPerm l1 l3
  
      | PPerm_drop :
          forall h t .
            PPerm (h :: t) t

Note the addition of `PPerm_drop`.

    PPerm : intersect (i : level) . forall (a : U i) . list a -> list a -> U i
         (1 implicit argument)

    PPerm_nil : intersect (i : level) . forall (a : U i) . PPerm nil nil

    PPerm_cons : intersect (i : level) .
                    forall (a : U i) (h : a) (t t' : list a) .
                      PPerm t t' -> PPerm (h :: t) (h :: t')

    PPerm_swap : intersect (i : level) .
                    forall (a : U i) (x y : a) (t : list a) . PPerm (x :: y :: t) (y :: x :: t)

    PPerm_trans : intersect (i : level) .
                     forall (a : U i) (l1 l2 l3 : list a) .
                       PPerm l1 l2 -> PPerm l2 l3 -> PPerm l1 l3

    PPerm_drop : intersect (i : level) . forall (a : U i) (h : a) (t : list a) . PPerm (h :: t) t

    PPerm_refl : intersect (i : level) . forall (a : U i) (l : list a) . PPerm l l

    Perm_impl_PPerm : forall (i : level) (a : U i) (l l' : list a) . Perm l l' -> PPerm l l'

    PPerm_drop_all : forall (i : level) (a : U i) (l : list a) . PPerm l nil

    PPerm_append_right : forall (i : level) (a : U i) (l1 l1' l2 : list a) .
                            PPerm l1 l1' -> PPerm (append l1 l2) (append l1' l2)

    PPerm_append_left : forall (i : level) (a : U i) (l1 l2 l2' : list a) .
                           PPerm l2 l2' -> PPerm (append l1 l2) (append l1 l2')

    PPerm_append : forall (i : level) (a : U i) (l1 l1' l2 l2' : list a) .
                      PPerm l1 l1' -> PPerm l2 l2' -> PPerm (append l1 l2) (append l1' l2')

    PPerm_cons_snoc : forall (i : level) (a : U i) (h : a) (t : list a) .
                         PPerm (h :: t) (append t (h :: nil))

    PPerm_snoc_cons : forall (i : level) (a : U i) (h : a) (t : list a) .
                         PPerm (append t (h :: nil)) (h :: t)

    PPerm_cons_middle : forall (i : level) (a : U i) (x : a) (l1 l2 : list a) .
                           PPerm (x :: append l1 l2) (append l1 (x :: l2))

    PPerm_middle_cons : forall (i : level) (a : U i) (x : a) (l1 l2 : list a) .
                           PPerm (append l1 (x :: l2)) (x :: append l1 l2)

    PPerm_drop_middle : forall (i : level) (a : U i) (x : a) (l1 l2 : list a) .
                           PPerm (append l1 (x :: l2)) (append l1 l2)

    PPerm_append_swap : forall (i : level) (a : U i) (l1 l2 : list a) .
                           PPerm (append l1 l2) (append l2 l1)

    PPerm_keep : forall (i : level) (a : U i) (l : list a) (n : nat) . PPerm l (keep n l)

    PPerm_drops : forall (i : level) (a : U i) (l : list a) (n : nat) . PPerm l (drop n l)

    PPerm_middle_invert : forall (i : level) (a : U i) (x : a) (l1 l1' l2 l2' : list a) .
                             PPerm (append l1 (x :: l2)) (append l1' (x :: l2'))
                             -> PPerm (append l1 l2) (append l1' l2')

    PPerm_middle_form : forall (i : level) (a : U i) (x : a) (l1 l2 m : list a) .
                           PPerm (append l1 (x :: l2)) m
                           -> (exists (m1 m2 : list a) .
                                 m = append m1 (x :: m2) : list a
                                 & PPerm (append l1 l2) (append m1 m2))
                              % PPerm (append l1 l2) m

    PPerm_cons_invert : forall (i : level) (a : U i) (x : a) (l l' : list a) .
                           PPerm (x :: l) (x :: l') -> PPerm l l'

    PPerm_implies_In : forall (i : level) (a : U i) (l l' : list a) .
                          PPerm l l' -> forall (x : a) . In a x l' -> In a x l

    length_PPerm : forall (i : level) (a : U i) (l l' : list a) .
                      PPerm l l' -> length l' <= length l

    Forall_PPerm : forall (i : level) (a : U i) (P : a -> U i) (l l' : list a) .
                      PPerm l l' -> Forall P l -> Forall P l'

    Exists_PPerm : forall (i : level) (a : U i) (P : a -> U i) (l l' : list a) .
                      PPerm l l' -> Exists P l' -> Exists P l

    PPerm_reverse_r : forall (i : level) (a : U i) (l : list a) . PPerm l (reverse l)

    PPerm_reverse_l : forall (i : level) (a : U i) (l : list a) . PPerm (reverse l) l

    reverse_PPerm : forall (i : level) (a : U i) (l l' : list a) .
                       PPerm l l' -> PPerm (reverse l) (reverse l')

    PPerm_map : forall (i : level) (a b : U i) (f : a -> b) (l l' : list a) .
                   PPerm l l' -> PPerm (map f l) (map f l')

    Forall_dist_PPerm : forall (i : level) (a : U i) (P : a -> a -> U i) (l l' : list a) .
                           (forall (x y : a) . P x y -> P y x)
                           -> PPerm l l'
                           -> Forall_dist P l
                           -> Forall_dist P l'

    datatype
      intersect (i : level) .
      U i
    of
      pperm : type =
      | pperm_refl : pperm
      | pperm_cons : pperm -> pperm
      | pperm_swap : pperm
      | pperm_trans : pperm -> pperm -> pperm
      | pperm_drop : pperm

    ppermute : intersect (i : level) (a : U i) . pperm -> list a -> list a

    ppermute (pperm_refl) l --> l
  
    ppermute (pperm_cons p) nil --> nil

    ppermute (pperm_cons p) (cons h t) --> cons h (ppermute p t)

    ppermute (pperm_swap) nil --> nil

    ppermute (pperm_swap) (cons x nil) --> cons x nil

    ppermute (pperm_swap) (cons x (cons y t)) --> cons y (cons x t)

    ppermute (pperm_trans p1 p2) l --> ppermute p2 (ppermute p1 l)

    ppermute (pperm_drop) nil --> nil

    ppermute (pperm_drop) (cons h t) --> t

    PPerm_ppermute : forall (i : level) (a : U i) (p : pperm) (l : list a) .
                        PPerm l (ppermute p l)

    PPerm_impl_ppermute : forall (i : level) (a : U i) (l l' : list a) .
                             PPerm l l' -> exists (p : pperm) . ppermute p l = l' : list a


### Rearrangements

Rearrangement by successive insertion is less general than
permutations, and consequently they can be represented less verbosely,
by a list of numbers.

    insert : intersect (i : level) (a : U i) . nat -> a -> list a -> list a

    insert (zero) x l --> x :: l
    insert (succ _) x (nil) --> x :: nil
    insert (succ n) x (cons h t) --> h :: insert n x t

    rearrange : intersect (i : level) (a : U i) . list nat -> list a -> list a

    rearrange (nil) l --> l
    rearrange (cons _ _) (nil) --> nil
    rearrange (cons n p) (cons h t) --> insert n h (rearrange p t)

    Perm_insert : forall (i : level) (a : U i) (n : nat) (h : a) (t : list a) .
                     Perm (h :: t) (insert n h t)

    Perm_rearrange : forall (i : level) (a : U i) (p : list nat) (l : list a) .
                        Perm l (rearrange p l)

