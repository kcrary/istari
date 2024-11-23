open:Permutation
open:List
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

    Perm : type:Perm
         imp:Perm

    Perm_nil : type:Perm_nil

    Perm_cons : type:Perm_cons

    Perm_swap : type:Perm_swap

    Perm_trans : type:Perm_trans


Operations on permutations:

    Perm_refl : type:Perm_refl

    Perm_symm : type:Perm_symm

    Perm_append_right : type:Perm_append_right

    Perm_append_left : type:Perm_append_left

    Perm_append : type:Perm_append

    Perm_cons_snoc : type:Perm_cons_snoc

    Perm_snoc_cons : type:Perm_snoc_cons

    Perm_cons_middle : type:Perm_cons_middle

    Perm_middle_cons : type:Perm_middle_cons

    Perm_append_swap : type:Perm_append_swap


If two lists in permuation contain the same element, then the rest of
the lists are in permutation:

    Perm_middle_invert : type:Perm_middle_invert

It is proven using the lemma:

    Perm_middle_form : type:Perm_middle_form

A corollary is when the distinguished element is first:

    Perm_cons_invert : type:Perm_cons_invert


The effect of permutations on other list-related concepts:

    Perm_implies_In : type:Perm_implies_In

    Perm_implies_In_iff : type:Perm_implies_In_iff

    length_Perm : type:length_Perm

    Forall_Perm : type:Forall_Perm

    Forall_Perm_Iff : type:Forall_Perm_iff

    Exists_Perm : type:Exists_Perm

    Exists_Perm_iff : type:Exists_Perm_iff

    Perm_reverse : type:Perm_reverse

    reverse_Perm : type:reverse_Perm

    Perm_map : type:Perm_map

    foldr_Perm : type:foldr_Perm

    foldl_Perm : type:foldl_Perm

    Forall_dist_Perm : type:Forall_dist_Perm

    Forall_dist_Perm_iff : type:Forall_dist_Perm_iff

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

    permute : type:permute

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

    Perm_permute : type:Perm_permute

    Perm_impl_permute : type:Perm_impl_permute


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

    PPerm : type:PPerm
         imp:PPerm

    PPerm_nil : type:PPerm_nil

    PPerm_cons : type:PPerm_cons

    PPerm_swap : type:PPerm_swap

    PPerm_trans : type:PPerm_trans

    PPerm_drop : type:PPerm_drop

    PPerm_refl : type:PPerm_refl

    Perm_impl_PPerm : type:Perm_impl_PPerm

    PPerm_drop_all : type:PPerm_drop_all    

    PPerm_append_right : type:PPerm_append_right

    PPerm_append_left : type:PPerm_append_left

    PPerm_append : type:PPerm_append

    PPerm_cons_snoc : type:PPerm_cons_snoc

    PPerm_snoc_cons : type:PPerm_snoc_cons

    PPerm_cons_middle : type:PPerm_cons_middle

    PPerm_middle_cons : type:PPerm_middle_cons

    PPerm_drop_middle : type:PPerm_drop_middle

    PPerm_append_swap : type:PPerm_append_swap

    PPerm_keep : type:PPerm_keep

    PPerm_drops : type:PPerm_drops

    PPerm_middle_invert : type:PPerm_middle_invert

    PPerm_middle_form : type:PPerm_middle_form

    PPerm_cons_invert : type:PPerm_cons_invert

    PPerm_implies_In : type:PPerm_implies_In

    length_PPerm : type:length_PPerm

    Forall_PPerm : type:Forall_PPerm

    Exists_PPerm : type:Exists_PPerm

    PPerm_reverse_r : type:PPerm_reverse_r

    PPerm_reverse_l : type:PPerm_reverse_l

    reverse_PPerm : type:reverse_PPerm

    PPerm_map : type:PPerm_map

    Forall_dist_PPerm : type:Forall_dist_PPerm

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

    ppermute : type:ppermute

    ppermute (pperm_refl) l --> l
  
    ppermute (pperm_cons p) nil --> nil

    ppermute (pperm_cons p) (cons h t) --> cons h (ppermute p t)

    ppermute (pperm_swap) nil --> nil

    ppermute (pperm_swap) (cons x nil) --> cons x nil

    ppermute (pperm_swap) (cons x (cons y t)) --> cons y (cons x t)

    ppermute (pperm_trans p1 p2) l --> ppermute p2 (ppermute p1 l)

    ppermute (pperm_drop) nil --> nil

    ppermute (pperm_drop) (cons h t) --> t

    PPerm_ppermute : type:PPerm_ppermute

    PPerm_impl_ppermute : type:PPerm_impl_ppermute
