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

The iterator for lists:

    list_iter : intersect (i : level) .
                   forall (a : U i) (v0 : list a -> U i) .
                     v0 nil
                     -> (forall (v1 : a) (v2 : list a) . v0 v2 -> v0 (v1 :: v2))
                     -> forall (v1 : list a) . v0 v1

A simpler case-analysis operation:

    list_case : intersect (i : level) .
                   forall (a : U i) (b : U i) .
                     list a -> b -> (a -> list a -> b) -> b
              = fn a b l mnil mcons .
                   list_iter a (fn v0 . b) mnil (fn h t v0 . mcons h t) l


### Append

    append : intersect (i : level) .
                forall (a : U i) . list a -> list a -> list a

    append_id_l : forall (i : level) (a : U i) (l : list a) .
                     append nil l = l : list a

    append_id_r : forall (i : level) (a : U i) (l : list a) .
                     append l nil = l : list a

    append_assoc : forall
                      (i : level)
                      (a : U i)
                      (l1 : list a)
                      (l2 : list a)
                      (l3 : list a) .
                      append (append l1 l2) l3
                        = append l1 (append l2 l3)
                        : list a


### Length

    length : intersect (i : level) . forall (a : U i) . list a -> nat

    length_append : forall (i : level) (a : U i) (l1 : list a) (l2 : list a) .
                       length (append l1 l2) = length l1 + length l2 : nat

