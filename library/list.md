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

The syntactic sugar `h :: t` is accepted for `` `cons _ h t``, as usual.


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

