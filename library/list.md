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

The iterator for lists:

    list_iter : type:list_iter

A simpler case-analysis operation:

    list_case : type:list_case
              = def:list_case


### Append

    append : type:append

    append_id_l : type:append_id_l

    append_id_r : type:append_id_r

    append_assoc : type:append_assoc


### Length

    length : type:length

    length_append : type:length_append

