open:Option
# `Option`

Options are defined:

    datatype
      intersect (i : level) .
      intermediate (a : U i) .
      U i
    of
      option : type =
      | None : option
      | Some : a -> option

Producing:

    option : type:option

    None : type:None

    Some : type:Some

The iterator for options:

    option_iter : type:option_iter

    option_iter a P n s (None) --> n
    option_iter a P n s (Some x) --> s x

A simpler case-analysis operation:

    option_case : type:option_case

    option_case (None) n s --> n
    option_case (Some x) n s --> s x

Options are covariant:

    option_subtype : type:option_subtype


### Operations

    bind : type:bind
         = def:bind
         imp:bind

    bind _ b (None _) _ --> None b
    bind _ _ (Some _ x) f --> f x


    join : type:join
         = def:join
         imp:join

    join a (None _) --> None a
    join _ (Some _ l) --> l


    map : type:map
         = def:map
         imp:map

    map _ b (None _) _ --> None b
    map _ b (Some _ x) f --> Some b (f x)

    map_identity : type:map_identity

    map_compose : type:map_compose

    valof : type:valof
         = def:valof
         imp:valof

    valof _ (None _) x --> x
    valof _ (Some _ x) --> x
