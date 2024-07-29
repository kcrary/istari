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

    option_iter a P z s (None _) --> z
    option_iter a P z s (Some _ x) --> s x

A simpler case-analysis operation:

    option_case : type:option_case
                = def:option_case
                imp:option_case

    option_case _ _ (None _) n _ --> n
    option_case _ _ (Some _ x) _ s --> s x


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


    valof : type:valof
         = def:valof
         imp:valof

    valof _ (None _) x --> x
    valof _ (Some _ x) --> x
