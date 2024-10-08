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

    option : intersect (i : level) . forall (a : U i) . U i

    None : intersect (i : level) (a : U i) . option a

    Some : intersect (i : level) (a : U i) . a -> option a

The iterator for options:

    option_iter : intersect (i : level) .
                     forall (a : U i) (P : option a -> U i) .
                       P None -> (forall (v0 : a) . P (Some v0)) -> forall (v0 : option a) . P v0

    option_iter a P z s (None _) --> z
    option_iter a P z s (Some _ x) --> s x

A simpler case-analysis operation:

    option_case : intersect (i : level) . forall (a b : U i) . option a -> b -> (a -> b) -> b
                = fn a b l mnone msome . option_iter a (fn v0 . b) mnone msome l
                (2 implicit arguments)

    option_case _ _ (None _) n _ --> n
    option_case _ _ (Some _ x) _ s --> s x

Options are covariant:

    option_subtype : intersect (i : level) (a b : U i) . a <: b -> option a <: option b


### Operations

    bind : intersect (i : level) . forall (a b : U i) . option a -> (a -> option b) -> option b
         = fn a b l f . option_case l None (fn x . f x)
         (2 implicit arguments)

    bind _ b (None _) _ --> None b
    bind _ _ (Some _ x) f --> f x


    join : intersect (i : level) . forall (a : U i) . option (option a) -> option a
         = fn a l . bind l (fn x . x)
         (1 implicit argument)

    join a (None _) --> None a
    join _ (Some _ l) --> l


    map : intersect (i : level) . forall (a b : U i) . (a -> b) -> option a -> option b
         = fn a b f l . bind l (fn x . Some (f x))
         (2 implicit arguments)

    map _ b (None _) _ --> None b
    map _ b (Some _ x) f --> Some b (f x)


    valof : intersect (i : level) . forall (a : U i) . option a -> a -> a
         = fn a l x . option_case l x (fn y . y)
         (1 implicit argument)

    valof _ (None _) x --> x
    valof _ (Some _ x) --> x
