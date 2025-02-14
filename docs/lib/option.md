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

    option_iter a P n s (None) --> n
    option_iter a P n s (Some x) --> s x

A simpler case-analysis operation:

    option_case : intersect (i : level) (a b : U i) . option a -> b -> (a -> b) -> b

    option_case (None) n s --> n
    option_case (Some x) n s --> s x


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

    map_identity : forall (i : level) (a : U i) (l : option a) . map (fn x . x) l = l : option a

    map_compose : forall (i : level) (a b c : U i) (f : b -> c) (g : a -> b) (l : option a) .
                     map f (map g l) = map (fn x . f (g x)) l : option c

    valof : intersect (i : level) . forall (a : U i) . option a -> a -> a
         = fn a l x . option_case l x (fn y . y)
         (1 implicit argument)

    valof _ (None _) x --> x
    valof _ (Some _ x) --> x



### Miscellaneous

    option_subtype : intersect (i : level) (a b : U i) . a <: b -> option a <: option b

Note that the subtyping principle relies on `None` and `Some`'s type
argument being invisible (*i.e.,* taken using `intersect`).

    option_eeqtp : forall (i : level) (a b : U i) . a <:> b -> option a <:> option b

    kindlike_option : forall (i : level) (a : U (1 + i)) .
                         a -> Kindlike.kindlike i a -> Kindlike.kindlike i (option a)
