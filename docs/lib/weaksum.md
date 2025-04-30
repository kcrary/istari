# `Weaksum`: an improved interface for union types

Weak sums provide an alternative interface for union types, using
introduction and elimination forms rather than retyping rules (*i.e.,*
rules that give a single term multiple types).

    weaksum : intersect (i : level) . forall (a : U i) . (a -> U i) -> U i
            = fn a b . union (x : a) . b x

The introduction form for the weak sum is `pack`:
    
    pack : intersect (i : level) .
              forall (a : U i) (b : a -> U i) (x : a) . b x -> weaksum (x1 : a) . b x1
         = fn a b x y . y
         (1 implicit argument)

The elimination form is `unpack`.  Note that the body has only
parametric access to the witness term:

    unpack : intersect (i : level) .
                forall (a : U i) (b : a -> U i) (c : U i) .
                  (weaksum (x : a) . b x) -> (parametric (x : a) . b x -> c) -> c
           = fn a b c y f . f Irrelevance.unavailable y
           (3 implicit arguments)

    `unpack _ _ _ (`pack _ _ x y) f --> f Ap x y

The syntactic sugar `unpack (x, y) = u in m` is accepted for 
`unpack u (fn x y . m)`.

Weaksum is covariant and preserves extensional equality:

    weaksum_subtype : forall (i : level) (a a' : U i) (b : a -> U i) (b' : a' -> U i) .
                         a <: a'
                         -> (forall (x : a) . b x <: b' x)
                         -> (weaksum (x : a) . b x) <: (weaksum (x : a') . b' x)

    weaksum_eeqtp : forall (i : level) (a a' : U i) (b : a -> U i) (b' : a' -> U i) .
                       a <:> a'
                       -> (forall (x : a) . b x <:> b' x)
                       -> (weaksum (x : a) . b x) <:> (weaksum (x : a') . b' x)

Since the body of the `unpack` has only parametric access to the
witness term, it is unsuitable for composing predicates that talk
about a weak sum's witness term.  For that, we can define
`unpackt`:

    unpackt : intersect (i : level) .
                 forall (a : U i) (b : a -> U i) .
                   (forall (x : a) . b x -> U i) -> (weaksum (x : a) . b x) -> U i
            = fn a b t u .
                 weaksum (x : a) .
                   exists (y : b x) . pack b x y = u : (weaksum (x1 : a) . b x1) & t x y
            (2 implicit arguments)
    
The syntactic sugar `unpackt (x, y) = u in c` is accepted for
`unpackt (fn x y . c) u`.

The introduction form for `unpackt` inhabits it when the weak sum
being unpacked is a known package:

    unpackt_intro : intersect (i : level) .
                       forall
                         (a : U i)
                         (b : a -> U i)
                         (c : forall (x : a) . b x -> U i)
                         (x : a)
                         (y : b x) .
                         c x y -> unpackt c (pack b x y)
                  = fn a b c x y z .
                       pack
                         (fn x' .
                           exists (y' : b x') .
                             pack b x' y' = pack b x y : (weaksum (x1 : a) . b x1) & c x' y')
                         x
                         (y, (), z)
                  (3 implicit arguments)

The elimination form allows one to move from an `unpackt` to some
other predicate about the weak sum in question.  Naturally, the
implication (the final argument) has only parametric access to the
witness term.

    unpackt_elim : intersect (i : level) .
                      forall
                        (a : U i)
                        (b : a -> U i)
                        (c : forall (x : a) . b x -> U i)
                        (d : (weaksum (x : a) . b x) -> U i)
                        (z : weaksum (x : a) . b x) .
                        unpackt c z
                        -> (parametric (x : a) . forall (y : b x) . c x y -> d (pack b x y))
                        -> d z
                 = fn a b c d z w f . unpack (x, w') = w in f Ap x (w' #1) (w' #2 #2)
                 (4 implicit arguments)

    `unpackt_elim _ _ _ _ _ (`unpackt_intro _ _ _ x y z) f --> f Ap x y z

Some lemmas for manipulating `unpackt`:

    unpackt_simple : parametric (i : level) (a : U i) (b : a -> U i) .
                        forall (e : weaksum (x : a) . b x) .
                          parametric (c : forall (x : a) . b x -> U i) .
                            (parametric (x : a) . forall (y : b x) . c x y) -> unpackt c e

    unpackt_map : forall
                     (i : level)
                     (a : U i)
                     (b : a -> U i)
                     (c d : forall (x : a) . b x -> U i)
                     (w : weaksum (x : a) . b x) .
                     (parametric (x : a) . forall (y : b x) . c x y -> d x y)
                     -> unpackt c w
                     -> unpackt d w

    unpackt_assoc : forall
                       (i : level)
                       (a : U i)
                       (b : a -> U i)
                       (c : U i)
                       (d : c -> U i)
                       (e : weaksum (x : a) . b x)
                       (f : parametric (x : a) . b x -> weaksum (x1 : c) . d x1)
                       (t : forall (x : c) . d x -> U i) .
                       unpackt t (unpack e f) <-> (unpackt (x, y) = e in unpackt t (f Ap x y))

    unpackt_commute : forall
                         (i : level)
                         (a : U i)
                         (b : a -> U i)
                         (c : U i)
                         (d : c -> U i)
                         (e : forall (x : a) . b x -> forall (u : c) . d u -> U i)
                         (s1 : weaksum (x : a) . b x)
                         (s2 : weaksum (u : c) . d u) .
                         (unpackt (x, y) = s1 in unpackt (u, v) = s2 in e x y u v)
                         -> unpackt (u, v) = s2 in unpackt (x, y) = s1 in e x y u v

    unpackt_commute_iff : forall
                             (i : level)
                             (a : U i)
                             (b : a -> U i)
                             (c : U i)
                             (d : c -> U i)
                             (e : forall (x : a) . b x -> forall (u : c) . d u -> U i)
                             (s1 : weaksum (x : a) . b x)
                             (s2 : weaksum (u : c) . d u) .
                             (unpackt (x, y) = s1 in unpackt (u, v) = s2 in e x y u v)
                               <-> (unpackt (u, v) = s2 in unpackt (x, y) = s1 in e x y u v)

    bindbart_unpack_assoc : forall
                               (i : level)
                               (a : U i)
                               (b : a -> U i)
                               (c : U i)
                               (w : weaksum (x : a) . b x)
                               (f : parametric (x : a) . b x -> Bar.bar c)
                               (P : c -> U i) .
                               (bindbart y = unpack w f in P y)
                                 <-> (unpackt (x, y) = w in bindbart z = f Ap x y in P z)

Impredicative existentials are isomorphic (indeed, extensionally
equivalent) to weak sums:

    iexists_weaksum : forall (i : level) (a : Kind i) (b : a -> U i) .
                         (iexists (x : a) . b x) <:> (weaksum (x : a) . b x)

We may quantify impredicatively using weaksums:

    weaksum_kindlike : forall (i : level) (A : U (1 + i)) .
                          Kindlike.kindlike i A
                          -> exists (Q : (A -> U i) -> U i) .
                               forall (B : A -> U i) . Q B <:> (weaksum (x : A) . B x)
