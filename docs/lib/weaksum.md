# `Weaksum`: an alternative interface for union types

Weak sums provide an alternative interface for union types, mostly
using introduction and elimination forms rather than retyping rules
(*i.e.,* rules that give a single term multiple types).

    weaksum : intersect (i : level) . forall (a : U i) . (a -> U i) -> U i
            = fn a b . union (x : a) . b x

The introduction form for the weak sum is pack.  We provide two
versions, one in which the witness term (*i.e.* the inhabitant of `a`)
is available (`pack`) and one in which it is not (`packinv`):

    packinv : intersect (i : level) .
                 forall (a : U i) (b : a -> U i) .
                   intersect (x : a) . b x -> weaksum (x1 : a) . b x1
            = fn a b y . y
    
    pack : intersect (i : level) .
              forall (a : U i) (b : a -> U i) (x : a) . b x -> weaksum (x1 : a) . b x1
         = fn a b x y . packinv b y

The elimination form is `unpack`.  Note that the body does not have
access to the witness term:

    unpack : intersect (i : level) .
                forall (a : U i) (b : a -> U i) (c : U i) .
                  (weaksum (x : a) . b x) -> (intersect (x : a) . b x -> c) -> c
           = fn a b c y f . f y

    `unpack _ _ _ (`pack _ _ x y) f --> f y
    `unpack _ _ _ (`packinv _ _ y) f --> f y

The syntactic sugar `unpack x = u in m` is accepted for 
`unpack u (fn x . m)`.

Weaksum is covariant and preserves extensional equality:

    weaksum_subtype : forall (i : level) (a a' : U i) (b : a -> U i) (b' : a' -> U i) .
                         a <: a'
                         -> (forall (x : a) . b x <: b' x)
                         -> (weaksum (x : a) . b x) <: (weaksum (x : a') . b' x)

    weaksum_eeqtp : forall (i : level) (a a' : U i) (b : a -> U i) (b' : a' -> U i) .
                       a <:> a'
                       -> (forall (x : a) . b x <:> b' x)
                       -> (weaksum (x : a) . b x) <:> (weaksum (x : a') . b' x)

Since the body of the `unpack` does not have access to the witness
term, it is unsuitable for composing predicates that talk about the
a weak sum's witness term.  For that, we can define `unpackt`:

    unpackt : intersect (i : level) .
                 forall (a : U i) (b : a -> U i) .
                   (forall (x : a) . b x -> U i) -> (weaksum (x : a) . b x) -> U i
            = fn a b t u .
                 weaksum (x : a) .
                   exists (y : b x) . pack b x y = u : (weaksum (x1 : a) . b x1) & t x y
    
The syntactic sugar `unpackt (x, y) = u in c` is accepted for
`unpackt _ _ (fn x y . c) u`.

The introduction forms for `unpackt` inhabits it when the weak sum
being unpacked is a known package.  Again, there are two versions, for
when the witness term is available and not:

    unpackt_intro_inv : intersect (i : level) .
                           forall (a : U i) (b : a -> U i) (c : forall (x : a) . b x -> U i) .
                             intersect (x : a) .
                               forall (y : b x) . c x y -> unpackt c (packinv b y)
                      = fn a b c y z .
                           packinv
                             (fn x' .
                               exists (y' : b x') .
                                 pack b x' y' = packinv b y : (weaksum (x : a) . b x) & c x' y')
                             (y, (), z)

    unpackt_intro : intersect (i : level) .
                       forall
                         (a : U i)
                         (b : a -> U i)
                         (c : forall (x : a) . b x -> U i)
                         (x : a)
                         (y : b x) .
                         c x y -> unpackt c (pack b x y)
                  = fn a b c x y z . unpackt_intro_inv y z

The elimination form allows one to move from an `unpackt` to some
other predicate about the weak sum in question.  Naturally, the
implication (the final argument) does not have access to the witness
term.

    unpackt_elim : intersect (i : level) .
                      forall
                        (a : U i)
                        (b : a -> U i)
                        (c : forall (x : a) . b x -> U i)
                        (d : (weaksum (x : a) . b x) -> U i)
                        (z : weaksum (x : a) . b x) .
                        unpackt c z
                        -> (intersect (x : a) . forall (y : b x) . c x y -> d (pack b x y))
                        -> d z
                 = fn a b c d z w f . unpack w' = w in f (w' #1) (w' #2 #2)

    `unpackt_elim _ _ _ _ _ (`unpackt_intro_inv _ _ _ y z) f --> f y z
    `unpackt_elim _ _ _ _ _ (`unpackt_intro _ _ _ x y z) f --> f y z

Finally, there are lemmas for converting union-like quantifiers to and
from weak sums:

    iexists_weaksum : forall (i : level) (a : Kind i) (b : a -> U i) .
                         (iexists (x : a) . b x) <:> (weaksum (x : a) . b x)

    weaksum_kindlike : forall (i : level) (A : U (1 + i)) .
                          Kindlike.kindlike i A
                          -> exists (Q : (A -> U i) -> U i) .
                               forall (B : A -> U i) . Q B <:> (weaksum (x : A) . B x)

For the latter, compare to [`Kindlike.exists_kindlike`](kindlike.html).
