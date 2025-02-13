open:Weaksum
# `Weaksum`: an alternative interface for union types

Weak sums provide an alternative interface for union types, mostly
using introduction and elimination forms rather than retyping rules
(*i.e.,* rules that give a single term multiple types).

    weaksum : type:weaksum
            = def:weaksum

The introduction form for the weak sum is pack.  We provide two
versions, one in which the witness term (*i.e.* the inhabitant of `a`)
is available (`pack`) and one in which it is not (`packinv`):

    packinv : type:packinv
            = def:packinv
    
    pack : type:pack
         = def:pack

The elimination form is `unpack`.  Note that the body does not have
access to the witness term:

    unpack : type:unpack
           = def:unpack

    `unpack _ _ _ (`pack _ _ x y) f --> f y
    `unpack _ _ _ (`packinv _ _ y) f --> f y

The syntactic sugar `unpack x = u in m` is accepted for 
`unpack u (fn x . m)`.

Since the body of the `unpack` does not have access to the witness
term, it is unsuitable for composing predicates that talk about the
a weak sum's witness term.  For that, we can define `unpackt`:

    unpackt : type:unpackt
            = def:unpackt
    
The syntactic sugar `unpackt (x, y) = u in c` is accepted for
`unpackt _ _ (fn x y . c) u`.

The introduction forms for `unpackt` inhabits it when the weak sum
being unpacked is a known package.  Again, there are two versions, for
when the witness term is available and not:

    unpackt_intro_inv : type:unpackt_intro_inv
                      = def:unpackt_intro_inv

    unpackt_intro : type:unpackt_intro
                  = def:unpackt_intro

The elimination form allows one to move from an `unpackt` to some
other predicate about the weak sum in question.  Naturally, the
implication (the final argument) does not have access to the witness
term.

    unpackt_elim : type:unpackt_elim
                 = def:unpackt_elim

    `unpackt_elim _ _ _ _ _ (`unpackt_intro_inv _ _ _ y z) f --> f y z
    `unpackt_elim _ _ _ _ _ (`unpackt_intro _ _ _ x y z) f --> f y z

Finally, there are lemmas for converting union-like quantifiers to and
from weak sums:

    iexists_weaksum : type:iexists_weaksum

    weaksum_kindlike : type:weaksum_kindlike

For the latter, compare to [`Kindlike.exists_kindlike`](kindlike.html).
