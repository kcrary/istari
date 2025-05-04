open:Weaksum
# `Weaksum`: an improved interface for union types

Weak sums provide an alternative interface for union types, using
introduction and elimination forms rather than retyping rules (*i.e.,*
rules that give a single term multiple types).

    weaksum : type:weaksum
            = def:weaksum

The introduction form for the weak sum is `pack`:
    
    pack : type:pack
         = def:pack
         imp:pack

The elimination form is `unpack`.  Note that the body has only
parametric access to the witness term:

    unpack : type:unpack
           = def:unpack
           imp:unpack

    `unpack _ _ _ (`pack _ _ x y) f --> f Ap x y

The syntactic sugar `unpack (x, y) = u in m` is accepted for 
`unpack u (fn x y . m)`.

Weaksum is covariant and preserves extensional equality:

    weaksum_subtype : type:weaksum_subtype

    weaksum_eeqtp : type:weaksum_eeqtp

Since the body of the `unpack` has only parametric access to the
witness term, it is unsuitable for composing predicates that talk
about a weak sum's witness term.  For that, we can define
`unpackt`:

    unpackt : type:unpackt
            = def:unpackt
            imp:unpackt
    
The syntactic sugar `unpackt (x, y) = u in c` is accepted for
`unpackt u (fn x y . c)`.

The introduction form for `unpackt` inhabits it when the weak sum
being unpacked is a known package:

    unpackt_intro : type:unpackt_intro
                  = def:unpackt_intro
                  imp:unpackt_intro

The elimination form allows one to move from an `unpackt` to some
other predicate about the weak sum in question.  Naturally, the
implication (the final argument) has only parametric access to the
witness term.

    unpackt_elim : type:unpackt_elim
                 = def:unpackt_elim
                 imp:unpackt_elim

    `unpackt_elim _ _ _ _ _ (`unpackt_intro _ _ _ x y z) f --> f Ap x y z

Some lemmas for manipulating `unpackt`:

    unpackt_simple : type:unpackt_simple

    unpackt_map : type:unpackt_map

    unpackt_assoc : type:unpackt_assoc

    unpackt_commute : type:unpackt_commute

    unpackt_commute_iff : type:unpackt_commute_iff

    bindbart_unpack_assoc : type:bindbart_unpack_assoc

Impredicative existentials are isomorphic (indeed, extensionally
equivalent) to weak sums:

    iexists_weaksum : type:iexists_weaksum

We may quantify impredicatively using weaksums:

    weaksum_kindlike : type:weaksum_kindlike
