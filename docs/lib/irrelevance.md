# `Irrelevance`

We say that `x` appears only in irrelevant positions within `M` (or,
more briefly, that `x` is irrelevant in `M`) if `x` does not
contribute to the computational or semantic meaning of `M`.
Intuitively, this the case when fully unfolding all the constants in
`M` and normalizing the result results in a normal form that does not
contain `x`.

To define irrelevance, we use the constant `unavailable` as a stand-in
for terms that are not available for relevant use.  Using it, we
define irrelevance by:

    irrelevant = fn f .
                    intersect (x : Misc.nonsense) . SyntacticEquality.sequal (f x) (f unavailable)

Some examples of irrelevant positions are `x` and `A` in `f ap x`, `f Ap x`,
`abort x`, `M :> A` and `fn (x : A) . M`.


#### Proof irrelevance modality

Irrelevance of `x` in `M` is a requirement for `fn x . M` to be a
parametric function.  [Parametric
functions](../type-theory.html#parametric-functions) provide one
important tool for proof irrelevance, and [weak sums](#weaksum.html)
provide another.  Still another is the proof irrelevance modality:

    pirr : intersect (i : level) . U i -> U i
         = fn a . { a }

The type `pirr A` expresses the fact that `A` is true but its
computational content is unavailable.  It is defined using the squash
type, but unlike squash it offers intro and elim forms.

    inpi : intersect (i : level) (a : U i) . a -> pirr a
         = fn m . ()

    outpi : intersect (i : level) (a b : U i) . pirr a -> (parametric (v0 : a) . b) -> b
          = fn m f . f unavailable

Importantly, `x` is irrelevant in `inpi x`, which means that hidden
variables can be used in that position.  Less importantly, `x` is
irrelevant in `outpi x f`.

Observe that `outpi M (fn x . N)` allows the unknown inhabitant of `A`
to be used in `N`, so long as `x` is irrelevant in `N`.  When that
inhabitant becomes known, we can reduce:

    outpi (inpi m) f --> f Ap m


#### Impredicative functions

Impredicative functions are isomorphic to parametric functions:

    iforall_to_parametric : intersect (i : level) (a : Kind i) (b : a -> U i) .
                               (iforall (x : a) . b x) -> parametric (x : a) . b x
                          = fn f x . f

    parametric_to_iforall : intersect (i : level) (a : Kind i) (b : a -> U i) .
                               (parametric (x : a) . b x) -> iforall (x : a) . b x
                          = fn f . f unavailable

    iforall_to_parametric_inverse : forall
                                       (i : level)
                                       (a : Kind i)
                                       (b : a -> U i)
                                       (f : iforall (x : a) . b x) .
                                       parametric_to_iforall (iforall_to_parametric f)
                                         = f
                                         : (iforall (x : a) . b x)

    parametric_to_iforall_inverse : forall
                                       (i : level)
                                       (a : Kind i)
                                       (b : a -> U i)
                                       (f : parametric (x : a) . b x) .
                                       iforall_to_parametric (parametric_to_iforall f)
                                         = f
                                         : (parametric (x : a) . b x)

As a corollary:

    iforall_parametric_equipollent : forall (i : level) (a : Kind i) (b : a -> U i) .
                                        Function.equipollent
                                          (iforall (x : a) . b x)
                                          (parametric (x : a) . b x)
