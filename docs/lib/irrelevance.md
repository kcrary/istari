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
         = fn a . isquash a

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

All proofs are equal at a proof irrelevant type:

    pirr_ext : forall (i : level) (a : U i) (m m' : pirr a) . m = m' : pirr a

Implication induces subtyping on `pirr`:

    pirr_subtype : forall (i : level) (a b : U i) . (a -> b) -> pirr a <: pirr b

    pirr_eeqtp : forall (i : level) (a b : U i) . a <-> b -> pirr a <:> pirr b

However, care must be taken when using these.  If a proof `x` is
extracted from `pirr A`, and `A` is changed to `B`, any uses of `x`
must be adjusted (*e.g.,* using the `convertIrr` rewrite) to account
for the fact that `x` now proves `B` instead of `A`.  For this reason,
`pirr_subtype` and `pirr_eeqtp` are not employed automatically.

Proof irrelevance commutes with the future modality:

    pirr_from_future : intersect (i : level) .
                          forallfut (a : U i) . future (pirr a) -> pirr (future a)
                     = fn a m . ()

    future_from_pirr : intersect (i : level) .
                          forallfut (a : U i) . pirr (future a) -> future (pirr a)
                     = fn a m . next ()

    pirr_from_future_inv : forall (i : level) .
                              forallfut (a : U i) .
                                forall (m : future (pirr a)) .
                                  future_from_pirr (pirr_from_future m) = m : future (pirr a)

    future_from_pirr_inv : forall (i : level) .
                              forallfut (a : U i) .
                                forall (m : pirr (future a)) .
                                  pirr_from_future (future_from_pirr m) = m : pirr (future a)

(The latter direction is actually an instance of `pirr_ext`.)  The
untyped reductions eliminate the commutations, but they leave eta
redices:

    pirr_from_future _ (future_from_pirr _ x) --> let inpi y = x in inpi y

    future_from_pirr _ (pirr_from_future _ x) --> let next y = x in let inpi z = y in next (inpi z)


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
