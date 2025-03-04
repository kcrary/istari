open:Irrelevance
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

    irrelevant = def:irrelevant

Some examples of irrelevant positions are `x` and `A` in `f ap x`, `f Ap x`,
`abort x`, `M :> A` and `fn (x : A) . M`.


#### Proof irrelevance modality

Irrelevance of `x` in `M` is a requirement for `fn x . M` to be a
parametric function.  [Parametric
functions](../type-theory.html#parametric-functions) provide one
important tool for proof irrelevance, and [weak sums](#weaksum.html)
provide another.  Still another is the proof irrelevance modality:

    pirr : type:pirr
         = def:pirr

The type `pirr A` expresses the fact that `A` is true but its
computational content is unavailable.  It is defined using the squash
type, but unlike squash it offers intro and elim forms.

    inpi : type:inpi
         = def:inpi

    outpi : type:outpi
          = def:outpi

Importantly, `x` is irrelevant in `inpi x`, which means that hidden
variables can be used in that position.  Less importantly, `x` is
irrelevant in `outpi x f`.

Observe that `outpi M (fn x . N)` allows the unknown inhabitant of `A`
to be used in `N`, so long as `x` is irrelevant in `N`.  When that
inhabitant becomes known, we can reduce:

    outpi (inpi m) f --> f Ap m

All proofs are equal at a proof irrelevant type:

    pirr_ext : type:pirr_ext

Implication induces subtyping on `pirr`:

    pirr_subtype : type:pirr_subtype

    pirr_eeqtp : type:pirr_eeqtp

However, care must be taken when using these.  If a proof `x` is
extracted from `pirr A`, and `A` is changed to `B`, any uses of `x`
must be adjusted (*e.g.,* using the `convertIrr` rewrite) to account
for the fact that `x` now proves `B` instead of `A`.  For this reason,
`pirr_subtype` and `pirr_eeqtp` are not employed automatically.

Proof irrelevance commutes with the future modality:

    pirr_from_future : type:pirr_from_future
                     = def:pirr_from_future

    future_from_pirr : type:future_from_pirr
                     = def:future_from_pirr

    pirr_from_future_inv : type:pirr_from_future_inv

The other direction is an instance of `pirr_ext`.

The typechecker will generally not be able to guess the future type
argument `af`, so a visibilized application will typically be
necessary.  A simpler version is available when the type argument is
available in the present:

    pirr_from_future' : type:pirr_from_future'
                      = def:pirr_from_future'

    future_from_pirr' : type:future_from_pirr'
                      = def:future_from_pirr'

    pirr_from_future'_inv : type:pirr_from_future'_inv


#### Impredicative functions

Impredicative functions are isomorphic to parametric functions:

    iforall_to_parametric : type:iforall_to_parametric
                          = def:iforall_to_parametric

    parametric_to_iforall : type:parametric_to_iforall
                          = def:parametric_to_iforall

    iforall_to_parametric_inverse : type:iforall_to_parametric_inverse

    parametric_to_iforall_inverse : type:parametric_to_iforall_inverse

As a corollary:

    iforall_parametric_equipollent : type:iforall_parametric_equipollent
