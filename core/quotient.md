open:Quotient
# `Quotient`

The relation used in a quotient type must be symmetric and transitive,
also known as a partial equivalence relation:

    PER : type:PER
        = def:PER

    quotient_formation : type:quotient_formation

Suppose `x` belongs to a quotient. When `x` is destructed to obtain
`x'`, `x'` has a different type (*i.e.,* the underlying type) than
`x`, which complicates typechecking.  By replacing `x` with 
`qintro _ _ _ x' h`, instead of merely `x'`, typechecking becomes
easier, even though the former unfolds to the latter.

    qintro : type:qintro
           = def:qintro

The squash below is necessary because the quotient's representative
(`y`) is not available for computation.  We use intensional squash so
that the result can be destructed without generative typing
obligations.

    quotient_representative : type:quotient_representative

The squash below is necessary because when the quotient arguments (`x`
and `y`) are destructed, we must show the the result type does not
depend on the representatives that are chosen.  Although they are
logically equivalent, `R x y` and `R x' y'` are distinct types.
However, `{ R x y }` and `{ R x' y' }` are equal.

    quotient_equality : type:quotient_equality

A common pattern for quotient types is to use a constraining predicate
(`Q` below), as well as a relation between representatives.  We
recapitulate the tools for this common pattern.

    PER2 : type:PER2
         = def:PER2

    quotient2_formation : type:quotient2_formation

    qintro2 : type:qintro2
            = def:qintro2

    quotient2_representative : type:quotient2_representative

    quotient2_equality : type:quotient2_equality
