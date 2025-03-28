open:Quotient
# `Quotient`

The relation used in a quotient type must be symmetric and transitive,
also known as a partial equivalence relation:

    PER : type:PER
        = def:PER

    quotient_formation : type:quotient_formation

The quotient type does not have an introduction form, which sometimes
causes difficulties for the type checker.  An alternative presentation
of quotient types, called `quotient1`, uses an introduction form:

    quotient1 : type:quotient1
              = def:quotient1

    qintro1 : type:qintro1
            = def:qintro1

Suppose `x` belongs to a quotient. When `x` is destructed to obtain
`x'`, `x'` has a different type than `x` (*i.e.,* the underlying
type).  This can complicate typechecking.  However, when `x` belongs
to `quotient1 A R Hper`, destructing `x` creates 
`qintro1 A R Hper x' hx` which can easily be determined still to have
the same type.

Nevertheless, `quotient (x y : A) . R x y` is interchangeable with
`quotient1 A R Hper`, and `x` is interchangeable with 
`qintro1 A R Hper x hx`, simply by using fold and unfold.

A common pattern for quotient types is to use a constraining predicate
(`Q` below), as well as a relation between representatives.  We
recapitulate the tools for this common pattern.

    PER2 : type:PER2
         = def:PER2

    quotient2_formation : type:quotient2_formation

    quotient2 : type:quotient2
              = def:quotient2

    qintro2 : type:qintro2
            = def:qintro2

When using the `extensionality` tactic to prove 
`M = N : quotient2 A Q R H`, it is necessary to prove `Q M` and 
`Q N`.  However, if we already know that `M` and `N` belong to 
`quotient2 A Q R H`, those obligations are redundant.  The
`quotient2_equality` lemma provides an easier way to prove equality in
such cases.

    quotient2_equality : type:quotient2_equality

(The squash in the type is necessary.  Since `R` works on the
underlying type, rather than on the quotient, it is necessary to draw
representatives from `x`'s and `y`'s equivalence classes.  But then we
have `R x y <-> R x' y'` but not (in general) `R x y = R x' y'` when
`x` and `x'` (and `y` and `y'`) are merely related.  However 
`{ R x y }` and `{ R x' y' }` *are* equal types, since squash contracts
logical equivalence to type equality.)
