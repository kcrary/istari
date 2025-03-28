# `Quotient`

The relation used in a quotient type must be symmetric and transitive,
also known as a partial equivalence relation:

    PER : intersect (i : level) . forall (A : U i) . (A -> A -> U i) -> U i
        = fn A R .
             (forall (x y : A) . R x y -> R y x) & (forall (x y z : A) . R x y -> R y z -> R x z)

    quotient_formation : forall (i : level) (A : U i) (R : A -> A -> U i) .
                            PER A R -> (quotient (x y : A) . R x y) : U i

The quotient type does not have an introduction form, which sometimes
causes difficulties for the type checker.  An alternative presentation
of quotient types, called `quotient1`, uses an introduction form:

    quotient1 : intersect (i : level) . forall (A : U i) (R : A -> A -> U i) . PER A R -> U i
              = fn A R Hper . quotient (x y : A) . R x y

    qintro1 : intersect (i : level) .
                 forall (A : U i) (R : A -> A -> U i) (Hper : PER A R) (x : A) .
                   R x x -> quotient1 A R Hper
            = fn A R Hper x Hx . x

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

    PER2 : intersect (i : level) . forall (A : U i) . (A -> U i) -> (A -> A -> U i) -> U i
         = fn A Q R .
              (forall (x : A) . Q x -> R x x)
              & (forall (x y : A) . Q x -> Q y -> R x y -> R y x)
              & (forall (x y z : A) . Q x -> Q y -> Q z -> R x y -> R y z -> R x z)

    quotient2_formation : forall (i : level) (A : U i) (Q : A -> U i) (R : A -> A -> U i) .
                             PER2 A Q R -> (quotient (x y : A) . Q x & Q y & R x y) : U i

    quotient2 : intersect (i : level) .
                   forall (A : U i) (Q : A -> U i) (R : A -> A -> U i) . PER2 A Q R -> U i
              = fn A Q R Hper . quotient (x y : A) . Q x & Q y & R x y

    qintro2 : intersect (i : level) .
                 forall (A : U i) (Q : A -> U i) (R : A -> A -> U i) (Hper : PER2 A Q R) (x : A) .
                   Q x -> quotient2 A Q R Hper
            = fn A Q R Hper x Hx . x

When using the `extensionality` tactic to prove 
`M = N : quotient2 A Q R H`, it is necessary to prove `Q M` and 
`Q N`.  However, if we already know that `M` and `N` belong to 
`quotient2 A Q R H`, those obligations are redundant.  The
`quotient2_equality` lemma provides an easier way to prove equality in
such cases.

    quotient2_equality : forall
                            (i : level)
                            (A : U i)
                            (Q : A -> U i)
                            (R : A -> A -> U i)
                            (Hper : PER2 A Q R)
                            (x y : quotient2 A Q R Hper) .
                            { R x y } -> x = y : quotient2 A Q R Hper

(The squash in the type is necessary.  Since `R` works on the
underlying type, rather than on the quotient, it is necessary to draw
representatives from `x`'s and `y`'s equivalence classes.  But then we
have `R x y <-> R x' y'` but not (in general) `R x y = R x' y'` when
`x` and `x'` (and `y` and `y'`) are merely related.  However 
`{ R x y }` and `{ R x' y' }` *are* equal types, since squash contracts
logical equivalence to type equality.)
