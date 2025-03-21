# `Quotient`

The relation used in a quotient type must be symmetric and transitive,
also known as a partial equivalence relation:

    PER : intersect (i : level) . forall (A : U i) . (A -> A -> U i) -> U i
        = fn A R .
             (forall (x y : A) . R x y -> R y x) & (forall (x y z : A) . R x y -> R y z -> R x z)

    quotient_formation : forall (i : level) (A : U i) (R : A -> A -> U i) .
                            PER A R -> (quotient (x y : A) . R x y) : U i

Suppose `x` belongs to a quotient. When `x` is destructed to obtain
`x'`, `x'` has a different type (*i.e.,* the underlying type) than
`x`, which complicates typechecking.  By replacing `x` with 
`qintro _ _ _ x' h`, instead of merely `x'`, typechecking becomes
easier, even though the former unfolds to the latter.

    qintro : intersect (i : level) .
                forall (A : U i) (R : A -> A -> U i) .
                  PER A R -> forall (x : A) . R x x -> quotient (x1 y : A) . R x1 y
           = fn A R Hper x Hx . x

The squash below is necessary because the quotient's representative
(`y`) is not available for computation.  We use intensional squash so
that the result can be destructed without generative typing
obligations.

    quotient_representative : forall
                                 (i : level)
                                 (A : U i)
                                 (R : A -> A -> U i)
                                 (Hper : PER A R)
                                 (x : quotient (x y : A) . R x y) .
                                 isquash
                                   (exists (y : A) (Hy : R y y) .
                                      x = qintro A R Hper y Hy : (quotient (x1 y1 : A) . R x1 y1))

The squash below is necessary because when the quotient arguments (`x`
and `y`) are destructed, we must show the the result type does not
depend on the representatives that are chosen.  Although they are
logically equivalent, `R x y` and `R x' y'` are distinct types.
However, `{ R x y }` and `{ R x' y' }` are equal.

    quotient_equality : forall (i : level) (A : U i) (R : A -> A -> U i) .
                           PER A R
                           -> forall (x y : quotient (x1 y : A) . R x1 y) .
                                { R x y } -> x = y : (quotient (x1 y1 : A) . R x1 y1)

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

    qintro2 : intersect (i : level) .
                 forall (A : U i) (Q : A -> U i) (R : A -> A -> U i) .
                   PER2 A Q R -> forall (x : A) . Q x -> quotient (x1 y : A) . Q x1 & Q y & R x1 y
            = fn A Q R Hper x Hx . x

    quotient2_representative : forall
                                  (i : level)
                                  (A : U i)
                                  (Q : A -> U i)
                                  (R : A -> A -> U i)
                                  (Hper : PER2 A Q R)
                                  (x : quotient (x y : A) . Q x & Q y & R x y) .
                                  isquash
                                    (exists (y : A) (Hy : Q y) .
                                       x
                                         = qintro2 A Q R Hper y Hy
                                         : (quotient (x1 y1 : A) . Q x1 & Q y1 & R x1 y1))

    quotient2_equality : forall (i : level) (A : U i) (Q : A -> U i) (R : A -> A -> U i) .
                            PER2 A Q R
                            -> forall (x y : quotient (x1 y : A) . Q x1 & Q y & R x1 y) .
                                 { Q x -> Q y -> R x y }
                                 -> x = y : (quotient (x1 y1 : A) . Q x1 & Q y1 & R x1 y1)
