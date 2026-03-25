# `Quotient`

The relation used in a quotient type must be at least symmetric and
transitive, also known as a partial equivalence relation:

    PER : intersect (i : level) . forall (A : U i) . (A -> A -> U i) -> U i
        = fn A R .
             (forall (x y : A) . R x y -> R y x) & (forall (x y z : A) . R x y -> R y z -> R x z)

    ER : intersect (i : level) . forall (A : U i) . (A -> A -> U i) -> U i
       = fn A R .
            (forall (x : A) . R x x)
            & (forall (x y : A) . R x y -> R y x)
            & (forall (x y z : A) . R x y -> R y z -> R x z)

    per_impl_er : forall (i : level) (A : U i) (R : A -> A -> U i) . ER A R -> PER A R

    per_refl_left : intersect (i : level) .
                       forall (A : U i) (R : A -> A -> U i) .
                         PER A R -> forall (x y : A) . R x y -> R x x

    per_refl_right : intersect (i : level) .
                        forall (A : U i) (R : A -> A -> U i) .
                          PER A R -> forall (x y : A) . R x y -> R y y

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
the same type.  Here, `x'` belongs to the underlying type, and `hx` is
a proof that `x'` is related to itself.

Nevertheless, `quotient (x y : A) . R x y` is interchangeable with
`quotient1 A R Hper`, and `x` is interchangeable with 
`qintro1 A R Hper x hx`, simply by using fold and unfold.

A common variant is when the relation is also reflexive (and hence is
an equivalence relation).  In that case, there is no need for a proof
that `x'` is related to itself, so destructing `x` creates 
`qintro1r A R Her x'`.

    quotient1r : intersect (i : level) . forall (A : U i) (R : A -> A -> U i) . ER A R -> U i
               = fn A R Her . quotient (x y : A) . R x y

    qintro1r : intersect (i : level) .
                  forall (A : U i) (R : A -> A -> U i) (Hper : ER A R) (x : A) .
                    quotient1r A R Hper
             = fn A R Her x . x

Another common pattern for quotient types is to use a constraining
predicate (`Q` below), as well as a relation between representatives.
We recapitulate the tools for this common pattern.

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

The following lemmas accomplish largely the same thing as the
`destruct` tactic, and are sometimes convenient:

    quotient1_representative : forall
                                  (i : level)
                                  (A : U i)
                                  (R : A -> A -> U i)
                                  (Hper : PER A R)
                                  (x : quotient1 A R Hper) .
                                  isquash
                                    (exists (y : A) (h : R y y) .
                                       x = qintro1 A R Hper y h : quotient1 A R Hper)

    quotient1r_representative : forall
                                   (i : level)
                                   (A : U i)
                                   (R : A -> A -> U i)
                                   (Her : ER A R)
                                   (x : quotient1r A R Her) .
                                   isquash
                                     (exists (y : A) . x = qintro1r A R Her y : quotient1r A R Her)

    quotient2_representative : forall
                                  (i : level)
                                  (A : U i)
                                  (Q : A -> U i)
                                  (R : A -> A -> U i)
                                  (Hper : PER2 A Q R)
                                  (x : quotient2 A Q R Hper) .
                                  isquash
                                    (exists (y : A) (h : Q y) .
                                       x = qintro2 A Q R Hper y h : quotient2 A Q R Hper)

(The squash in the type is necessary.  In a proof, destructing `x`
under appropriate circumstances provides an element of the underlying
type, but it produces a hidden variable, so that element is not
available computationally.  Regular squash (`{ ... }`) would work too,
but it is convenient to use
[`isquash`](../type-theory.html#subset-types) so that the proceeds of
the lemma can be destructed with fewer typechecking goals.

The following lemmas accomplish largely the same thing as the
`extensionality` tactic [1], and are sometimes convenient:

    quotient1_equality : forall
                            (i : level)
                            (A : U i)
                            (R : A -> A -> U i)
                            (Hper : PER A R)
                            (x y : quotient1 A R Hper) .
                            { R x y } -> x = y : quotient1 A R Hper

    quotient1r_equality : forall
                             (i : level)
                             (A : U i)
                             (R : A -> A -> U i)
                             (Her : ER A R)
                             (x y : quotient1r A R Her) .
                             { R x y } -> x = y : quotient1r A R Her

    quotient2_equality : forall
                            (i : level)
                            (A : U i)
                            (Q : A -> U i)
                            (R : A -> A -> U i)
                            (Hper : PER2 A Q R)
                            (x y : quotient2 A Q R Hper) .
                            { R x y } -> x = y : quotient2 A Q R Hper

In these, note that the `x` and `y` in the `R x y` antecedent do not
obviously have the type that `R` is expecting.  This type is correct,
but it may surprise the typechecker.  However, if `x` and `y` already
have a form like `qintro1 ...` (*e.g.,* by using a "representative"
tactic), then the antecedent can be put in a more convenient form by
unfolding the `qintro1`.

(The squash in the type is necessary.  Since `R` works on the
underlying type, rather than on the quotient, it is necessary to draw
representatives from `x`'s and `y`'s equivalence classes.  This gives us
`R x y <-> R x' y'` but not (in general) `R x y = R x' y'` when `x`
and `x'` (and `y` and `y'`) are merely related.  However `{ R x y }`
and `{ R x' y' }` *are* equal types, since squash contracts logical
equivalence to type equality.)

---

[1] except that, in practice, the `quotient2_equality` lemma will
normally generate fewer subgoals than `extensionality`
