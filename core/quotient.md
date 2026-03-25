open:Quotient
# `Quotient`

The relation used in a quotient type must be at least symmetric and
transitive, also known as a partial equivalence relation:

    PER : type:PER
        = def:PER

    ER : type:ER
       = def:ER

    per_impl_er : type:per_impl_er

    per_refl_left : type:per_refl_left

    per_refl_right : type:per_refl_right

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
the same type.  Here, `x'` belongs to the underlying type, and `hx` is
a proof that `x'` is related to itself.

Nevertheless, `quotient (x y : A) . R x y` is interchangeable with
`quotient1 A R Hper`, and `x` is interchangeable with 
`qintro1 A R Hper x hx`, simply by using fold and unfold.

Destruction can match against a `quotient1` using `[p1 p2]` or
`[p1 p2 p3]`.

A common variant is when the relation is also reflexive (and hence is
an equivalence relation).  In that case, there is no need for a proof
that `x'` is related to itself, so destructing `x` creates 
`qintro1r A R Her x'`.

    quotient1r : type:quotient1r
               = def:quotient1r

    qintro1r : type:qintro1r
             = def:qintro1r

Destruction can match against a `quotient1r` using `[p1]` or 
`[p1 p2 p3]`.

Another common pattern for quotient types is to use a constraining
predicate (`Q` below), as well as a relation between representatives.
We recapitulate the tools for this common pattern.

    PER2 : type:PER2
         = def:PER2

    quotient2_formation : type:quotient2_formation

    quotient2 : type:quotient2
              = def:quotient2

    qintro2 : type:qintro2
            = def:qintro2

Destruction can match against a `quotient2` using `[p1 p2]` or 
`[p1 p2 p3 p4 p5]`.

The following lemmas accomplish largely the same thing as the
`destruct` tactic, and are sometimes convenient:

    quotient1_representative : type:quotient1_representative

    quotient1r_representative : type:quotient1r_representative

    quotient2_representative : type:quotient2_representative

(The squash in the type is necessary.  In a proof, destructing `x`
under appropriate circumstances provides an element of the underlying
type, but it produces a hidden variable, so that element is not
available computationally.  Regular squash (`{ ... }`) would work too,
but it is convenient to use
[`isquash`](../type-theory.html#subset-types) so that the proceeds of
the lemma can be destructed with fewer typechecking goals.

The following lemmas accomplish largely the same thing as the
`extensionality` tactic [1], and are sometimes convenient:

    quotient1_equality : type:quotient1_equality

    quotient1r_equality : type:quotient1r_equality

    quotient2_equality : type:quotient2_equality

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
