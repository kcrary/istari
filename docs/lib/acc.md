# `Acc` (accessibility)

Accessibility is used for expressing strong induction.  A relation is
*well-founded* if every element of the underlying type is accessible
using that relation.

    Acc : intersect (i : level) . forall (A : U i) (R : A -> A -> U i) . A -> U i

So if `A` is a type, and `R` is a relation on `A`, then `Acc A R x`
means that properties of `x` can be proven by induction.  (Ignoring
constructive niceties, it means that there are no infinite chains
descending from `x`.)  The definition is complicated, and is given at
the bottom of the page.

For example, well-foundedness of `<` on natural numbers is expressed
by the lemma:

    Nat.lt_well_founded : forall (n : nat) . Acc nat Nat.lt n

The main use of accessibility is to invoke
[induction](../tactics.html#induction) on an accessibility hypothesis,
often obtained from a [well-foundness
lemma](../definitions.html#strong-induction).

Accessibility can also be used directly.  Since the definition is
complicated, it is easier to think about in terms of its intro and
elim operations:

    Acc_intro : forall (i : level) (A : U i) (R : A -> A -> U i) (x : A) .
                   (forall (y : A) . R y x -> Acc A R y) -> Acc A R x

    Acc_elim : forall (i : level) (A : U i) (R : A -> A -> U i) (x y : A) .
                  Acc A R x -> R y x -> Acc A R y

---

    Acc = fn A R x .
             exists (a : mu t . (exists (y : A) . forall (z : A) . R z y -> t)) .
               fix
                 (fn W b y .
                   exists (v : y = b #1 : A) . forall (z : A) (r : R z y) . W (b #2 z r) z)
                 a
                 x
