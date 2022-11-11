# `Acc` (accessibility)

Accessibility is used for expressing strong induction.  A relation is
*well-founded* if every element of the underlying type is accessible
using that relation.

The `Acc` predicate is primitive, but aliased in the `Acc` module:

    Acc : intersect (i : level) .
             forall (A : U i) (R : A -> A -> U i) . A -> U i

So if `A` is a type, and `R` is a relation on `A`, then `Acc A R x`
means that properties of `x` can be proven by induction.  (Ignoring
constructive niceties, it means that there are no infinite chains
descending from `x`.)

For example, well-foundedness of `<` on natural numbers is expressed
by the lemma:

    Nat.lt_well_founded : forall (n : nat) . Acc nat Nat.lt n

The main use of accessibility is to invoke induction on an
accessibility hypothesis, often obtained from a well-foundness lemma.
It can also be used directly:

    Acc_intro : forall (i : level) (A : U i) (R : A -> A -> U i) (x : A) .
                   (forall (y : A) . R y x -> Acc A R y) -> Acc A R x

    Acc_elim : forall
                  (i : level)
                  (A : U i)
                  (R : A -> A -> U i)
                  (x : A)
                  (y : A) .
                  Acc A R x -> R y x -> Acc A R y

