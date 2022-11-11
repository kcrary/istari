open:Acc
# `Acc` (accessibility)

Accessibility is used for expressing strong induction.  A relation is
*well-founded* if every element of the underlying type is accessible
using that relation.

The `Acc` predicate is primitive, but aliased in the `Acc` module:

    Acc : type:Acc

So if `A` is a type, and `R` is a relation on `A`, then `Acc A R x`
means that properties of `x` can be proven by induction.  (Ignoring
constructive niceties, it means that there are no infinite chains
descending from `x`.)

For example, well-foundedness of `<` on natural numbers is expressed
by the lemma:

    Nat.lt_well_founded : type:Nat.lt_well_founded

The main use of accessibility is to invoke induction on an
accessibility hypothesis, often obtained from a well-foundness lemma.
It can also be used directly:

    Acc_intro : type:Acc_intro

    Acc_elim : type:Acc_elim

