open:Acc
# `Acc` (accessibility)

Accessibility is used for expressing strong induction.  A relation is
*well-founded* if every element of the underlying type is accessible
using that relation.

    Acc : type:Acc

So if `A` is a type, and `R` is a relation on `A`, then `Acc A R x`
means that properties of `x` can be proven by induction.  (Ignoring
constructive niceties, it means that there are no infinite chains
descending from `x`.)  The definition is complicated, and is given at
the bottom of the page.

For example, well-foundedness of `<` on natural numbers is expressed
by the lemma:

    Nat.lt_well_founded : type:Nat.lt_well_founded

The main use of accessibility is to invoke
[induction](../tactics.html#induction) on an accessibility hypothesis,
often obtained from a [well-foundness
lemma](../definitions.html#strong-induction).

Accessibility can also be used directly.  The definition is
complicated (given below); it is easier to think about in terms of its
intro and elim operations:

    Acc_intro : type:Acc_intro

    Acc_elim : type:Acc_elim

---

    Acc = def:Acc
