# `GirardParadox`

Can be loaded using `File.import "girard-paradox-load.iml";`

---

Girard's paradox [1] is a proof that *type* is not a type, an
adaptation of set theory's Burali-Forti paradox into type theory.

The proof works by observing that the collection of all well-founded
posets looks like a poset itself, using strict embedding as the order.
That poset of well-founded posets, let's call it **P**, would need to
reside one level higher in the universe hierarchy, but if the universe
hierarchy is collapsed, **P** is a poset at the same level.  Moreover,
(if the universe hierarchy is collapsed) we can show that **P** is
well-founded.  However, **P** embeds into itself, which is a
contradiction.

We express the proposition that *type* is a type in Istari by saying
that `U (1 + i) <: U i`, for some level `i`.  From that it would
follow that `U i : U i`.  However, unlike the direct statement, the
statement using subtyping is
[negatable](../type-theory.html#negatability).

    girard_paradox : forall (i : level) . not (U (1 + i) <: U i)

---

[1] Jean-Yves Girard.  *Une extension de l'interpr&eacute;tation de
G&ouml;del &agrave; l'analyse, et son application &agrave;
l'&eacute;limination de coupures dans l'analyse et la th&eacute;orie
des types*, 1972.

