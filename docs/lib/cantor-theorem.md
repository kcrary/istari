# `CantorTheorem`

Can be loaded using `File.import "cantor-theorem-load.iml";`

---

Cantor's classic proof that the real numbers are not enumerable.
Alas, the diagonal construction is sensitive to the representations of
the input numbers, which means that the construction must be done
using prereals, rather than actual reals (which are a quotient of the
prereals).  This doesn't change anything fundamentally, but it makes
the result messier.

The statement and proof is based on the development in Bishop and
Bridges [1].

    cantors_theorem : forall (x y : prereal) (f : nat -> prereal) .
                         realintro x <r realintro y
                         -> exists (z : prereal) .
                              realintro x <r= realintro z
                              & realintro z <r= realintro y
                              & (forall (i : nat) . realintro z != realintro (f i) : real)

---

[1] Errett Bishop and Douglas Bridges.  *Constructive Analysis.*
Springer, 1985.
