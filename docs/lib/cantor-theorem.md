# `CantorTheorem`

Can be loaded using `File.import "cantor-theorem-load.iml";`

---

Expressions in this file are rendered using the `real`
[overloading mode](../overloading.html).

Cantor's classic proof that the real numbers are not enumerable.
The statement and proof are based on the development in Bishop and
Bridges [1].

    cantors_theorem : forall (x y : real) (f : nat -> real) .
                         x < y
                         -> Squish.squish
                              (exists (z : real) .
                                 x <= z & z <= y & (forall (i : nat) . z != f i : real))

---

[1] Errett Bishop and Douglas Bridges.  *Constructive Analysis.*
Springer, 1985.
