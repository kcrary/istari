# `Kindlike`

Although Istari primitively supports impredicative quantification only
over kinds, this library shows that, using a certain construction, we
can extend the ability to quantify impredicatively to a variety of
other types.  We call such types *kindlike*.

    kindlike : forall (i : level) . U (1 + i) -> U (2 + i)
             = fn i A .
                  exists (B : U i) (C : Kind i) (P : B -> C -> U i) .
                    Function.subpollent A { x : B & C | P (x #1) (x #2) }

Kindlikeness is a predicate over types in universe `1 + i`, which is
the same level of types that belong to `Kind i`.  We say that a type
`A` is kindlike if it is subpollent to 
`{ x : B & C | P (x #1) (x #2) }`, where `B` is an ordinary type in 
`U i`, `C` is a kind, and `P` is a predicate on `B` and `C`.  We say
that `A` is subpollent to `D` if there exists a function `A -> D` that
possesses a left inverse (in other words, if there exists a split
injection from `A` into `D`).

Note that it is not necessary to remember this definition to use the
library.

The first two lemmas establish that kindlike types enjoy impredicative
universal and existential quantifiers.  Their impredicative
quantifiers are equivalent to intersect/union, but unlike those, they
reside at universe `i`, not `1 + i`.

    forall_kindlike : forall (i : level) (A : U (1 + i)) .
                         kindlike i A
                         -> exists (Q : (A -> U i) -> U i) .
                              forall (B : A -> U i) . Q B <:> (intersect (x : A) . B x)

    exists_kindlike : forall (i : level) (A : U (1 + i)) .
                         kindlike i A
                         -> exists (Q : (A -> U i) -> U i) .
                              forall (B : A -> U i) . Q B <:> (union (x : A) . B x)

The remaining lemmas provide tools for establishing kindlikeness:

    kindlike_subpollent : forall (i : level) (A B : U (1 + i)) .
                             Function.subpollent A B -> kindlike i B -> kindlike i A

Level `i` kinds (which belong to `U (1 + i)`) are kindlike at level `i`:

    kindlike_kind : forall (i : level) (K : Kind i) . kindlike i K

    kindlike_univ : forall (i : level) . kindlike i (U i)

Ordinary types (at level `i`) are kindlike at level i:

    kindlike_degenerate : forall (i : level) (A : U i) . kindlike i A

    kindlike_arrow_right : forall (i : level) (A : U i) (B : U (1 + i)) .
                              kindlike i B -> kindlike i (A -> B)

    kindlike_arrow_left : forall (i : level) (A : U (1 + i)) (B : Kind i) .
                             kindlike i A -> guardable i B -> kindlike i (A -> B)

(The guardability condition used here is discussed below.)

    kindlike_prod : forall (i : level) (A B : U (1 + i)) .
                       kindlike i A -> kindlike i B -> kindlike i (A & B)

    kindlike_sum : forall (i : level) (A B : U (1 + i)) .
                      A -> B -> kindlike i A -> kindlike i B -> kindlike i (A % B)

    kindlike_future : forall (i : level) (A : U (1 + i)) .
                         future (kindlike i A) -> kindlike i (future A)

A more general version of kindlikeness for `future` is occasionally
useful:

    kindlike_future_gen : forall (i : level) (A : future (U (1 + i))) .
                             future (kindlike i (A #prev)) -> kindlike i (future (A #prev))

    kindlike_set : forall (i : level) (A : U (1 + i)) (P : A -> U i) .
                      kindlike i A -> kindlike i { x : A | P x }

    kindlike_iset : forall (i : level) (A : U (1 + i)) (P : A -> U i) .
                       kindlike i A -> kindlike i (iset (x : A) . P x)

    kindlike_rec : forall (i : level) (F : future (U (1 + i)) -> U (1 + i)) .
                      (forall (X : future (U (1 + i))) .
                         let next X' = X in future (kindlike i X') -> kindlike i (F X))
                      -> kindlike i (rec X . F (next X))



#### Guardability

Guardability is a technical condition that arises in
`kindlike_arrow_left`.  It generalizes the guard operator on types to
higher types.

The primitive [guard operator](../type-theory.html#guarded-types)
`P -g> A` creates a type such that `M : P -g> A` if `M : A` assuming
`P`.  Thus, if `M` is well-formed only when `P` holds, `M` can belong
to `P -g> A`.  When `P` holds, `P -g> A` is the same type as `A`.
Because of this guard operator on types, we say that universes
(*i.e.,* `U i`) are *guardable*.  We say that other types are
guardable if they support an analogous construction.

Specifically, `T` is guardable if there exists some guarding function
`f` that (for any `P`) embeds `P -g> T` within `T` in such a way that
`f` does nothing if `P` turns out to be true.

Guardability can be used to hide conditions on a function's argument
within its codomain.  So if we have a function `h` that almost has
type `A -> B` but it only works on arguments `x` satisfying `P`, we
can observe that `h x : P x -g> B` and therefore (if `B` is guardable)
`f P (h x) : B`.  Consequently, `fn x . f P (h x) : A -> B`.  In the
event that `P x` is true, `f P (h x) = h x`.

As with kindlikeness, it is not necessary to remember this definition
to use the library.  More kinds are guardable, but apparently not
`future`.

    guardable : forall (i : level) . U (1 + i) -> U (1 + i)
              = fn i A .
                   exists (f : forall (P : U i) . (P -g> A) -> A) .
                     forall (P : U i) . P -> forall (x : A) . f P x = x : A

    guardable_univ : forall (i : level) . guardable i (U i)

    guardable_unit : forall (i : level) . guardable i unit

    guardable_arrow : forall (i : level) (A B : U (1 + i)) . guardable i B -> guardable i (A -> B)

    guardable_karrow : forall (i : level) (K1 K2 : Kind i) .
                          guardable i K2 -> guardable i (K1 -k> K2)

    guardable_tarrow : forall (i : level) (A : U i) (K : Kind i) .
                          guardable i K -> guardable i (A -t> K)

    guardable_prod : forall (i : level) (A B : U (1 + i)) .
                        guardable i A -> guardable i B -> guardable i (A & B)

    guardable_rec : forall (i : level) (F : future (U (1 + i)) -> U (1 + i)) .
                       (forall (X : future (U (1 + i))) . guardable i (F X))
                       -> guardable i (rec X . F (next X))

For `future` to be guardable apparently would require the guard to
hold immediately in a situation in which it it only gets the guard in
the future.

The `guardable_rec` lemma could be strengthened by giving its
antecedent the assumption that `X` is guardable in the future, but
since `future` itself is not guardable, there doesn't appear to be
anything useful to do with such an assumption.
