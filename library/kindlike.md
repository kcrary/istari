open:Kindlike
# `Kindlike`

Although Istari primitively supports impredicative quantification only
over kinds, this library shows that, using a certain construction, we
can extend the ability to quantify impredicatively to a variety of
other types.  We call such types *kindlike*.

    kindlike : type:kindlike
             = def:kindlike

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

    forall_kindlike : type:forall_kindlike

    exists_kindlike : type:exists_kindlike

The remaining lemmas provide tools for establishing kindlikeness:

    kindlike_subpollent : type:kindlike_subpollent

Level `i` kinds (which belong to `U (1 + i)`) are kindlike at level `i`:

    kindlike_kind : type:kindlike_kind

    kindlike_univ : type:kindlike_univ

Ordinary types (at level `i`) are kindlike at level i:

    kindlike_degenerate : type:kindlike_degenerate

    kindlike_arrow_right : type:kindlike_arrow_right

    kindlike_arrow_left : type:kindlike_arrow_left

(The guardability condition used here is discussed below.)

    kindlike_prod : type:kindlike_prod

    kindlike_sum : type:kindlike_sum

    kindlike_future : type:kindlike_future

A more general version of kindlikeness for `future` is occasionally
useful:

    kindlike_future_gen : type:kindlike_future_gen

    kindlike_set : type:kindlike_set

    kindlike_iset : type:kindlike_iset

    kindlike_rec : type:kindlike_rec



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

    guardable : type:guardable
              = def:guardable

    guardable_univ : type:guardable_univ

    guardable_unit : type:guardable_unit

    guardable_arrow : type:guardable_arrow

    guardable_karrow : type:guardable_karrow

    guardable_tarrow : type:guardable_tarrow

    guardable_prod : type:guardable_prod

    guardable_rec : type:guardable_rec

For `future` to be guardable apparently would require the guard to
hold immediately in a situation in which it it only gets the guard in
the future.

The `guardable_rec` lemma could be strengthened by giving its
antecedent the assumption that `X` is guardable in the future, but
since `future` itself is not guardable, there doesn't appear to be
anything useful to do with such an assumption.
