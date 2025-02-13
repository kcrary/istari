# `Union`: elimination forms for `union` and `iexists`

Can be loaded using `File.import "girard-paradox-load.iml";`  To
enable `Union`'s syntactic sugar:

    grammaroff Weaksum;
    grammaron Union;

This is necessary because `Union`'s syntactic sugar conflicts with
`Weaksum`'s.

---

To assist in typechecking code that operates on a union, we have
`unpack` and its dependently typed analogue `unpack_dep`:

    unpack     : intersect (i : level) (a : U i) (b : a -> U i) (c : U i) .
                    (union (x : a) . b x) -> (intersect (x : a) . b x -> c) -> c
               = fn u f . f u

    unpack_dep : intersect (i : level) (a : U i) (b : a -> U i) .
                    forall (c : intersect (x : a) . b x -> U i) (u : union (x : a) . b x) .
                      (intersect (x : a) . forall (y : b x) . c y) -> c u
               = fn c u f . f u

If enabled, the syntactic sugar `unpack x = u in m` is accepted for ``
`unpack u (fn x . m)``.

Since unions are, at least in part, for managing situations in which
some variables are hidden, everything in this module takes every
argument invisibly (*i.e.,* using a `intersect`) that can be taken
that way.

Beyond that, observe that in the body of `unpack` and `unpack_dep`,
the union's hidden witness (`x`) is bound using intersection, which
means that the body cannot use that variable.

This is essential, due to the nature of union types.  Nevertheless,
that limitation can be problematic when defining a type based on a
union, so we have a variation on `unpack` for defining types:

    unpackt : intersect (i : level) .
                 forall (a : U i) (b : a -> U i) .
                   (forall (x : a) . b x -> U i) -> (union (x : a) . b x) -> U i
            = fn a b c u .
                 union (x : a) . exists (y : b x) . y = u : (union (x1 : a) . b x1) & c x y

If enabled, the syntactic sugar `unpackt (x , y) = u in b` is accepted
for `` `unpackt _ _ (fn x y . b) u``.

The `unpackt` type has an introduction and elimination form:

    unpackt_intro : intersect
                       (i : level)
                       (a : U i)
                       (b : a -> U i)
                       (c : forall (x : a) . b x -> U i)
                       (x : a) .
                       forall (y : b x) . c x y -> unpackt a b c y
                  = fn y z . (y, (), z)

    unpackt_elim  : intersect
                       (i : level)
                       (a : U i)
                       (b : a -> U i)
                       (c : forall (x : a) . b x -> U i)
                       (d : (union (x : a) . b x) -> U i)
                       (u : union (x : a) . b x) .
                       unpackt a b c u
                       -> (intersect (x : a) . forall (y : b x) . c x y -> d y)
                       -> d u
                  = fn w f . f (w #1) (w #2 #2)

Again, observe that the continuation in `unpackt_elim` (*i.e.,* its
final argument) cannot refer to the union's hidden witness (`x`).

The intro and elim forms reduce in the expected manner:

    unpackt_elim (unpackt_intro y z) f --> f y z


To use an `unpackt`, it is generally just a matter of destructing it
and exploiting its equality.  Suppose:

    i : level
    a : U i
    b : a -> U i
    c : forall (x : a) . b x -> U i
    d : forall (x : a) . b x -> U i
    u : union (x : a) . b x
    H : unpackt (x , y) = u in c x y

Then `destruct /H/ /x y Heq Hy/ >> reduce /Hy/` produces:

    x (hidden) : a
    y : b x
    Heq : y = u : (union (x1 : a) . b x1)
    Hy : c x y

Now (assuming `u` is always used in a manner consistent with the type
`union (x : a) . b x`) you can use `subst /u/` to replace `u` with `y`
and proceed from there.

---

A similar set of definitions is available for `iexists`:

    iunpack     : intersect (i : level) (a : Kind i) (b : a -> U i) (c : U i) .
                     (iexists (x : a) . b x) -> (intersect (x : a) . b x -> c) -> c
                = fn u f . f u

    iunpack_dep : intersect (i : level) (a : Kind i) (b : a -> U i) .
                     forall (c : intersect (x : a) . b x -> U i) (u : iexists (x : a) . b x) .
                       (intersect (x : a) . forall (y : b x) . c y) -> c u
                = fn c u f . f u

If enabled, the syntactic sugar `iunpack x = u in m` is accepted for
`` `iunpack u (fn x . m)``.

    iunpackt : forall (i : level) (a : Kind i) (b : a -> U i) .
                  (forall (x : a) . b x -> U i) -> (iexists (x : a) . b x) -> U i
             = fn i a b c u .
                  iexists (x : a) . exists (y : b x) . y = u : (iexists (x1 : a) . b x1) & c x y

If enabled, the syntactic sugar `iunpackt (x , y) = u in b` is
accepted for `` `iunpackt _ _ _ (fn x y . b) u``.

    iunpackt_intro : intersect
                        (i : level)
                        (a : Kind i)
                        (b : a -> U i)
                        (c : forall (x : a) . b x -> U i)
                        (x : a) .
                        forall (y : b x) . c x y -> iunpackt a b c y
                   = fn y z . (y, (), z)

    iunpackt_elim  : intersect
                        (i : level)
                        (a : Kind i)
                        (b : a -> U i)
                        (c : forall (x : a) . b x -> U i)
                        (d : (iexists (x : a) . b x) -> U i)
                        (u : iexists (x : a) . b x) .
                        iunpackt a b c u
                        -> (intersect (x : a) . forall (y : b x) . c x y -> d y)
                        -> d u
                   = fn w f . f (w #1) (w #2 #2)

    iunpackt_elim (iunpackt_intro y z) f --> f y z
