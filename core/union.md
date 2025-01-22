open:Union
# `Union`: elimination forms for `union` and `iexists`

To assist in typechecking code that operates on a union, we have
`unpack` and its dependently typed analogue `unpack_dep`:

    unpack     : type:unpack
               = def:unpack

    unpack_dep : type:unpack_dep
               = def:unpack_dep

The syntactic sugar `unpack x = u in m` is accepted for
`` `unpack u (fn x . m)``.

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

    unpackt : type:unpackt
            = def:unpackt

The syntactic sugar `unpackt (x , y) = u in b` is accepted for
`` `unpackt _ _ (fn x y . b) u``.

The `unpackt` type has an introduction and elimination form:

    unpackt_intro : type:unpackt_intro
                  = def:unpackt_intro

    unpackt_elim  : type:unpackt_elim
                  = def:unpackt_elim

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

    iunpack     : type:iunpack
                = def:iunpack

    iunpack_dep : type:iunpack_dep
                = def:iunpack_dep

The syntactic sugar `iunpack x = u in m` is accepted for
`` `iunpack u (fn x . m)``.

    iunpackt : type:iunpackt
             = def:iunpackt

The syntactic sugar `iunpackt (x , y) = u in b` is accepted for
`` `iunpackt _ _ _ (fn x y . b) u``.

    iunpackt_intro : type:iunpackt_intro
                   = def:iunpackt_intro

    iunpackt_elim  : type:iunpackt_elim
                   = def:iunpackt_elim

    iunpackt_elim (iunpackt_intro y z) f --> f y z
