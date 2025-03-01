# `Misc`

This module contains various constants that need to be primitive, but aren't used
widely enough to make them pervasive.

| Constant       | Usage                                                    |
| -------------- | -------------------------------------------------------- |
| `bogus`        | used for placeholder terms                               |
| `entailment`   | a pseudo-relation used in the rewriter                   |
| `magic`        | the extract for `trustme`                                |
| `orphan`       | substituted for variables going out of scope             |
| `positive`     | arises in determining whether `mu` types are well-formed |
| `negative`     | arises in determining whether `mu` types are well-formed |


It also contains other material that defies categorization:

    nonsense : U 0
             = void -g> void

The important property of `nonsense` is *everything* belongs to
nonsense, even terms that would normally be ill-formed.  As a
corollary, every type is a subtype of nonsense:

    nonsense_subtype : forall (i : level) (a : U i) . a <: nonsense

Extensional type equivalence can be mapped through any covariant or
contravariant type operator:

    eeqtp_compat_covariant : forall (i : level) (t : U i -> U i) .
                                (forall (a a' : U i) . a <: a' -> t a <: t a')
                                -> forall (a a' : U i) . a <:> a' -> t a <:> t a'

    eeqtp_compat_contravariant : forall (i : level) (t : U i -> U i) .
                                    (forall (a a' : U i) . a <: a' -> t a' <: t a)
                                    -> forall (a a' : U i) . a <:> a' -> t a <:> t a'
