open:Misc
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

    nonsense : type:nonsense
             = def:nonsense

The important property of `nonsense` is *everything* belongs to
nonsense, even terms that would normally be ill-formed.  As a
corollary, every type is a subtype of nonsense:

    nonsense_subtype : type:nonsense_subtype

Extensional type equivalence can be mapped through any covariant or
contravariant type operator:

    eeqtp_compat_covariant : type:eeqtp_compat_covariant

    eeqtp_compat_contravariant : type:eeqtp_compat_contravariant
