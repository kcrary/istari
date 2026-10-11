open:Real
open:RealSupremum
overload:real
# `RealSupremum`

Expressions in this file are rendered using the `real`
[overloading mode](../overloading.html).

    supremum : type:supremum
             = def:supremum

    supremum_ub : type:supremum_ub

The way least-upper-bound is defined in `supremum` is classically
equivalent to the usual definition, but it is stronger constructively.
(Note the not-not in `classical_lub_to_constructive`.)

    constructive_lub_to_classical : type:constructive_lub_to_classical

    classical_lub_to_constructive : type:classical_lub_to_constructive

    supremum_lub : type:supremum_lub

    supremum_unique : type:supremum_unique

    supremum_ext : type:supremum_ext

Classically, a supremum exists for every nonempty, bounded set.  We
require an additional condition to make the supremum computable: for
any `x < y`, either `x` is not an upper bound or `y` is an upper
bound.  (Another sufficient condition would be that it is decidable
whether an arbitrary real is an upper bound or not, but that condition
is typically false.)

    supremum_exists : type:supremum_exists

The above includes the technical condition that the predicate defining
the set be squash-stable.  That requirement can be weakened:

    supremum_exists_sqsq : type:supremum_exists_sqsq

    supremum_exists_symmetrical : type:supremum_exists_symmetrical

In this last and most general version, the predicate is required to be
*symmetrical* in the sense of [`Quotient`](quotient.html).  This
condition holds with considerable generality.  It is required (in
`infinite_sequence_squish`, below) in order to turn a sequence of
squished, qualifying elements into a squished sequence of qualifying
elements.


### Tools for constructing infinite sequences

    infinite_sequence : type:infinite_sequence

    infinite_sequence_squish : type:infinite_sequence_squish
