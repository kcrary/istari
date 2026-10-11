open:Real
open:RealSequence
overload:real
# `RealSequence`

Expressions in this file are rendered using the `real`
[overloading mode](../overloading.html).

### Convergence

    converges : type:converges
              = def:converges

    converges_unique : type:converges_unique

    converges_equal : type:converges_equal

    converges_from_tail : type:converges_from_tail

    cauchy : type:cauchy
           = def:cauchy

    cauchy_impl_converges : type:cauchy_impl_converges

    converges_impl_cauchy : type:converges_impl_cauchy

    cauchy_iff_converges : type:cauchy_iff_converges

    converges_constant : type:converges_constant

    converges_plusr : type:converges_plusr

    converges_negr : type:converges_negr

    converges_minusr : type:converges_minusr

    converges_timesr : type:converges_timesr

    converges_invr : type:converges_invr

    converges_maxr : type:converges_maxr

    converges_minr : type:converges_minr

    converges_leqr : type:converges_leqr

When an increasing sequence and a decreasing sequence, with the
decreasing sequence above the increasing one, and they grow closer at
a steady rate, both sequences converge to the same value.
    
    dual_convergence : type:dual_convergence


### Series

The partial sum operator turns a series into a sequence:

    sums : type:sums
         = def:sums

The segment sum `sums s m n` adds the elements from `s m` (inclusive)
to `s n` (exclusive):

    ssums_all : type:ssums_all

    ssums_split : type:ssums_split

    sums_split : type:sums_split

    sums_difference : type:sums_difference

    ssums_empty : type:ssums_empty

    ssums_singleton : type:ssums_singleton

    ssums_left : type:ssums_left

    ssums_right : type:ssums_right

    ssums_right_succ : type:ssums_right_succ

We use the word "convergent" (as opposed to "converges"), to say that
a series converges.  (More precisely, to say that its partial sums
converge.)  Since we do not define "convergent" formally (we just use
it in names), we can use it loosely to refer both to when a series
converges (at all) and to when it converges to a particular value.

    convergent_absolutely : type:convergent_absolutely
                          = def:convergent_absolutely

    convergent_absolutely_impl_convergent : type:convergent_absolutely_impl_convergent

    convergent_impl_converges_zero : type:convergent_impl_converges_zero

    convergent_plusr : type:convergent_plusr

    convergent_timesr_const : type:convergent_timesr_const

    sums_nexpr_increment : type:sums_nexpr_increment

    convergent_nexpr : type:convergent_nexpr

    comparison_test : type:comparison_test

    convergent_split : type:convergent_split

    convergent_from_tail : type:convergent_from_tail

    ratio_test : type:ratio_test

    convergent_alternation : type:convergent_alternation
