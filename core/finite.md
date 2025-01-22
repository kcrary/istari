open:Finite
# `Finite`

A form of Kuratowski finiteness:

    finite : type:finite
           = def:finite
           imp:finite

Note that the list may contain a superset of the elements satisfying
`P`.  This makes the definition easier to work with.  For example, the
simple form of the `finite_subset` lemma depends on it.

    finite_subset : type:finite_subset

When the underlying type changes, we can show that a set is finite
by showing that its image through a function is finite, provided that
function is injective.  It is convenient to establish the function is
injective by requiring a left inverse.

    map_through_finite : type:map_through_finite

We only actually need the function to apply for elements of `P`.

    map_through_finite_gen : type:map_through_finite_gen

    finite_exists : type:finite_exists

    decidable_forall_finite : type:decidable_forall_finite

    decidable_exists_finite : type:decidable_exists_finite

    decidable_exists_finite_simple : type:decidable_exists_finite_simple

We can show that a set of functions is finite if the functions only
vary on a finite and decidable portion of the domain, and each varying
domain element maps to finitely many results.

    finite_function_dep : type:finite_function_dep

    finite_function : type:finite_function

Finiteness allows the list to contain a superset, but if the predicate
is also decidable, we can obtain a precise list.

    enumerate_finite : type:enumerate_finite
