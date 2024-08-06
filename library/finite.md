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

    decidable_forall_finite : type:decidable_forall_finite

    decidable_exists_finite : type:decidable_exists_finite

    decidable_exists_finite_simple : type:decidable_exists_finite_simple
