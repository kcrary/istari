open:Option
open:FiniteMap
# `FiniteMap`

### Simple finite maps

A finite map from `A` into `B` (`finite_map A B`) is a mapping from
`A` to `option B`, in which only finitely many arguments map to
anything other than `None`.

    finite_map : type:finite_map

The operations on a finite map are `lookup`, `empty`, `update`,
`remove`, and `merge`:

    lookup : type:lookup
           imp:lookup

    empty : type:empty
          imp:empty

    update : type:update
           imp:update

    remove : type:remove
           imp:remove

    merge : type:merge
          imp:merge

The update operation `update f a b` produces a new finite map that
maps `a` to `Some b`.  If `a` was already in `f`'s domain, it
overwrites `a`'s old mapping.  The merge operation `merge f g`
combines the two finite maps into one; if an argument is in both
domains, the left-hand mapping takes precedence.

To build a finite map requires the domain type to have decidable
equality.  The equality test is supplied to the `empty` operation.

    eqtest : type:eqtest
           = def:eqtest

    finite_map_impl_eqtest : type:finite_map_impl_eqtest

A recommended way to use `empty` is to define `eqt : eqtest A`, then
define `myempty` to be `empty eqt`.  If `myempty` is then made a [soft
constant](../terms.html#opacity), the lemmas that follow will work
with `myempty` without any additional effort.

Finite maps have extensional equality:

    finite_map_ext : type:finite_map_ext

Several principles determine how the operations interact with lookup:

    lookup_empty : type:lookup_empty

    lookup_update : type:lookup_update

    lookup_update_neq : type:lookup_update_neq

    lookup_remove : type:lookup_remove

    lookup_remove_neq : type:lookup_remove_neq

    lookup_merge_left : type:lookup_merge_left

    lookup_merge_right : type:lookup_merge_right

We can obtain other corollaries about finite maps using the above and
extensional equality:

    update_update : type:update_update

    update_update_neq : type:update_update_neq

    remove_empty : type:remove_empty

    remove_update : type:remove_update

    remove_update_neq : type:remove_update_neq

    remove_absent : type:remove_absent

    merge_empty_left : type:merge_empty_left

    merge_empty_right : type:merge_empty_right

    update_merge_left : type:update_merge_left

    update_merge_right : type:update_merge_right

    remove_merge : type:remove_merge

The derived notion of membership is useful:

    member : type:member
           = def:member
           imp:member

    remove_absent' : type:remove_absent'

    lookup_merge_left' : type:lookup_merge_left'

    lookup_merge_right' : type:lookup_merge_right'

    decidable_member : type:decidable_member



##### Mapping over finite maps


    map : type:map

    map_identity : type:map_identity

    map_compose : type:map_compose

    lookup_map : type:lookup_map

    map_empty : type:map_empty

    map_update : type:map_update

    map_remove : type:map_remove

    map_merge : type:map_merge

    member_map : type:member_map



##### Combination (a.k.a. symmetric merge)

    combine : type:combine
            = def:combine
            imp:combine

    combine_transpose : type:combine_transpose

    lookup_combine_left : type:lookup_combine_left

    lookup_combine_right : type:lookup_combine_right

    lookup_combine_both : type:lookup_combine_both

    combine_empty_left : type:combine_empty_left

    combine_empty_right : type:combine_empty_right

    combine_update_left_absent : type:combine_update_left_absent

    combine_update_right_absent : type:combine_update_right_absent

    combine_update_left_present : type:combine_update_left_present

    combine_update_right_present : type:combine_update_right_present

    combine_remove_left_absent : type:combine_remove_left_absent

    combine_remove_right_absent : type:combine_remove_right_absent

    combine_remove_left_present : type:combine_remove_left_present

    combine_remove_right_present : type:combine_remove_right_present

    map_combine : type:map_combine



#### Finite map domains

Finite maps have finite domains, but it is difficult to obtain them
without a canonical ordering on the domain's type.  One version gives
the list quotiented by rearrangement:

    finite_map_domain_quotient : type:finite_map_domain_quotient

Another version gives the list quotiented by permutation:

    finite_map_domain_quotient_perm : type:finite_map_domain_quotient_perm

Still another version returns the domain unquotiented but squashed:

    finite_map_domain_squash : type:finite_map_domain_squash

Finally, although the domain (as a list) is underdetermined, its
length is determined:

    finite_map_domain_size : type:finite_map_domain_size



#### Generic finite maps

The submodule [`Class`](finite-map-class.html) defines a generic class
determining what it means to be a finite map.  It is used in the
implementation of the simple finite maps above.

The simple finite maps are defined using tools from the `Class`
submodule.  The discrepancy between the types of `empty` versus `emp`
(*q.v.*) is mediated using the `finite_map_impl_eqtest` lemma (above)
that extracts an equality test from a finite map.  (By definition, all
equality tests at the same type are equal.)

    FiniteMap_finite_map : type:FiniteMap_finite_map

    FiniteMap_finite_map' : type:FiniteMap_finite_map'



#### Miscellaneous

    finite_map_subtype : type:finite_map_subtype

    equipollent_finite_map : type:equipollent_finite_map

    subpollent_finite_map : type:subpollent_finite_map

    kindlike_finite_map : type:kindlike_finite_map
