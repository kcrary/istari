open:FiniteMap
open:List
open:Option
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


#### Finite map domains

Finite maps have finite domains, but it is difficult to obtain them
without a canonical ordering on the domain's type.  One version gives
the list quotiented by rearrangement:

    finite_map_domain_quotient : type:finite_map_domain_quotient

Another version returns the domain squashed:

    finite_map_domain_squash : type:finite_map_domain_squash


### Generic finite maps

We can define a generic class determining what it means to be a finite map:

    FiniteMap : type:FiniteMap
              = def:FiniteMap

We can then prove properties about such maps similar to what we showed
above for simple finite maps:

    FiniteMap_look_emp : type:FiniteMap_look_emp

    FiniteMap_look_upd : type:FiniteMap_look_upd

    FiniteMap_look_upd_neq : type:FiniteMap_look_upd_neq

    FiniteMap_look_rem : type:FiniteMap_look_rem

    FiniteMap_look_rem_neq : type:FiniteMap_look_rem_neq

    FiniteMap_upd_upd : type:FiniteMap_upd_upd

    FiniteMap_upd_upd_neq : type:FiniteMap_upd_upd_neq

    FiniteMap_rem_emp : type:FiniteMap_rem_emp

    FiniteMap_rem_upd : type:FiniteMap_rem_upd

    FiniteMap_rem_upd_neq : type:FiniteMap_rem_upd_neq

    FiniteMap_rem_absent : type:FiniteMap_rem_absent

Note that generic finite maps require that the domain's equality is
decidable, and thus an equality test is not supplied to the `emp`
operation.


### Generic finite maps with merge

The `FiniteMap` class does not include a merge option.  The
`FiniteMapMerge` class adds one:

    FiniteMapMerge : type:FiniteMapMerge
                   = def:FiniteMapMerge

    FiniteMapMerge_look_mer_left : type:FiniteMapMerge_look_mer_left

    FiniteMapMerge_look_mer_right : type:FiniteMapMerge_look_mer_right

    FiniteMapMerge_mer_emp_left : type:FiniteMapMerge_mer_emp_left

    FiniteMapMerge_mer_emp_right : type:FiniteMapMerge_mer_emp_right

    FiniteMapMerge_upd_mer_left : type:FiniteMapMerge_upd_mer_left

    FiniteMapMerge_upd_mer_right : type:FiniteMapMerge_upd_mer_right

    FiniteMapMerge_rem_mer : type:FiniteMapMerge_rem_mer


### Generic finite maps minus extensionality

To assist in building finite maps, there is a class that leaves out
extensionality equality:

    PreFiniteMap : type:PreFiniteMap
                 = def:PreFiniteMap

Given a pre-finite-map, one can build a finite map by quotienting it:

    (* "quotient pre-finite-map" *)
    qpfm : type:qpfm
         = def:qpfm

    quotient_emp : type:quotient_emp

    quotient_look : type:quotient_look

    quotient_upd : type:quotient_upd

    quotient_rem : type:quotient_rem

    FiniteMap_qpfm : type:FiniteMap_qpfm

Another class gives finite maps with merge but without extensionality:

    PreFiniteMapMerge : type:PreFiniteMapMerge
                      = def:PreFiniteMapMerge

    quotient_mer : type:quotient_mer

    FiniteMapMerge_qpfm : type:FiniteMapMerge_qpfm

The simple finite maps are defined using these tools.  The discrepancy
between the types of `empty` versus `emp` is mediated using a lemma
that extracts an equality test from a finite map:

    finite_map_impl_eqtest : type:finite_map_impl_eqtest

(By definition, all equality tests at the same type are equal.)
