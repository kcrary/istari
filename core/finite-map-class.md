open:Option
open:FiniteMap
open:Class
open:Factory
# `FiniteMap.Class`


### Generic finite maps

The module `FiniteMap.Class` defines a generic class determining what
it means to be a finite map:

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

The `FiniteMap` class does not include a merge operation.  The
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


### The factory

The `FiniteMap.Class.Factory` submodule provides tools to assist in
constructing finite maps.  First, there is a class of generic finite
maps *minus extensional equality.*

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

Another class gives finite maps with merge but minus extensionality:

    PreFiniteMapMerge : type:PreFiniteMapMerge
                      = def:PreFiniteMapMerge

    quotient_mer : type:quotient_mer

    FiniteMapMerge_qpfm : type:FiniteMapMerge_qpfm
