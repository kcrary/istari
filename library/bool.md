open:Bool
# `Bool`

The `bool` type is primitive, but aliased in the `Bool` module:

    bool : type:bool
    true : type:true
    false : type:false


### The `istrue` predicate

    istrue : type:istrue
           = def:istrue

    istrue_inhabitant : type:istrue_inhabitant

    istrue_true : type:istrue_true

    not_istrue_false : type:not_istrue_false

    istrue_iff_eq_true : type:istrue_iff_eq_true

    not_istrue_iff_eq_false : type:not_istrue_iff_eq_false

    iff_eq_bool : type:iff_eq_bool


### Boolean operations

    notb : type:notb
         = def:notb

    andb : type:andb
         = def:andb

    orb : type:orb
        = def:orb

    impb : type:impb
         = def:impb

    notb_invol : type:notb_invol

    notb_andb : type:notb_andb

    notb_orb : type:notb_orb

    notb_impb : type:notb_impb

    impb_as_orb : type:impb_as_orb

    andb_commute : type:andb_commute

    orb_commute : type:orb_commute

    andb_assoc : type:andb_assoc

    orb_assoc : type:orb_assoc

    impb_curry : type:impb_curry

    andb_id_l : type:andb_id_l

    andb_id_r : type:andb_id_r

    orb_id_l : type:orb_id_l

    orb_id_r : type:orb_id_r

    impb_id_l : type:impb_id_l

    andb_ann_l : type:andb_ann_l

    andb_ann_r : type:andb_ann_r

    orb_ann_l : type:orb_ann_l

    orb_ann_r : type:orb_ann_r

    impb_ann_l : type:impb_ann_l

    impb_ann_r : type:impb_ann_r

    ite_notb : type:ite_notb

    istrue_notb : type:istrue_notb

    istrue_andb : type:istrue_andb

    istrue_orb : type:istrue_orb

    istrue_impb : type:istrue_impb

    istrue_true_iff : type:istrue_true_iff

    istrue_false_iff : type:istrue_false_iff
