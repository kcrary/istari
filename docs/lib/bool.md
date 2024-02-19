# `Bool`

The `bool` type is primitive, but aliased in the `Bool` module:

    bool : U 0
    true : bool
    false : bool


### The `istrue` predicate

    istrue : bool -> U 0
           = fn b . if b then unit else void

    istrue_inhabitant : forall (b : bool) . istrue b -> () : istrue b

    istrue_true : istrue true

    not_istrue_false : not (istrue false)

    istrue_iff_eq_true : forall (b : bool) . istrue b <-> b = true : bool

    not_istrue_iff_eq_false : forall (b : bool) . not (istrue b) <-> b = false : bool

    not_not_istrue_iff_eq_true : forall (b : bool) . not (not (istrue b)) <-> b = true : bool

    iff_eq_bool : forall (b c : bool) . (istrue b <-> istrue c) <-> b = c : bool


### Boolean operations

    notb : bool -> bool
         = fn b . if b then false else true

    andb : bool -> bool -> bool
         = fn b c . if b then c else false

    orb : bool -> bool -> bool
        = fn b c . if b then true else c

    impb : bool -> bool -> bool
         = fn b c . if b then c else true

    notb_invol : forall (b : bool) . notb (notb b) = b : bool

    notb_andb : forall (b c : bool) . notb (andb b c) = orb (notb b) (notb c) : bool

    notb_orb : forall (b c : bool) . notb (orb b c) = andb (notb b) (notb c) : bool

    notb_impb : forall (b c : bool) . notb (impb b c) = andb b (notb c) : bool

    impb_as_orb : forall (b c : bool) . impb b c = orb (notb b) c : bool

    andb_commute : forall (b c : bool) . andb b c = andb c b : bool

    orb_commute : forall (b c : bool) . orb b c = orb c b : bool

    andb_assoc : forall (b c d : bool) . andb (andb b c) d = andb b (andb c d) : bool

    orb_assoc : forall (b c d : bool) . orb (orb b c) d = orb b (orb c d) : bool

    impb_curry : forall (b c d : bool) . impb (andb b c) d = impb b (impb c d) : bool

    andb_id_l : forall (b : bool) . andb true b = b : bool

    andb_id_r : forall (b : bool) . andb b true = b : bool

    orb_id_l : forall (b : bool) . orb false b = b : bool

    orb_id_r : forall (b : bool) . orb b false = b : bool

    impb_id_l : forall (b : bool) . impb true b = b : bool

    andb_ann_l : forall (b : bool) . andb false b = false : bool

    andb_ann_r : forall (b : bool) . andb b false = false : bool

    orb_ann_l : forall (b : bool) . orb true b = true : bool

    orb_ann_r : forall (b : bool) . orb b true = true : bool

    impb_ann_l : forall (b : bool) . impb false b = true : bool

    impb_ann_r : forall (b : bool) . impb b true = true : bool

    ite_notb : forall (i : level) (a : U i) (b : bool) (x y : a) .
                  (if notb b then x else y) = (if b then y else x) : a

    istrue_notb : forall (b : bool) . istrue (notb b) <-> not (istrue b)

    istrue_andb : forall (b c : bool) . istrue (andb b c) <-> istrue b & istrue c

    istrue_orb : forall (b c : bool) . istrue (orb b c) <-> istrue b % istrue c

    istrue_impb : forall (b c : bool) . istrue (impb b c) <-> (istrue b -> istrue c)

    istrue_true_iff : istrue true <-> unit

    istrue_false_iff : istrue false <-> void
