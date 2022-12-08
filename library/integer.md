open:Integer
# `Integer`

The `integer` type is primitive but aliased in the `Integer` module:

    integer : type:integer

Integer literals are written using a `` z` `` parsing directive.  For
example, zero is ``z`0``.


### Plus and negation

    (* +z *)
    plusz : type:plusz

    (* ~z *)
    negz : type:negz

    (* -z *)
    minusz : type:minusz
           = def:minusz

    neq_0_1 : type:neq_0_1

    plusz_commute : type:plusz_commute

    plusz_assoc : type:plusz_assoc

    plusz_id_l : type:plusz_id_l

    plusz_id_r : type:plusz_id_r

    plusz_inverse_l : type:plusz_inverse_l

    plusz_inverse_r : type:plusz_inverse_r

    negz_invol : type:negz_invol

    negz_plusz : type:negz_plusz

    plusz_compat : type:plusz_compat

    negz_compat : type:negz_compat


### Inequalities

    (* <z= *)
    leqz : type:leqz

    (* <z *)
    ltz : type:ltz
        = def:ltz

    leqz_inhabitant : type:leqz_inhabitant

    ltz_inhabitant : type:ltz_inhabitant

    leqz_0_1 : type:leqz_0_1

    leqz_refl : type:leqz_refl

    leqz_refl_eq : type:leqz_refl_eq

    leqz_trans : type:leqz_trans

    leqz_antisymm : type:leqz_antisymm

This one gives transitivity in the form needed for rewriting:

    leqz_implication : type:leqz_implication

    ltz_impl_leqz : type:ltz_impl_leqz

    ltz_irrefl : type:ltz_irrefl

    ltz_trans : type:ltz_trans

    leqz_ltz_trans : type:leqz_ltz_trans

    ltz_leqz_trans : type:ltz_leqz_trans

    plusz_leqz : type:plusz_leqz

    plusz_cancel_leqz_l : type:plusz_cancel_leqz_l

    plusz_cancel_leqz_r : type:plusz_cancel_leqz_r

    plus_cancel_leq_leq_l : type:plus_cancel_leq_leq_l

    plus_cancel_leq_leq_r : type:plus_cancel_leq_leq_r

    negz_leqz : type:negz_leqz

    negz_leqz' : type:negz_leqz'

    negz_ltz : type:negz_ltz

    negz_ltz' : type:negz_ltz'

    not_leqz : type:not_leqz

    not_ltz : type:not_ltz


### Effective comparisons

    eqzb : type:eqzb

    leqzb : type:leqzb

    ltzb : type:ltzb
         = def:ltzb

    istrue_eqzb : type:istrue_eqzb

    istrue_leqzb : type:istrue_leqzb

    istrue_ltzb : type:istrue_ltzb


### Induction

We say that `a` is smaller than `b` if they are both non-positive and
`b <z a`, or if they are both non-negative and `a <z b`:

    smaller : type:smaller
            = def:smaller


Smaller is well-founded, giving us strong induction for integers:

    smaller_well_founded : type:smaller_well_founded


As a corollary, we can build an iterator for integers.  It has three
cases: a base case for zero, a negative case that works downwards, and a
positive case that works upwards.

    integer_iter : type:integer_iter
                 =rec= defrec:integer_iter


### Relation to natural numbers

    nat_to_integer : type:nat_to_integer
                   =rec= defrec:nat_to_integer

    nat_to_integer (zero) --> z`0
    nat_to_integer (succ n) --> plusz z`1 (nat_to_integer n)

    integer_to_nat : type:integer_to_nat
                   =rec= defrec:integer_to_nat

    nat_to_integer_inv : type:nat_to_integer_inv

    integer_to_nat_inv : type:integer_to_nat_inv

    nat_to_integer_nonneg : type:nat_to_integer_nonneg

    nat_to_integer_mono : type:nat_to_integer_mono

    plus_to_integer : type:plus_to_integer

    integer_to_nat_succ : type:integer_to_nat_succ

    integer_to_nat_mono : type:integer_to_nat_mono

    plusz_to_nat : type:plusz_to_nat

    minus_to_integer : type:minus_to_integer

    minusz_to_nat : type:minusz_to_nat
