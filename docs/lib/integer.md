# `Integer`

The `integer` type is primitive but aliased in the `Integer` module:

    integer : U 0

Integer literals are written using a `` z` `` parsing directive.  For
example, zero is ``z`0``.


### Plus and negation

    (* +z *)
    plusz : integer -> integer -> integer

    (* ~z *)
    negz : integer -> integer

    (* -z *)
    minusz : integer -> integer -> integer
           = fn x y . x +z ~z y

    neq_0_1 : z`0 = z`1 : integer -> void

    neq_0_neg1 : z`0 = z`-1 : integer -> void

    plusz_commute : forall (a b : integer) . a +z b = b +z a : integer

    plusz_assoc : forall (a b c : integer) . a +z b +z c = a +z (b +z c) : integer

    plusz_id_l : forall (a : integer) . z`0 +z a = a : integer

    plusz_id_r : forall (a : integer) . a +z z`0 = a : integer

    plusz_inverse_l : forall (a : integer) . ~z a +z a = z`0 : integer

    plusz_inverse_r : forall (a : integer) . a +z ~z a = z`0 : integer

    negz_invol : forall (a : integer) . ~z (~z a) = a : integer

    negz_plusz : forall (a b : integer) . ~z (a +z b) = ~z a +z ~z b : integer

    plusz_cancel_l : forall (a b c : integer) . c +z a = c +z b : integer -> a = b : integer

    plusz_cancel_r : forall (a b c : integer) . a +z c = b +z c : integer -> a = b : integer

    plusz_shift_l : forall (a b c : integer) . a = b +z c : integer <-> ~z b +z a = c : integer

    plusz_shift_r : forall (a b c : integer) . a +z b = c : integer <-> a = c +z ~z b : integer

    plusz_shift_lr : forall (a b c : integer) . a +z b = c : integer <-> b = ~z a +z c : integer

    plusz_shift_rl : forall (a b c : integer) . a = b +z c : integer <-> a +z ~z c = b : integer

    plusz_compat : forall (a a' b b' : integer) .
                      a = a' : integer -> b = b' : integer -> a +z b = a' +z b' : integer

    negz_compat : forall (a a' : integer) . a = a' : integer -> ~z a = ~z a' : integer


### Inequalities

    (* <z= *)
    leqz : integer -> integer -> U 0

    (* <z *)
    ltz : integer -> integer -> U 0
        = fn x y . z`1 +z x <z= y

    leqz_inhabitant : forall (a b : integer) . a <z= b -> () : a <z= b

    ltz_inhabitant : forall (a b : integer) . a <z b -> () : a <z b

    leqz_0_1 : z`0 <z= z`1

    leqz_refl : forall (a : integer) . a <z= a

    leqz_refl_eq : forall (a b : integer) . a = b : integer -> a <z= b

    leqz_trans : forall (a b c : integer) . a <z= b -> b <z= c -> a <z= c

    leqz_antisymm : forall (a b : integer) . a <z= b -> b <z= a -> a = b : integer

This one gives transitivity in the form needed for rewriting:

    leqz_implication : forall (a a' b b' : integer) . a' <z= a -> b <z= b' -> a <z= b -> a' <z= b'

    ltz_impl_leqz : forall (a b : integer) . a <z b -> a <z= b

    ltz_irrefl : forall (a : integer) . a <z a -> void

    ltz_trans : forall (a b c : integer) . a <z b -> b <z c -> a <z c

    leqz_ltz_trans : forall (a b c : integer) . a <z= b -> b <z c -> a <z c

    ltz_leqz_trans : forall (a b c : integer) . a <z b -> b <z= c -> a <z c

    ltz_succ : forall (a : integer) . a <z z`1 +z a

    leqz_succ : forall (a : integer) . a <z= z`1 +z a

    plusz_leqz : forall (a a' b b' : integer) . a <z= a' -> b <z= b' -> a +z b <z= a' +z b'

    plusz_cancel_leqz_l : forall (a b c : integer) . c +z a <z= c +z b -> a <z= b

    plusz_cancel_leqz_r : forall (a b c : integer) . a +z c <z= b +z c -> a <z= b

    plusz_cancel_leqz_leqz_l : forall (a a' b b' : integer) .
                                  a +z b <z= a' +z b' -> a' <z= a -> b <z= b'

    plusz_cancel_leqz_leqz_r : forall (a a' b b' : integer) .
                                  a +z b <z= a' +z b' -> b' <z= b -> a <z= a'

    plusz_shift_leqz_l : forall (a b c : integer) . a <z= b +z c <-> ~z b +z a <z= c

    plusz_shift_leqz_r : forall (a b c : integer) . a +z b <z= c <-> a <z= c +z ~z b

    plusz_shift_leqz_lr : forall (a b c : integer) . a +z b <z= c <-> b <z= ~z a +z c

    plusz_shift_leqz_rl : forall (a b c : integer) . a <z= b +z c <-> a +z ~z c <z= b

    plusz_ltz_l : forall (a a' b b' : integer) . a <z a' -> b <z= b' -> a +z b <z a' +z b'

    plusz_ltz_r : forall (a a' b b' : integer) . a <z= a' -> b <z b' -> a +z b <z a' +z b'

    plusz_ltz : forall (a a' b b' : integer) . a <z a' -> b <z b' -> a +z b <z a' +z b'

    plusz_cancel_ltz_l : forall (a b c : integer) . c +z a <z c +z b -> a <z b

    plusz_cancel_ltz_r : forall (a b c : integer) . a +z c <z b +z c -> a <z b

    plusz_shift_ltz_l : forall (a b c : integer) . a <z b +z c <-> ~z b +z a <z c

    plusz_shift_ltz_r : forall (a b c : integer) . a +z b <z c <-> a <z c +z ~z b

    plusz_shift_ltz_lr : forall (a b c : integer) . a +z b <z c <-> b <z ~z a +z c

    plusz_shift_ltz_rl : forall (a b c : integer) . a <z b +z c <-> a +z ~z c <z b

    negz_leqz : forall (a b : integer) . a <z= b -> ~z b <z= ~z a

    negz_leqz' : forall (a b : integer) . ~z b <z= ~z a -> a <z= b

    negz_ltz : forall (a b : integer) . a <z b -> ~z b <z ~z a

    negz_ltz' : forall (a b : integer) . ~z b <z ~z a -> a <z b

    not_leqz : forall (a b : integer) . not (a <z= b) <-> b <z a

    not_ltz : forall (a b : integer) . not (a <z b) <-> b <z= a

    ltz_from_leqz_neq : forall (a b : integer) . a <z= b -> not (a = b : integer) -> a <z b

    ltz_as_leqz_l : forall (a b : integer) . a <z b <-> z`1 +z a <z= b

    ltz_as_leqz_r : forall (a b : integer) . a <z b <-> a +z z`1 <z= b

    leqz_as_ltz_l : forall (a b : integer) . a <z= b <-> a <z z`1 +z b

    leqz_as_ltz_r : forall (a b : integer) . a <z= b <-> a <z b +z z`1



### Effective comparisons

    eqzb : integer -> integer -> bool

    leqzb : integer -> integer -> bool

    ltzb : integer -> integer -> bool
         = fn a b . leqzb (z`1 +z a) b

    istrue_eqzb : forall (a b : integer) . Bool.istrue (eqzb a b) <-> a = b : integer

    istrue_leqzb : forall (a b : integer) . Bool.istrue (leqzb a b) <-> a <z= b

    istrue_ltzb : forall (a b : integer) . Bool.istrue (ltzb a b) <-> a <z b


### Induction

We say that `a` is smaller than `b` if they are both non-positive and
`b <z a`, or if they are both non-negative and `a <z b`:

    smaller : integer -> integer -> U 0
            = fn a b . b <z a & a <z= z`0 % a <z b & z`0 <z= a


Smaller is well-founded, giving us strong induction for integers:

    smaller_well_founded : forall (a : integer) . Acc integer smaller a


As a corollary, we can build an iterator for integers.  It has three
cases: a base case for zero, a negative case that works downwards, and a
positive case that works upwards.

    integer_iter : intersect (i : level) .
                      forall (P : integer -> U i) .
                        P z`0
                        -> (forall (a : integer) . a <z= z`0 -> P a -> P (z`-1 +z a))
                        -> (forall (a : integer) . z`0 <z= a -> P a -> P (z`1 +z a))
                        -> forall (a : integer) . P a
                 =rec= fn P hz hm hp a .
                          if eqzb z`0 a
                          then hz
                          else (if leqzb z`0 a
                                then hp (z`-1 +z a) () (integer_iter P hz hm hp (z`-1 +z a))
                                else hm (z`1 +z a) () (integer_iter P hz hm hp (z`1 +z a)))


### Relation to natural numbers

    nat_to_integer : nat -> integer
                   =rec= fn n . natcase n z`0 (fn n' . z`1 +z nat_to_integer n')

    nat_to_integer (zero) --> z`0
    nat_to_integer (succ n) --> plusz z`1 (nat_to_integer n)

    integer_to_nat : integer -> nat
                   =rec= fn a . if leqzb a z`0 then 0 else succ (integer_to_nat (z`-1 +z a))

    nat_to_integer_inv : forall (n : nat) . integer_to_nat (nat_to_integer n) = n : nat

    integer_to_nat_inv : forall (a : integer) .
                            z`0 <z= a -> nat_to_integer (integer_to_nat a) = a : integer

    nat_to_integer_nonneg : forall (n : nat) . z`0 <z= nat_to_integer n

    nat_to_integer_mono : forall (m n : nat) . m <= n -> nat_to_integer m <z= nat_to_integer n

    nat_to_integer_mono_lt : forall (m n : nat) . m < n -> nat_to_integer m <z nat_to_integer n

    plus_to_integer : forall (m n : nat) .
                         nat_to_integer (m + n) = nat_to_integer m +z nat_to_integer n : integer

    integer_to_nat_succ : forall (a : integer) .
                             z`0 <z= a -> integer_to_nat (z`1 +z a) = succ (integer_to_nat a) : nat

    integer_to_nat_mono : forall (a b : integer) .
                             z`0 <z= a -> a <z= b -> integer_to_nat a <= integer_to_nat b

    integer_to_nat_mono_lt : forall (a b : integer) .
                                z`0 <z= a -> a <z b -> integer_to_nat a < integer_to_nat b

    plusz_to_nat : forall (a b : integer) .
                      z`0 <z= a
                      -> z`0 <z= b
                      -> integer_to_nat (a +z b) = integer_to_nat a + integer_to_nat b : nat

    minus_to_integer : forall (m n : nat) .
                          n <= m
                          -> nat_to_integer (m - n)
                               = nat_to_integer m -z nat_to_integer n
                               : integer

    minusz_to_nat : forall (a b : integer) .
                       z`0 <z= b
                       -> b <z= a
                       -> integer_to_nat (a -z b) = integer_to_nat a - integer_to_nat b : nat


### Decidability

    eq_integer_decide : forall (a b : integer) . Decidable.decidable (a = b : integer)

    leqz_decide : forall (a b : integer) . Decidable.decidable (a <z= b)

    ltz_decide : forall (a b : integer) . Decidable.decidable (a <z b)

    eq_integer_stable : forall (a b : integer) . Stable.stable (a = b : integer)

    leqz_stable : forall (a b : integer) . Stable.stable (a <z= b)

    ltz_stable : forall (a b : integer) . Stable.stable (a <z b)

    leqz_iff_ltz_or_eq : forall (a b : integer) . a <z= b <-> a <z b % a = b : integer

    integer_trichotomy : forall (a b : integer) . a <z b % a = b : integer % b <z a

    integer_dichotomy : forall (a b : integer) . a <z= b % b <z a

    integer_dichotomy_neq : forall (a b : integer) . not (a = b : integer) -> a <z b % b <z a


### Multiplication

    (* *z *)
    timesz : integer -> integer -> integer

    timesz_id_l : forall (a : integer) . z`1 *z a = a : integer

    timesz_id_r : forall (a : integer) . a *z z`1 = a : integer

    timesz_ann_l : forall (a : integer) . z`0 *z a = z`0 : integer

    timesz_ann_r : forall (a : integer) . a *z z`0 = z`0 : integer

    timesz_commute : forall (a b : integer) . a *z b = b *z a : integer

    timesz_assoc : forall (a b c : integer) . a *z b *z c = a *z (b *z c) : integer

    timesz_dist_plusz_l : forall (a b c : integer) . (a +z b) *z c = a *z c +z b *z c : integer

    timesz_dist_plusz_r : forall (a b c : integer) . a *z (b +z c) = a *z b +z a *z c : integer

    negz_dist_timesz_l : forall (a b : integer) . ~z (a *z b) = ~z a *z b : integer

    negz_dist_timesz_r : forall (a b : integer) . ~z (a *z b) = a *z ~z b : integer

    negz_as_timesz : forall (a : integer) . ~z a = z`-1 *z a : integer

    timesz_leqz : forall (a a' b b' : integer) .
                     z`0 <z= a -> z`0 <z= b -> a <z= a' -> b <z= b' -> a *z b <z= a' *z b'

    (* an alias for timesz_leqz *)
    timesz_leqz_pos_pos : forall (a a' b b' : integer) .
                             z`0 <z= a -> z`0 <z= b -> a <z= a' -> b <z= b' -> a *z b <z= a' *z b'

    timesz_leqz_neg_neg : forall (a a' b b' : integer) .
                             a' <z= z`0
                             -> b' <z= z`0
                             -> a <z= a'
                             -> b <z= b'
                             -> a' *z b' <z= a *z b

    timesz_leqz_pos_neg : forall (a a' b b' : integer) .
                             z`0 <z= a -> b' <z= z`0 -> a <z= a' -> b <z= b' -> a' *z b <z= a *z b'

    timesz_leqz_neg_pos : forall (a a' b b' : integer) .
                             a' <z= z`0 -> z`0 <z= b -> a <z= a' -> b <z= b' -> a *z b' <z= a' *z b

    timesz_leqz_l : forall (a b b' : integer) . z`0 <z= a -> b <z= b' -> a *z b <z= a *z b'

    timesz_leqz_r : forall (a a' b : integer) . z`0 <z= b -> a <z= a' -> a *z b <z= a' *z b

    timesz_leqz_l_neg : forall (a b b' : integer) . a <z= z`0 -> b <z= b' -> a *z b' <z= a *z b

    timesz_leqz_r_neg : forall (a a' b : integer) . b <z= z`0 -> a <z= a' -> a' *z b <z= a *z b

    timesz_ltz_zero : forall (a b : integer) . z`0 <z a -> z`0 <z b -> z`0 <z a *z b

    (* an alias for timesz_ltz_zero *)
    timesz_ltz_zero_pos_pos : forall (a b : integer) . z`0 <z a -> z`0 <z b -> z`0 <z a *z b

    timesz_ltz_zero_pos_neg : forall (a b : integer) . z`0 <z a -> b <z z`0 -> a *z b <z z`0

    timesz_ltz_zero_neg_pos : forall (a b : integer) . a <z z`0 -> z`0 <z b -> a *z b <z z`0

    timesz_ltz_zero_neg_neg : forall (a b : integer) . a <z z`0 -> b <z z`0 -> z`0 <z a *z b

    integer_integral_domain : forall (a b : integer) .
                                 a *z b = z`0 : integer -> a = z`0 : integer % b = z`0 : integer

    timesz_ltz_zero_invert : forall (a b : integer) .
                                z`0 <z a *z b -> a <z z`0 & b <z z`0 % z`0 <z a & z`0 <z b

    times_to_integer : forall (m n : nat) .
                          nat_to_integer (m * n) = nat_to_integer m *z nat_to_integer n : integer

    timesz_ltz_l : forall (a b b' : integer) . z`0 <z a -> b <z b' -> a *z b <z a *z b'

    timesz_ltz_r : forall (a a' b : integer) . z`0 <z b -> a <z a' -> a *z b <z a' *z b

    timesz_cancel_leqz_l : forall (a b c : integer) . z`0 <z c -> c *z a <z= c *z b -> a <z= b

    timesz_cancel_leqz_r : forall (a b c : integer) . z`0 <z c -> a *z c <z= b *z c -> a <z= b

    timesz_cancel_leqz_l_remainder : forall (a b c r : integer) .
                                        z`0 <z c -> r <z c -> c *z a <z= c *z b +z r -> a <z= b

    timesz_cancel_leqz_r_remainder : forall (a b c r : integer) .
                                        z`0 <z c -> r <z c -> a *z c <z= b *z c +z r -> a <z= b
