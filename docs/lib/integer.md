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

    ltz_0_1 : z`0 <z z`1

    leqz_neg1_0 : z`-1 <z z`0

    ltz_neg1_0 : z`-1 <z z`0

    leqz_refl : forall (a : integer) . a <z= a

    leqz_refl_eq : forall (a b : integer) . a = b : integer -> a <z= b

    leqz_trans : forall (a b c : integer) . a <z= b -> b <z= c -> a <z= c

    leqz_antisymm : forall (a b : integer) . a <z= b -> b <z= a -> a = b : integer

This one gives transitivity in the form needed for rewriting:

    leqz_implication : forall (a a' b b' : integer) . a' <z= a -> b <z= b' -> a <z= b -> a' <z= b'

    ltz_impl_leqz : forall (a b : integer) . a <z b -> a <z= b

    ltz_impl_neq : forall (a b : integer) . a <z b -> a != b : integer

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

    (* =z? *)
    eqzb : integer -> integer -> bool

    (* <z=? *)
    leqzb : integer -> integer -> bool

    (* <z? *)
    ltzb : integer -> integer -> bool
         = fn a b . z`1 +z a <z=? b

    (* !z=? *)
    neqzb : integer -> integer -> bool
          = fn a b . Bool.notb (a =z? b)

    istrue_eqzb : forall (a b : integer) . Bool.istrue (a =z? b) <-> a = b : integer

    istrue_neqzb : forall (a b : integer) . Bool.istrue (a !z=? b) <-> a != b : integer

    istrue_leqzb : forall (a b : integer) . Bool.istrue (a <z=? b) <-> a <z= b

    istrue_ltzb : forall (a b : integer) . Bool.istrue (a <z? b) <-> a <z b

    notb_eqzb : forall (a b : integer) . Bool.notb (a =z? b) = a !z=? b : bool

    notb_neqzb : forall (a b : integer) . Bool.notb (a !z=? b) = a =z? b : bool

    notb_leqzb : forall (a b : integer) . Bool.notb (a <z=? b) = b <z? a : bool

    notb_ltzb : forall (a b : integer) . Bool.notb (a <z? b) = b <z=? a : bool


### Induction

We say that `a` is smaller than `b` when `b` < `a` &le; 0 or 0 &le; `a` < `b`:

    smaller : integer -> integer -> U 0
            = fn a b . b <z a & a <z= z`0 % a <z b & z`0 <z= a


Smaller is well-founded, giving us strong induction for integers:

    smaller_well_founded : forall (a : integer) . Acc.Acc integer smaller a


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
                          if z`0 =z? a
                          then hz
                          else (if z`0 <z=? a
                                then hp (z`-1 +z a) () (integer_iter P hz hm hp (z`-1 +z a))
                                else hm (z`1 +z a) () (integer_iter P hz hm hp (z`1 +z a)))


### Relation to natural numbers

    nat_to_integer : nat -> integer
                   =rec= fn n . nat_case n z`0 (fn n' . z`1 +z nat_to_integer n')

    nat_to_integer (zero) --> z`0
    nat_to_integer (succ n) --> plusz z`1 (nat_to_integer n)

    integer_to_nat : integer -> nat
                   =rec= fn a . if a <z=? z`0 then 0 else succ (integer_to_nat (z`-1 +z a))

    nat_to_integer_inv : forall (n : nat) . integer_to_nat (nat_to_integer n) = n : nat

    integer_to_nat_inv : forall (a : integer) .
                            z`0 <z= a -> nat_to_integer (integer_to_nat a) = a : integer

    nat_to_integer_nonneg : forall (n : nat) . z`0 <z= nat_to_integer n

    nat_to_integer_mono : forall (m n : nat) . m <= n -> nat_to_integer m <z= nat_to_integer n

    nat_to_integer_mono_lt : forall (m n : nat) . m < n -> nat_to_integer m <z nat_to_integer n

    integer_to_nat_zero : integer_to_nat z`0 = 0 : nat

    integer_to_nat_succ : forall (a : integer) .
                             z`0 <z= a -> integer_to_nat (z`1 +z a) = succ (integer_to_nat a) : nat

    integer_to_nat_mono : forall (a b : integer) . a <z= b -> integer_to_nat a <= integer_to_nat b

    integer_to_nat_mono_lt : forall (a b : integer) .
                                z`0 <z= a -> a <z b -> integer_to_nat a < integer_to_nat b

    succ_to_integer : forall (n : nat) .
                         nat_to_integer (succ n) = z`1 +z nat_to_integer n : integer

    plus_to_integer : forall (m n : nat) .
                         nat_to_integer (m + n) = nat_to_integer m +z nat_to_integer n : integer

    plusz_to_nat : forall (a b : integer) .
                      z`0 <z= a
                      -> z`0 <z= b
                      -> integer_to_nat (a +z b) = integer_to_nat a + integer_to_nat b : nat

    pred_to_integer : forall (n : nat) .
                         0 < n -> nat_to_integer (Nat.pred n) = z`-1 +z nat_to_integer n : integer

    minus_to_integer : forall (m n : nat) .
                          n <= m
                          -> nat_to_integer (m - n)
                               = nat_to_integer m -z nat_to_integer n
                               : integer

    minusz_to_nat : forall (a b : integer) .
                       z`0 <z= b
                       -> b <z= a
                       -> integer_to_nat (a -z b) = integer_to_nat a - integer_to_nat b : nat

    eqb_to_integer : forall (m n : nat) . m =? n = nat_to_integer m =z? nat_to_integer n : bool

    eqzb_to_nat : forall (a b : integer) .
                     z`0 <z= a
                     -> z`0 <z= b
                     -> a =z? b = integer_to_nat a =? integer_to_nat b : bool

    leqb_to_integer : forall (m n : nat) . m <=? n = nat_to_integer m <z=? nat_to_integer n : bool

    leqzb_to_nat : forall (a b : integer) .
                      z`0 <z= a
                      -> z`0 <z= b
                      -> a <z=? b = integer_to_nat a <=? integer_to_nat b : bool

    ltb_to_integer : forall (m n : nat) . m <? n = nat_to_integer m <z? nat_to_integer n : bool

    ltzb_to_nat : forall (a b : integer) .
                     z`0 <z= a
                     -> z`0 <z= b
                     -> a <z? b = integer_to_nat a <? integer_to_nat b : bool

    neqb_to_integer : forall (m n : nat) . m !=? n = nat_to_integer m !z=? nat_to_integer n : bool

    neqzb_to_nat : forall (a b : integer) .
                      z`0 <z= a
                      -> z`0 <z= b
                      -> a !z=? b = integer_to_nat a !=? integer_to_nat b : bool


### Decidability

    eq_integer_decide : forall (a b : integer) . Decidable.decidable (a = b : integer)

    neq_integer_decide : forall (a b : integer) . Decidable.decidable (a != b : integer)

    leqz_decide : forall (a b : integer) . Decidable.decidable (a <z= b)

    ltz_decide : forall (a b : integer) . Decidable.decidable (a <z b)

    eq_integer_stable : forall (a b : integer) . Stable.stable (a = b : integer)

    neq_integer_stable : forall (a b : integer) . Stable.stable (a != b : integer)

    leqz_stable : forall (a b : integer) . Stable.stable (a <z= b)

    ltz_stable : forall (a b : integer) . Stable.stable (a <z b)

    leqz_iff_ltz_or_eq : forall (a b : integer) . a <z= b <-> a <z b % a = b : integer

    integer_trichotomy : forall (a b : integer) . a <z b % a = b : integer % b <z a

    integer_dichotomy : forall (a b : integer) . a <z= b % b <z a

    integer_dichotomy_weak : forall (a b : integer) . a <z= b % b <z= a

    integer_dichotomy_neq : forall (a b : integer) . a != b : integer -> a <z b % b <z a


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

    timesz_compat : forall (a a' b b' : integer) .
                       a = a' : integer -> b = b' : integer -> a *z b = a' *z b' : integer

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

    timesz_leqz_zero : forall (a b : integer) . z`0 <z= a -> z`0 <z= b -> z`0 <z= a *z b

    (* an alias for timesz_leqz_zero *)
    timesz_leqz_zero_pos_pos : forall (a b : integer) . z`0 <z= a -> z`0 <z= b -> z`0 <z= a *z b

    timesz_leqz_zero_pos_neg : forall (a b : integer) . z`0 <z= a -> b <z= z`0 -> a *z b <z= z`0

    timesz_leqz_zero_neg_pos : forall (a b : integer) . a <z= z`0 -> z`0 <z= b -> a *z b <z= z`0

    timesz_leqz_zero_neg_neg : forall (a b : integer) . a <z= z`0 -> b <z= z`0 -> z`0 <z= a *z b

    timesz_ltz_zero : forall (a b : integer) . z`0 <z a -> z`0 <z b -> z`0 <z a *z b

    (* an alias for timesz_ltz_zero *)
    timesz_ltz_zero_pos_pos : forall (a b : integer) . z`0 <z a -> z`0 <z b -> z`0 <z a *z b

    timesz_ltz_zero_pos_neg : forall (a b : integer) . z`0 <z a -> b <z z`0 -> a *z b <z z`0

    timesz_ltz_zero_neg_pos : forall (a b : integer) . a <z z`0 -> z`0 <z b -> a *z b <z z`0

    timesz_ltz_zero_neg_neg : forall (a b : integer) . a <z z`0 -> b <z z`0 -> z`0 <z a *z b

    integer_integral_domain : forall (a b : integer) .
                                 a *z b = z`0 : integer -> a = z`0 : integer % b = z`0 : integer

    timesz_neq_zero : forall (a b : integer) .
                         a != z`0 : integer -> b != z`0 : integer -> a *z b != z`0 : integer

    timesz_ltz_zero_invert : forall (a b : integer) .
                                z`0 <z a *z b -> a <z z`0 & b <z z`0 % z`0 <z a & z`0 <z b

    timesz_ltz_zero_invert_neg : forall (a b : integer) .
                                    a *z b <z z`0 -> a <z z`0 & z`0 <z b % z`0 <z a & b <z z`0

    times_to_integer : forall (m n : nat) .
                          nat_to_integer (m * n) = nat_to_integer m *z nat_to_integer n : integer

    timesz_to_nat : forall (a b : integer) .
                       z`0 <z= a
                       -> z`0 <z= b
                       -> integer_to_nat (a *z b) = integer_to_nat a * integer_to_nat b : nat

    timesz_ltz_l : forall (a b b' : integer) . z`0 <z a -> b <z b' -> a *z b <z a *z b'

    timesz_ltz_r : forall (a a' b : integer) . z`0 <z b -> a <z a' -> a *z b <z a' *z b

    timesz_cancel_l : forall (a b c : integer) .
                         c != z`0 : integer -> c *z a = c *z b : integer -> a = b : integer

    timesz_cancel_r : forall (a b c : integer) .
                         c != z`0 : integer -> a *z c = b *z c : integer -> a = b : integer

    timesz_cancel_leqz_l : forall (a b c : integer) . z`0 <z c -> c *z a <z= c *z b -> a <z= b

    timesz_cancel_leqz_r : forall (a b c : integer) . z`0 <z c -> a *z c <z= b *z c -> a <z= b

    timesz_cancel_ltz_l : forall (a b c : integer) . z`0 <z c -> c *z a <z c *z b -> a <z b

    timesz_cancel_ltz_r : forall (a b c : integer) . z`0 <z c -> a *z c <z b *z c -> a <z b

    timesz_cancel_leqz_l_remainder : forall (a b c r : integer) .
                                        z`0 <z c -> r <z c -> c *z a <z= c *z b +z r -> a <z= b

    timesz_cancel_leqz_r_remainder : forall (a b c r : integer) .
                                        z`0 <z c -> r <z c -> a *z c <z= b *z c +z r -> a <z= b


### Minimum/Maximum

    minz : integer -> integer -> integer
         = fn a b . if a <z=? b then a else b

    maxz : integer -> integer -> integer
         = fn a b . if a <z=? b then b else a

    negz_minz : forall (a b : integer) . ~z (minz a b) = maxz (~z a) (~z b) : integer

    negz_maxz : forall (a b : integer) . ~z (maxz a b) = minz (~z a) (~z b) : integer

    maxz_as_minz : forall (a b : integer) . maxz a b = ~z (minz (~z a) (~z b)) : integer

    minz_as_maxz : forall (a b : integer) . minz a b = ~z (maxz (~z a) (~z b)) : integer

    minz_commute : forall (a b : integer) . minz a b = minz b a : integer

    maxz_commute : forall (a b : integer) . maxz a b = maxz b a : integer

    minz_assoc : forall (a b c : integer) . minz (minz a b) c = minz a (minz b c) : integer

    maxz_assoc : forall (a b c : integer) . maxz (maxz a b) c = maxz a (maxz b c) : integer

    minz_leq_l : forall (a b : integer) . minz a b <z= a

    minz_leq_r : forall (a b : integer) . minz a b <z= b

    maxz_leq_l : forall (a b : integer) . a <z= maxz a b

    maxz_leq_r : forall (a b : integer) . b <z= maxz a b

    minz_glb : forall (a b c : integer) . c <z= a -> c <z= b -> c <z= minz a b

    maxz_lub : forall (a b c : integer) . a <z= c -> b <z= c -> maxz a b <z= c

    minz_eq_l : forall (a b : integer) . a <z= b -> minz a b = a : integer

    minz_eq_r : forall (a b : integer) . b <z= a -> minz a b = b : integer

    maxz_eq_l : forall (a b : integer) . b <z= a -> maxz a b = a : integer

    maxz_eq_r : forall (a b : integer) . a <z= b -> maxz a b = b : integer

    minz_idem : forall (a : integer) . minz a a = a : integer

    maxz_idem : forall (a : integer) . maxz a a = a : integer

    minz_dist_maxz_l : forall (a b c : integer) .
                          minz (maxz a b) c = maxz (minz a c) (minz b c) : integer

    minz_dist_maxz_r : forall (a b c : integer) .
                          minz a (maxz b c) = maxz (minz a b) (minz a c) : integer

    maxz_dist_minz_l : forall (a b c : integer) .
                          maxz (minz a b) c = minz (maxz a c) (maxz b c) : integer

    maxz_dist_minz_r : forall (a b c : integer) .
                          maxz a (minz b c) = minz (maxz a b) (maxz a c) : integer

    plusz_dist_minz_l : forall (a b c : integer) .
                           minz a b +z c = minz (a +z c) (b +z c) : integer

    plusz_dist_minz_r : forall (a b c : integer) .
                           a +z minz b c = minz (a +z b) (a +z c) : integer

    plusz_dist_maxz_l : forall (a b c : integer) .
                           maxz a b +z c = maxz (a +z c) (b +z c) : integer

    plusz_dist_maxz_r : forall (a b c : integer) .
                           a +z maxz b c = maxz (a +z b) (a +z c) : integer

    min_to_integer : forall (m n : nat) .
                        nat_to_integer (Nat.min m n)
                          = minz (nat_to_integer m) (nat_to_integer n)
                          : integer

    max_to_integer : forall (m n : nat) .
                        nat_to_integer (Nat.max m n)
                          = maxz (nat_to_integer m) (nat_to_integer n)
                          : integer

    minz_to_nat : forall (a b : integer) .
                     integer_to_nat (minz a b)
                       = Nat.min (integer_to_nat a) (integer_to_nat b)
                       : nat

    maxz_to_nat : forall (a b : integer) .
                     integer_to_nat (maxz a b)
                       = Nat.max (integer_to_nat a) (integer_to_nat b)
                       : nat
