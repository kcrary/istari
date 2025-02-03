# `Natural`

A doppleganger of the `Nat` module, but using "native" arithmetic to
implement natural numbers instead of a datatype.

    natural : U 0

Zero is written `` z`0 ``.

    succn : natural -> natural
          = fn n . z`1 +N n

The iterator for natural numbers:

    natural_iter : intersect (i : level) .
                      forall (P : natural -> U i) .
                        P z`0
                        -> (forall (n : natural) . P n -> P (succn n))
                        -> forall (n : natural) . P n

In lieu of reductions (such as `nat_iter _ hz _ (zero) --> hz`), the
library has equality lemmas:

       natural_iter_zeron : forall
                               (i : level)
                               (P : natural -> U i)
                               (hz : P z`0)
                               (hs : forall (n : natural) . P n -> P (succn n)) .
                               natural_iter P hz hs z`0 = hz : P z`0

       natural_iter_succn : forall
                               (i : level)
                               (P : natural -> U i)
                               (hz : P z`0)
                               (hs : forall (n : natural) . P n -> P (succn n))
                               (n : natural) .
                               natural_iter P hz hs (succn n)
                                 = hs n (natural_iter P hz hs n)
                                 : P (succn n)

A simpler case-analysis operation:

    natural_case : intersect (i : level) (a : U i) . natural -> a -> (natural -> a) -> a

       natural_case_zeron : forall (i : level) (a : U i) (hz : a) (hs : natural -> a) .
                               natural_case z`0 hz hs = hz : a

       natural_case_succn : forall
                               (i : level)
                               (a : U i)
                               (hz : a)
                               (hs : natural -> a)
                               (n : natural) .
                               natural_case (succn n) hz hs = hs n : a


### Equality

    eq_0_succn_not : forall (n : natural) . z`0 = succn n : natural -> void

    eq_succn_0_not : forall (n : natural) . succn n = z`0 : natural -> void

    succn_inj : forall (m n : natural) . succn m = succn n : natural -> m = n : natural


### Inequalities

    (* <N= *)
    leqn : natural -> natural -> U 0

    (* <N *)
    ltn : natural -> natural -> U 0

    leqn_inhabitant : forall (m n : natural) . m <N= n -> () : m <N= n

    ltn_inhabitant : forall (m n : natural) . m <N n -> () : m <N n

    leqn_0_min : forall (n : natural) . z`0 <N= n

    leqn_succn_0_not : forall (n : natural) . succn n <N= z`0 -> void

    leqn_succn_succn : forall (m n : natural) . m <N= n -> succn m <N= succn n

    leqn_succn_invert : forall (m n : natural) . succn m <N= succn n -> m <N= n

    leqn_succn : forall (n : natural) . n <N= succn n

    leqn_refl : forall (n : natural) . n <N= n

    leqn_refl_eq : forall (m n : natural) . m = n : natural -> m <N= n

    leqn_trans : forall (m n p : natural) . m <N= n -> n <N= p -> m <N= p

    leqn_antisymm : forall (m n : natural) . m <N= n -> n <N= m -> m = n : natural

    leqn_implication : forall (m m' n n' : natural) . m' <N= m -> n <N= n' -> m <N= n -> m' <N= n'

    ltn_impl_leqn : forall (m n : natural) . m <N n -> m <N= n

    ltn_succn_succn : forall (m n : natural) . m <N n -> succn m <N succn n

    ltn_succn_invert : forall (m n : natural) . succn m <N succn n -> m <N n

    ltn_succn : forall (n : natural) . n <N succn n

    ltn_irrefl : forall (n : natural) . n <N n -> void

    ltn_trans : forall (m n p : natural) . m <N n -> n <N p -> m <N p

    leqn_ltn_trans : forall (m n p : natural) . m <N= n -> n <N p -> m <N p

    ltn_leqn_trans : forall (m n p : natural) . m <N n -> n <N= p -> m <N p

    ltn_0_succn : forall (n : natural) . z`0 <N succn n

    ltn_0_not : forall (n : natural) . n <N z`0 -> void

    not_leqn : forall (m n : natural) . not (m <N= n) <-> n <N m

    not_ltn : forall (m n : natural) . not (m <N n) <-> n <N= m

    leqn_iff_ltn_succn : forall (m n : natural) . m <N= n <-> m <N succn n

    ltn_from_leqn_neq : forall (m n : natural) . m <N= n -> not (m = n : natural) -> m <N n

Strong induction for natural numbers:

    ltn_well_founded : forall (n : natural) . Acc.Acc natural ltn n


### Addition

    (* +N *)
    plusn : natural -> natural -> natural

       plusn_zeron : forall (n : natural) . z`0 +N n = n : natural

       plusn_succn : forall (m n : natural) . succn m +N n = succn (m +N n) : natural

    (* an alias for plusz_zeron *)
    plusn_0_l : forall (n : natural) . z`0 +N n = n : natural

    plusn_0_r : forall (n : natural) . n +N z`0 = n : natural

    plusn_assoc : forall (m n p : natural) . m +N n +N p = m +N (n +N p) : natural

    plusn_shift_r : forall (m n : natural) . m +N succn n = succn (m +N n) : natural

    plusn_commute : forall (m n : natural) . m +N n = n +N m : natural

    plusn_leqn_l : forall (m n : natural) . m <N= m +N n

    plusn_leqn_r : forall (m n : natural) . n <N= m +N n

    plusn_leqn : forall (m m' n n' : natural) . m <N= m' -> n <N= n' -> m +N n <N= m' +N n'

    plusn_cancel_leqn_l : forall (m n p : natural) . p +N m <N= p +N n -> m <N= n

    plusn_cancel_leqn_r : forall (m n p : natural) . m +N p <N= n +N p -> m <N= n

    plusn_cancel_leqn_leqn_l : forall (m m' n n' : natural) .
                                  m +N n <N= m' +N n' -> m' <N= m -> n <N= n'

    plusn_cancel_leqn_leqn_r : forall (m m' n n' : natural) .
                                  m +N n <N= m' +N n' -> n' <N= n -> m <N= m'

    plusn_ltn_r : forall (m n : natural) . z`0 <N n -> m <N m +N n

    plusn_cancel_l : forall (m n p : natural) . p +N m = p +N n : natural -> m = n : natural

    plusn_cancel_l_eq : forall (m n p q : natural) .
                           m +N n = p +N q : natural -> m = p : natural -> n = q : natural

    plusn_cancel_r : forall (m n p : natural) . m +N p = n +N p : natural -> m = n : natural

    plusn_cancel_r_eq : forall (m n p q : natural) .
                           m +N n = p +N q : natural -> n = q : natural -> m = p : natural

    plusn_compat : forall (m m' n n' : natural) .
                      m = m' : natural -> n = n' : natural -> m +N n = m' +N n' : natural


### Subtraction

    predn : natural -> natural
          = fn n . n -N z`1

       predn_zeron : predn z`0 = z`0 : natural

       predn_succn : forall (n : natural) . predn (succn n) = n : natural

    (* -N *)
    minusn : natural -> natural -> natural

       minusn_zeron : forall (n : natural) . n -N z`0 = n : natural

       minusn_succn_r : forall (m n : natural) . m -N succn n = predn m -N n : natural

    succn_predn : forall (n : natural) . z`0 <N n -> succn (predn n) = n : natural

    plusn_minusn_cancel_l : forall (m n : natural) . m +N n -N m = n : natural

    plusn_minusn_cancel_r : forall (m n : natural) . m +N n -N n = m : natural

    minusn_swap : forall (m n p : natural) . m -N n -N p = m -N p -N n : natural

    minusn_plusn_cancel : forall (m n : natural) . n <N= m -> m -N n +N n = m : natural

    minusn_0_l : forall (n : natural) . z`0 -N n = z`0 : natural

    (* an alias for minusn_zeron *)
    minusn_0_r : forall (n : natural) . n -N z`0 = n : natural

    minusn_proper : forall (m n : natural) . m <N= n -> m -N n = z`0 : natural

    minusn_assoc : forall (m n p : natural) . m -N n -N p = m -N (n +N p) : natural

    minusn_succn : forall (m n : natural) . succn m -N succn n = m -N n : natural

    predn_leqn : forall (n : natural) . predn n <N= n

    minusn_leqn_l : forall (m n : natural) . m -N n <N= m

    minusn_leqn : forall (m m' n n' : natural) . m <N= m' -> n' <N= n -> m -N n <N= m' -N n'

    minusn_self : forall (n : natural) . n -N n = z`0 : natural

    minusn_succn_l_leqn : forall (m n : natural) . succn m -N n <N= succn (m -N n)

    minusn_succn_l_eq : forall (m n : natural) .
                           n <N= m -> succn m -N n = succn (m -N n) : natural

    plusn_minusn_swap : forall (m n p : natural) . p <N= m -> m +N n -N p = m -N p +N n : natural

    plusn_minusn_assoc : forall (m n p : natural) .
                            p <N= n -> m +N n -N p = m +N (n -N p) : natural

    plusn_minusn_assoc_swap : forall (m n p : natural) .
                                 n <N= p -> m +N n -N p = m -N (p -N n) : natural

    minusn_plusn_assoc : forall (m n p : natural) .
                            p <N= n -> n <N= m -> m -N n +N p = m -N (n -N p) : natural

    minusn_compat : forall (m m' n n' : natural) .
                       m = m' : natural -> n = n' : natural -> m -N n = m' -N n' : natural


### Multiplication

    (* *N *)
    timesn : natural -> natural -> natural

       timesn_zeron : forall (n : natural) . z`0 *N n = z`0 : natural
    
       timesn_succn : forall (m n : natural) . succn m *N n = n +N m *N n : natural

    (* an alias for timesn_zeron *)
    timesn_0_l : forall (n : natural) . z`0 *N n = z`0 : natural

    timesn_0_r : forall (n : natural) . n *N z`0 = z`0 : natural

    timesn_1_l : forall (n : natural) . z`1 *N n = n : natural

    timesn_1_r : forall (n : natural) . n *N z`1 = n : natural

    timesn_commute : forall (m n : natural) . m *N n = n *N m : natural

    timesn_assoc : forall (m n p : natural) . m *N n *N p = m *N (n *N p) : natural

    timesn_dist_succn_r : forall (m n : natural) . m *N succn n = m +N m *N n : natural

    timesn_dist_plusn_l : forall (m n p : natural) . (m +N n) *N p = m *N p +N n *N p : natural

    timesn_dist_plusn_r : forall (m n p : natural) . m *N (n +N p) = m *N n +N m *N p : natural

    timesn_leqn : forall (m m' n n' : natural) . m <N= m' -> n <N= n' -> m *N n <N= m' *N n'

    timesn_dist_predn_l : forall (m n : natural) . predn m *N n = m *N n -N n : natural

    timesn_dist_predn_r : forall (m n : natural) . m *N predn n = m *N n -N m : natural

    timesn_dist_minusn_l : forall (m n p : natural) . (m -N n) *N p = m *N p -N n *N p : natural

    timesn_dist_minusn_r : forall (m n p : natural) . m *N (n -N p) = m *N n -N m *N p : natural

    natural_integral_domain : forall (m n : natural) .
                                 m *N n = z`0 : natural -> m = z`0 : natural % n = z`0 : natural

    timesn_compat : forall (m m' n n' : natural) .
                       m = m' : natural -> n = n' : natural -> m *N n = m' *N n' : natural


### Minimum

    minn : natural -> natural -> natural

    minn_commute : forall (m n : natural) . minn m n = minn n m : natural

    minn_assoc : forall (m n p : natural) . minn (minn m n) p = minn m (minn n p) : natural

    minn_ann_l : forall (n : natural) . minn z`0 n = z`0 : natural

    minn_ann_r : forall (n : natural) . minn n z`0 = z`0 : natural

    minn_succn : forall (m n : natural) . minn (succn m) (succn n) = succn (minn m n) : natural

    minn_leqn_l : forall (m n : natural) . minn m n <N= m

    minn_leqn_r : forall (m n : natural) . minn m n <N= n

    minn_glb : forall (m n p : natural) . p <N= m -> p <N= n -> p <N= minn m n

    minn_leqn : forall (m m' n n' : natural) . m <N= m' -> n <N= n' -> minn m n <N= minn m' n'

    minn_eq_l : forall (m n : natural) . m <N= n -> minn m n = m : natural

    minn_eq_r : forall (m n : natural) . n <N= m -> minn m n = n : natural

    minn_idem : forall (n : natural) . minn n n = n : natural

    plusn_dist_minn_l : forall (m n p : natural) .
                           minn m n +N p = minn (m +N p) (n +N p) : natural

    plusn_dist_minn_r : forall (m n p : natural) .
                           m +N minn n p = minn (m +N n) (m +N p) : natural


### Maximum

    maxn : natural -> natural -> natural

    maxn_commute : forall (m n : natural) . maxn m n = maxn n m : natural

    maxn_assoc : forall (m n p : natural) . maxn (maxn m n) p = maxn m (maxn n p) : natural

    maxn_id_l : forall (n : natural) . maxn z`0 n = n : natural

    maxn_id_r : forall (n : natural) . maxn n z`0 = n : natural

    maxn_succn : forall (m n : natural) . maxn (succn m) (succn n) = succn (maxn m n) : natural

    maxn_leqn_l : forall (m n : natural) . m <N= maxn m n

    maxn_leqn_r : forall (m n : natural) . n <N= maxn m n

    maxn_lub : forall (m n p : natural) . m <N= p -> n <N= p -> maxn m n <N= p

    maxn_leqn : forall (m m' n n' : natural) . m <N= m' -> n <N= n' -> maxn m n <N= maxn m' n'

    maxn_eq_l : forall (m n : natural) . n <N= m -> maxn m n = m : natural

    maxn_eq_r : forall (m n : natural) . m <N= n -> maxn m n = n : natural

    maxn_idem : forall (n : natural) . maxn n n = n : natural

    plusn_dist_maxn_l : forall (m n p : natural) .
                           maxn m n +N p = maxn (m +N p) (n +N p) : natural

    plusn_dist_maxn_r : forall (m n p : natural) .
                           m +N maxn n p = maxn (m +N n) (m +N p) : natural

    minn_dist_maxn_l : forall (m n p : natural) .
                          minn (maxn m n) p = maxn (minn m p) (minn n p) : natural

    minn_dist_maxn_r : forall (m n p : natural) .
                          minn m (maxn n p) = maxn (minn m n) (minn m p) : natural

    maxn_dist_minn_l : forall (m n p : natural) .
                          maxn (minn m n) p = minn (maxn m p) (maxn n p) : natural

    maxn_dist_minn_r : forall (m n p : natural) .
                          maxn m (minn n p) = minn (maxn m n) (maxn m p) : natural

    minn_maxn_same : forall (m n : natural) . minn m (maxn m n) = m : natural

    maxn_minn_same : forall (m n : natural) . maxn m (minn m n) = m : natural


### Effective comparisons

    (* =N? *)
    eqnb : natural -> natural -> bool

    (* <N=? *)
    leqnb : natural -> natural -> bool

    (* <N? *)
    ltnb : natural -> natural -> bool

    (* !N=? *)
    neqnb : natural -> natural -> bool
         = fn m n . Bool.notb (m =N? n)

    istrue_eqnb : forall (m n : natural) . Bool.istrue (m =N? n) <-> m = n : natural

    istrue_neqnb : forall (m n : natural) . Bool.istrue (m !N=? n) <-> m != n : natural

    istrue_leqnb : forall (m n : natural) . Bool.istrue (m <N=? n) <-> m <N= n

    istrue_ltnb : forall (m n : natural) . Bool.istrue (m <N? n) <-> m <N n

    notb_eqnb : forall (m n : natural) . Bool.notb (m =N? n) = m !N=? n : bool

    notb_neqnb : forall (m n : natural) . Bool.notb (m !N=? n) = m =N? n : bool

    notb_leqnb : forall (m n : natural) . Bool.notb (m <N=? n) = n <N? m : bool

    notb_ltnb : forall (m n : natural) . Bool.notb (m <N? n) = n <N=? m : bool


### Decidability

    eq_natural_decide : forall (m n : natural) . Decidable.decidable (m = n : natural)

    neq_natural_decide : forall (m n : natural) . Decidable.decidable (m != n : natural)

    leqn_decide : forall (m n : natural) . Decidable.decidable (m <N= n)

    ltn_decide : forall (m n : natural) . Decidable.decidable (m <N n)

    eq_natural_stable : forall (m n : natural) . Stable.stable (m = n : natural)

    neq_natural_stable : forall (m n : natural) . Stable.stable (m != n : natural)

    leqn_stable : forall (m n : natural) . Stable.stable (m <N= n)

    ltn_stable : forall (m n : natural) . Stable.stable (m <N n)

    leqn_iff_ltn_or_eq : forall (m n : natural) . m <N= n <-> m <N n % m = n : natural

    natural_trichotomy : forall (m n : natural) . m <N n % m = n : natural % n <N m

    natural_dichotomy : forall (m n : natural) . m <N= n % n <N m

    natural_dichotomy_weak : forall (m n : natural) . m <N= n % n <N= m

    natural_dichotomy_neq : forall (m n : natural) . m != n : natural -> m <N n % n <N m

    natural_cases : forall (n : natural) .
                       n = z`0 : natural % (exists (n' : natural) . n = succn n' : natural)


### Relation to `nat`

    nat_to_natural : nat -> natural

    natural_to_nat : natural -> nat

    nat_to_natural_inv : forall (n : nat) . natural_to_nat (nat_to_natural n) = n : nat

    natural_to_nat_inv : forall (n : natural) . nat_to_natural (natural_to_nat n) = n : natural

    nat_to_natural_mono : forall (m n : nat) . m <= n -> nat_to_natural m <N= nat_to_natural n

    natural_to_nat_mono : forall (m n : natural) . m <N= n -> natural_to_nat m <= natural_to_nat n

    nat_to_natural_mono_lt : forall (m n : nat) . m < n -> nat_to_natural m <N nat_to_natural n

    natural_to_nat_mono_lt : forall (m n : natural) .
                                m <N n -> natural_to_nat m < natural_to_nat n

    natural_eq_from_nat : forall (m n : natural) .
                             natural_to_nat m = natural_to_nat n : nat -> m = n : natural

    nat_eq_from_natural : forall (m n : nat) .
                             nat_to_natural m = nat_to_natural n : natural -> m = n : nat

    leqn_from_nat : forall (m n : natural) . natural_to_nat m <= natural_to_nat n -> m <N= n

    leq_from_natural : forall (m n : nat) . nat_to_natural m <N= nat_to_natural n -> m <= n

    ltn_from_nat : forall (m n : natural) . natural_to_nat m < natural_to_nat n -> m <N n

    lt_from_natural : forall (m n : nat) . nat_to_natural m <N nat_to_natural n -> m < n

    plusn_to_nat : forall (m n : natural) .
                      natural_to_nat (m +N n) = natural_to_nat m + natural_to_nat n : nat

    plus_to_natural : forall (m n : nat) .
                         nat_to_natural (m + n) = nat_to_natural m +N nat_to_natural n : natural

    minusn_to_nat : forall (m n : natural) .
                       natural_to_nat (m -N n) = natural_to_nat m - natural_to_nat n : nat

    minus_to_natural : forall (m n : nat) .
                          nat_to_natural (m - n) = nat_to_natural m -N nat_to_natural n : natural

    timesn_to_nat : forall (m n : natural) .
                       natural_to_nat (m *N n) = natural_to_nat m * natural_to_nat n : nat

    times_to_natural : forall (m n : nat) .
                          nat_to_natural (m * n) = nat_to_natural m *N nat_to_natural n : natural

    minn_to_nat : forall (m n : natural) .
                     natural_to_nat (minn m n)
                       = Nat.min (natural_to_nat m) (natural_to_nat n)
                       : nat

    min_to_natural : forall (m n : nat) .
                        nat_to_natural (Nat.min m n)
                          = minn (nat_to_natural m) (nat_to_natural n)
                          : natural

    maxn_to_nat : forall (m n : natural) .
                     natural_to_nat (maxn m n)
                       = Nat.max (natural_to_nat m) (natural_to_nat n)
                       : nat

    max_to_natural : forall (m n : nat) .
                        nat_to_natural (Nat.max m n)
                          = maxn (nat_to_natural m) (nat_to_natural n)
                          : natural

    eqnb_to_nat : forall (m n : natural) . m =N? n = natural_to_nat m =? natural_to_nat n : bool

    eqb_to_natural : forall (m n : nat) . m =? n = nat_to_natural m =N? nat_to_natural n : bool

    leqnb_to_nat : forall (m n : natural) .
                      m <N=? n = natural_to_nat m <=? natural_to_nat n : bool

    leqb_to_natural : forall (m n : nat) . m <=? n = nat_to_natural m <N=? nat_to_natural n : bool

    ltnb_to_nat : forall (m n : natural) . m <N? n = natural_to_nat m <? natural_to_nat n : bool

    ltb_to_natural : forall (m n : nat) . m <? n = nat_to_natural m <N? nat_to_natural n : bool

    neqnb_to_nat : forall (m n : natural) .
                      m !N=? n = natural_to_nat m !=? natural_to_nat n : bool

    neqb_to_natural : forall (m n : nat) . m !=? n = nat_to_natural m !N=? nat_to_natural n : bool


### Relation to `integer`

    natural_to_integer : natural -> integer

    integer_to_natural : integer -> natural

    natural_to_integer_inv : forall (n : natural) .
                                integer_to_natural (natural_to_integer n) = n : natural

    integer_to_natural_inv : forall (a : integer) .
                                z`0 <z= a
                                -> natural_to_integer (integer_to_natural a) = a : integer

    natural_to_integer_nonneg : forall (n : natural) . z`0 <z= natural_to_integer n

    natural_to_integer_mono : forall (m n : natural) .
                                 m <N= n -> natural_to_integer m <z= natural_to_integer n

    natural_to_integer_mono_lt : forall (m n : natural) .
                                    m <N n -> natural_to_integer m <z natural_to_integer n

    integer_to_natural_zero : integer_to_natural z`0 = z`0 : natural

    integer_to_natural_succ : forall (a : integer) .
                                 z`0 <z= a
                                 -> integer_to_natural (z`1 +z a)
                                      = succn (integer_to_natural a)
                                      : natural

    integer_to_natural_mono : forall (a b : integer) .
                                 a <z= b -> integer_to_natural a <N= integer_to_natural b

    integer_to_natural_mono_lt : forall (a b : integer) .
                                    z`0 <z= a
                                    -> a <z b
                                    -> integer_to_natural a <N integer_to_natural b

    integer_to_natural_nonpos : forall (a : integer) .
                                   a <z= z`0 -> integer_to_natural a = z`0 : natural

    integer_to_natural_neg : forall (a : integer) .
                                a <z z`0 -> integer_to_natural a = z`0 : natural

    plusn_to_integer : forall (m n : natural) .
                          natural_to_integer (m +N n)
                            = natural_to_integer m +z natural_to_integer n
                            : integer

    plusz_to_natural : forall (a b : integer) .
                          z`0 <z= a
                          -> z`0 <z= b
                          -> integer_to_natural (a +z b)
                               = integer_to_natural a +N integer_to_natural b
                               : natural

    succn_to_integer : forall (n : natural) .
                          natural_to_integer (succn n) = z`1 +z natural_to_integer n : integer

    predn_to_integer : forall (n : natural) .
                          z`0 <N n
                          -> natural_to_integer (predn n) = z`-1 +z natural_to_integer n : integer

    minusn_to_integer : forall (m n : natural) .
                           n <N= m
                           -> natural_to_integer (m -N n)
                                = natural_to_integer m -z natural_to_integer n
                                : integer

    minusz_to_natural : forall (a b : integer) .
                           z`0 <z= b
                           -> b <z= a
                           -> integer_to_natural (a -z b)
                                = integer_to_natural a -N integer_to_natural b
                                : natural

    timesn_to_integer : forall (m n : natural) .
                           natural_to_integer (m *N n)
                             = natural_to_integer m *z natural_to_integer n
                             : integer

    timesz_to_natural : forall (a b : integer) .
                           z`0 <z= a
                           -> z`0 <z= b
                           -> integer_to_natural (a *z b)
                                = integer_to_natural a *N integer_to_natural b
                                : natural

    minn_to_integer : forall (m n : natural) .
                         natural_to_integer (minn m n)
                           = Integer.minz (natural_to_integer m) (natural_to_integer n)
                           : integer

    maxn_to_integer : forall (m n : natural) .
                         natural_to_integer (maxn m n)
                           = Integer.maxz (natural_to_integer m) (natural_to_integer n)
                           : integer

    minz_to_natural : forall (a b : integer) .
                         integer_to_natural (Integer.minz a b)
                           = minn (integer_to_natural a) (integer_to_natural b)
                           : natural

    maxz_to_natural : forall (a b : integer) .
                         integer_to_natural (Integer.maxz a b)
                           = maxn (integer_to_natural a) (integer_to_natural b)
                           : natural

    eqnb_to_integer : forall (m n : natural) .
                         m =N? n = natural_to_integer m =z? natural_to_integer n : bool

    eqzb_to_natural : forall (a b : integer) .
                         z`0 <z= a
                         -> z`0 <z= b
                         -> a =z? b = integer_to_natural a =N? integer_to_natural b : bool

    leqnb_to_integer : forall (m n : natural) .
                          m <N=? n = natural_to_integer m <z=? natural_to_integer n : bool

    leqzb_to_natural : forall (a b : integer) .
                          z`0 <z= a
                          -> z`0 <z= b
                          -> a <z=? b = integer_to_natural a <N=? integer_to_natural b : bool

    ltnb_to_integer : forall (m n : natural) .
                         m <N? n = natural_to_integer m <z? natural_to_integer n : bool

    ltzb_to_natural : forall (a b : integer) .
                         z`0 <z= a
                         -> z`0 <z= b
                         -> a <z? b = integer_to_natural a <N? integer_to_natural b : bool

    neqnb_to_integer : forall (m n : natural) .
                          m !N=? n = natural_to_integer m !z=? natural_to_integer n : bool

    neqzb_to_natural : forall (a b : integer) .
                          z`0 <z= a
                          -> z`0 <z= b
                          -> a !z=? b = integer_to_natural a !N=? integer_to_natural b : bool

    natural_to_nat_to_integer : forall (n : natural) .
                                   Integer.nat_to_integer (natural_to_nat n)
                                     = natural_to_integer n
                                     : integer

    integer_to_nat_to_natural : forall (a : integer) .
                                   nat_to_natural (Integer.integer_to_nat a)
                                     = integer_to_natural a
                                     : natural

    nat_to_natural_to_integer : forall (n : nat) .
                                   natural_to_integer (nat_to_natural n)
                                     = Integer.nat_to_integer n
                                     : integer

    integer_to_natural_to_nat : forall (a : integer) .
                                   natural_to_nat (integer_to_natural a)
                                     = Integer.integer_to_nat a
                                     : nat

    nat_to_integer_to_natural : forall (n : nat) .
                                   integer_to_natural (Integer.nat_to_integer n)
                                     = nat_to_natural n
                                     : natural

    natural_to_integer_to_nat : forall (n : natural) .
                                   Integer.integer_to_nat (natural_to_integer n)
                                     = natural_to_nat n
                                     : nat
