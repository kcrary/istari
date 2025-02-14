# `Nat`

The `nat` type is primitive, but aliased in the `Nat` module:

    nat : U 0
    zero : nat
    succ : nat -> nat

The iterator for natural numbers:

    nat_iter : intersect (i : level) .
                  forall (P : nat -> U i) .
                    P 0 -> (forall (n : nat) . P n -> P (succ n)) -> forall (n : nat) . P n

    nat_iter _ z _ (zero) --> z
    nat_iter a z s (succ n) --> s n (nat_iter a z s n)

A simpler case-analysis operation:

    nat_case : intersect (i : level) (a : U i) . nat -> a -> (nat -> a) -> a

    nat_case (zero) z s --> z
    nat_case (succ n) z s --> s n


### Equality

    eq_0_succ_not : forall (n : nat) . 0 = succ n : nat -> void

    eq_succ_0_not : forall (n : nat) . succ n = 0 : nat -> void

    succ_inj : forall (m n : nat) . succ m = succ n : nat -> m = n : nat


### Inequalities

    leq : nat -> nat -> U 0

    lt : nat -> nat -> U 0

    leq_inhabitant : forall (m n : nat) . m <= n -> () : m <= n

    lt_inhabitant : forall (m n : nat) . m < n -> () : m < n

    leq_0_min : forall (n : nat) . 0 <= n

    leq_0_minimal : forall (n : nat) . n <= 0 -> n = 0 : nat

    leq_succ_0_not : forall (n : nat) . succ n <= 0 -> void

    leq_succ_succ : forall (m n : nat) . m <= n -> succ m <= succ n

    leq_succ_invert : forall (m n : nat) . succ m <= succ n -> m <= n

    leq_succ : forall (n : nat) . n <= succ n

    leq_refl : forall (n : nat) . n <= n

    leq_refl_eq : forall (m n : nat) . m = n : nat -> m <= n

    leq_trans : forall (m n p : nat) . m <= n -> n <= p -> m <= p

    leq_antisymm : forall (m n : nat) . m <= n -> n <= m -> m = n : nat

This one gives transitivity in the form needed for rewriting:

    leq_implication : forall (m m' n n' : nat) . m' <= m -> n <= n' -> m <= n -> m' <= n'

    lt_impl_leq : forall (m n : nat) . m < n -> m <= n

    lt_succ_succ : forall (m n : nat) . m < n -> succ m < succ n

    lt_succ_invert : forall (m n : nat) . succ m < succ n -> m < n

    lt_succ : forall (n : nat) . n < succ n

    lt_irrefl : forall (n : nat) . n < n -> void

    lt_trans : forall (m n p : nat) . m < n -> n < p -> m < p

    leq_lt_trans : forall (m n p : nat) . m <= n -> n < p -> m < p

    lt_leq_trans : forall (m n p : nat) . m < n -> n <= p -> m < p

    lt_0_succ : forall (n : nat) . 0 < succ n

    lt_0_not : forall (n : nat) . n < 0 -> void

    not_leq : forall (m n : nat) . not (m <= n) <-> n < m

    not_lt : forall (m n : nat) . not (m < n) <-> n <= m

    leq_iff_lt_succ : forall (m n : nat) . m <= n <-> m < succ n

    lt_from_leq_neq : forall (m n : nat) . m <= n -> not (m = n : nat) -> m < n

Strong induction for natural numbers:

    lt_well_founded : forall (n : nat) . Acc.Acc nat lt n


### Addition

    plus : nat -> nat -> nat

    plus (zero) n --> n
    plus (succ m) n --> succ (plus m n)

    plus_0_l : forall (n : nat) . 0 + n = n : nat

    plus_0_r : forall (n : nat) . n + 0 = n : nat

    plus_assoc : forall (m n p : nat) . m + n + p = m + (n + p) : nat

    plus_shift_r : forall (m n : nat) . m + succ n = succ (m + n) : nat

    plus_commute : forall (m n : nat) . m + n = n + m : nat

    plus_leq_l : forall (m n : nat) . m <= m + n

    plus_leq_r : forall (m n : nat) . n <= m + n

    plus_leq : forall (m m' n n' : nat) . m <= m' -> n <= n' -> m + n <= m' + n'

    plus_cancel_leq_l : forall (m n p : nat) . p + m <= p + n -> m <= n

    plus_cancel_leq_r : forall (m n p : nat) . m + p <= n + p -> m <= n

    plus_cancel_leq_leq_l : forall (m m' n n' : nat) . m + n <= m' + n' -> m' <= m -> n <= n'

    plus_cancel_leq_leq_r : forall (m m' n n' : nat) . m + n <= m' + n' -> n' <= n -> m <= m'

    plus_lt_r : forall (m n : nat) . 0 < n -> m < m + n

    plus_cancel_l : forall (m n p : nat) . p + m = p + n : nat -> m = n : nat

    plus_cancel_l_eq : forall (m n p q : nat) . m + n = p + q : nat -> m = p : nat -> n = q : nat

    plus_cancel_r : forall (m n p : nat) . m + p = n + p : nat -> m = n : nat

    plus_cancel_r_eq : forall (m n p q : nat) . m + n = p + q : nat -> n = q : nat -> m = p : nat

    plus_compat : forall (m m' n n' : nat) . m = m' : nat -> n = n' : nat -> m + n = m' + n' : nat


### Subtraction

    pred : nat -> nat

    pred (zero) --> zero
    pred (succ n) --> n

    minus : nat -> nat -> nat

    minus m (zero) --> m
    minus m (succ n) --> minus (pred m) n

    plus_minus_cancel_l : forall (m n : nat) . m + n - m = n : nat

    plus_minus_cancel_r : forall (m n : nat) . m + n - n = m : nat

    minus_swap : forall (m n p : nat) . m - n - p = m - p - n : nat

    minus_plus_cancel : forall (m n : nat) . n <= m -> m - n + n = m : nat

    minus_0_l : forall (n : nat) . 0 - n = 0 : nat

    minus_0_r : forall (n : nat) . n - 0 = n : nat

    minus_proper : forall (m n : nat) . m <= n -> m - n = 0 : nat

    minus_assoc : forall (m n p : nat) . m - n - p = m - (n + p) : nat

    minus_succ : forall (m n : nat) . succ m - succ n = m - n : nat

    pred_leq : forall (n : nat) . pred n <= n

    succ_pred : forall (n : nat) . 0 < n -> succ (pred n) = n : nat

    minus_leq_l : forall (m n : nat) . m - n <= m

    minus_leq : forall (m m' n n' : nat) . m <= m' -> n' <= n -> m - n <= m' - n'

    minus_self : forall (n : nat) . n - n = 0 : nat

    minus_succ_l_leq : forall (m n : nat) . succ m - n <= succ (m - n)

    minus_succ_l_eq : forall (m n : nat) . n <= m -> succ m - n = succ (m - n) : nat

    plus_minus_swap : forall (m n p : nat) . p <= m -> m + n - p = m - p + n : nat

    plus_minus_assoc : forall (m n p : nat) . p <= n -> m + n - p = m + (n - p) : nat

    plus_minus_assoc_swap : forall (m n p : nat) . n <= p -> m + n - p = m - (p - n) : nat

    minus_plus_assoc : forall (m n p : nat) . p <= n -> n <= m -> m - n + p = m - (n - p) : nat

    minus_compat : forall (m m' n n' : nat) .
                      m = m' : nat -> n = n' : nat -> m - n = m' - n' : nat


### Multiplication

    times : nat -> nat -> nat

    times (zero) _ --> zero ;
    times (succ m) n --> plus n (times m n) ;

    times_0_l : forall (n : nat) . 0 * n = 0 : nat

    times_0_r : forall (n : nat) . n * 0 = 0 : nat

    times_1_l : forall (n : nat) . 1 * n = n : nat

    times_1_r : forall (n : nat) . n * 1 = n : nat

    times_commute : forall (m n : nat) . m * n = n * m : nat

    times_assoc : forall (m n p : nat) . m * n * p = m * (n * p) : nat

    times_dist_succ_r : forall (m n : nat) . m * succ n = m + m * n : nat

    times_dist_plus_l : forall (m n p : nat) . (m + n) * p = m * p + n * p : nat

    times_dist_plus_r : forall (m n p : nat) . m * (n + p) = m * n + m * p : nat

    times_leq : forall (m m' n n' : nat) . m <= m' -> n <= n' -> m * n <= m' * n'

    times_dist_pred_l : forall (m n : nat) . pred m * n = m * n - n : nat

    times_dist_pred_r : forall (m n : nat) . m * pred n = m * n - m : nat

    times_dist_minus_l : forall (m n p : nat) . (m - n) * p = m * p - n * p : nat

    times_dist_minus_r : forall (m n p : nat) . m * (n - p) = m * n - m * p : nat

    nat_integral_domain : forall (m n : nat) . m * n = 0 : nat -> m = 0 : nat % n = 0 : nat

    times_compat : forall (m m' n n' : nat) .
                      m = m' : nat -> n = n' : nat -> m * n = m' * n' : nat


### Minimum

    min : nat -> nat -> nat

    min_commute : forall (m n : nat) . min m n = min n m : nat

    min_assoc : forall (m n p : nat) . min (min m n) p = min m (min n p) : nat

    min_ann_l : forall (n : nat) . min 0 n = 0 : nat

    min_ann_r : forall (n : nat) . min n 0 = 0 : nat

    min_succ : forall (m n : nat) . min (succ m) (succ n) = succ (min m n) : nat

    min_leq_l : forall (m n : nat) . min m n <= m

    min_leq_r : forall (m n : nat) . min m n <= n

    min_glb : forall (m n p : nat) . p <= m -> p <= n -> p <= min m n

    min_leq : forall (m m' n n' : nat) . m <= m' -> n <= n' -> min m n <= min m' n'

    min_eq_l : forall (m n : nat) . m <= n -> min m n = m : nat

    min_eq_r : forall (m n : nat) . n <= m -> min m n = n : nat

    min_idem : forall (n : nat) . min n n = n : nat

    plus_dist_min_l : forall (m n p : nat) . min m n + p = min (m + p) (n + p) : nat

    plus_dist_min_r : forall (m n p : nat) . m + min n p = min (m + n) (m + p) : nat

    minus_dist_min_l : forall (m n p : nat) . min m n - p = min (m - p) (n - p) : nat


### Maximum

    max : nat -> nat -> nat

    max_commute : forall (m n : nat) . max m n = max n m : nat

    max_assoc : forall (m n p : nat) . max (max m n) p = max m (max n p) : nat

    max_id_l : forall (n : nat) . max 0 n = n : nat

    max_id_r : forall (n : nat) . max n 0 = n : nat

    max_succ : forall (m n : nat) . max (succ m) (succ n) = succ (max m n) : nat

    max_leq_l : forall (m n : nat) . m <= max m n

    max_leq_r : forall (m n : nat) . n <= max m n

    max_lub : forall (m n p : nat) . m <= p -> n <= p -> max m n <= p

    max_leq : forall (m m' n n' : nat) . m <= m' -> n <= n' -> max m n <= max m' n'

    max_eq_l : forall (m n : nat) . n <= m -> max m n = m : nat

    max_eq_r : forall (m n : nat) . m <= n -> max m n = n : nat

    max_idem : forall (n : nat) . max n n = n : nat

    plus_dist_max_l : forall (m n p : nat) . max m n + p = max (m + p) (n + p) : nat

    plus_dist_max_r : forall (m n p : nat) . m + max n p = max (m + n) (m + p) : nat

    minus_dist_max_l : forall (m n p : nat) . max m n - p = max (m - p) (n - p) : nat

    minus_dist_max_r : forall (m n p : nat) . m - max n p = min (m - n) (m - p) : nat

    minus_dist_min_r : forall (m n p : nat) . m - min n p = max (m - n) (m - p) : nat

    min_dist_max_l : forall (m n p : nat) . min (max m n) p = max (min m p) (min n p) : nat

    min_dist_max_r : forall (m n p : nat) . min m (max n p) = max (min m n) (min m p) : nat

    max_dist_min_l : forall (m n p : nat) . max (min m n) p = min (max m p) (max n p) : nat

    max_dist_min_r : forall (m n p : nat) . max m (min n p) = min (max m n) (max m p) : nat

    min_max_same : forall (m n : nat) . min m (max m n) = m : nat

    max_min_same : forall (m n : nat) . max m (min m n) = m : nat


### Effective comparisons

    (* =? *)
    eqb : nat -> nat -> bool

    eqb (zero) (zero) --> true
    eqb (zero) (succ _) --> false
    eqb (succ _) (zero) --> false
    eqb (succ m) (succ n) --> eqb m n

    (* <=? *)
    leqb : nat -> nat -> bool

    leqb (zero) _ --> true
    leqb (succ _) (zero) --> false
    leqb (succ m) (succ n) --> leqb m n

    (* <? *)
    ltb : nat -> nat -> bool
        = fn m n . succ m <=? n

    ltb _ (zero) --> false
    ltb m (succ n) --> leqb m n

    (* !=? *)
    neqb : nat -> nat -> bool
         = fn m n . Bool.notb (m =? n)

    neqb (zero) (zero) --> false
    neqb (zero) (succ _) --> true
    neqb (succ _) (zero) --> true
    neqb (succ m) (succ n) --> neqb m n

    istrue_eqb : forall (m n : nat) . Bool.istrue (m =? n) <-> m = n : nat

    istrue_neqb : forall (m n : nat) . Bool.istrue (m !=? n) <-> m != n : nat

    istrue_leqb : forall (m n : nat) . Bool.istrue (m <=? n) <-> m <= n

    istrue_ltb : forall (m n : nat) . Bool.istrue (m <? n) <-> m < n

    notb_eqb : forall (m n : nat) . Bool.notb (m =? n) = m !=? n : bool

    notb_neqb : forall (m n : nat) . Bool.notb (m !=? n) = m =? n : bool

    notb_leqb : forall (m n : nat) . Bool.notb (m <=? n) = n <? m : bool

    notb_ltb : forall (m n : nat) . Bool.notb (m <? n) = n <=? m : bool


### Decidability

    eq_nat_decide : forall (m n : nat) . Decidable.decidable (m = n : nat)

    neq_nat_decide : forall (m n : nat) . Decidable.decidable (m != n : nat)

    leq_decide : forall (m n : nat) . Decidable.decidable (m <= n)

    lt_decide : forall (m n : nat) . Decidable.decidable (m < n)

    eq_nat_stable : forall (m n : nat) . Stable.stable (m = n : nat)

    neq_nat_stable : forall (m n : nat) . Stable.stable (m != n : nat)

    leq_stable : forall (m n : nat) . Stable.stable (m <= n)

    lt_stable : forall (m n : nat) . Stable.stable (m < n)

    leq_iff_lt_or_eq : forall (m n : nat) . m <= n <-> m < n % m = n : nat

    nat_trichotomy : forall (m n : nat) . m < n % m = n : nat % n < m

    nat_dichotomy : forall (m n : nat) . m <= n % n < m

    nat_dichotomy_weak : forall (m n : nat) . m <= n % n <= m

    nat_dichotomy_neq : forall (m n : nat) . m != n : nat -> m < n % n < m
