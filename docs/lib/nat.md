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

    natcase : intersect (i : level) (a : U i) . nat -> a -> (nat -> a) -> a

    natcase (zero) z s --> z
    natcase (succ n) z s --> s n


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

    lt_succ : forall (n : nat) . n < succ n

    lt_irrefl : forall (n : nat) . n < n -> void

    lt_trans : forall (m n p : nat) . m < n -> n < p -> m < p

    leq_lt_trans : forall (m n p : nat) . m <= n -> n < p -> m < p

    lt_leq_trans : forall (m n p : nat) . m < n -> n <= p -> m < p

    lt_0_succ : forall (n : nat) . 0 < succ n

    lt_succ_succ : forall (m n : nat) . m < n -> succ m < succ n

Strong induction for natural numbers:

    lt_well_founded : forall (n : nat) . Acc nat lt n


### Addition and Subtraction

    plus : nat -> nat -> nat

    plus (zero) n --> n
    plus (succ m) n --> succ (plus m n)

    minus : nat -> nat -> nat

    minus m (zero) --> m
    minus m (succ n) --> natcase m zero (fn m' . minus m' n)

    plus_0_l : forall (n : nat) . 0 + n = n : nat

    plus_0_r : forall (n : nat) . n + 0 = n : nat

    plus_assoc : forall (m n p : nat) . m + n + p = m + (n + p) : nat

    plus_shift_r : forall (m n : nat) . m + succ n = succ (m + n) : nat

    plus_commute : forall (m n : nat) . m + n = n + m : nat

    plus_leq_l : forall (m n : nat) . m <= m + n

    plus_leq_r : forall (m n : nat) . n <= m + n

    plus_leq : forall (m m' n n' : nat) . m <= m' -> n <= n' -> m + n <= m' + n'

    plus_cancel_leq_r : forall (m n p : nat) . m + p <= n + p -> m <= n

    plus_cancel_leq_l : forall (m n p : nat) . p + m <= p + n -> m <= n

    plus_cancel_leq_leq_l : forall (m m' n n' : nat) . m + n <= m' + n' -> m' <= m -> n <= n'

    plus_cancel_leq_leq_r : forall (m m' n n' : nat) . m + n <= m' + n' -> n' <= n -> m <= m'

    plus_lt_r : forall (m n : nat) . 0 < n -> m < m + n

    plus_minus_cancel_l : forall (m n : nat) . m + n - m = n : nat

    plus_minus_cancel_r : forall (m n : nat) . m + n - n = m : nat

    plus_cancel_l : forall (m n p : nat) . p + m = p + n : nat -> m = n : nat

    plus_cancel_r : forall (m n p : nat) . m + p = n + p : nat -> m = n : nat

    minus_plus_cancel : forall (m n : nat) . n <= m -> m - n + n = m : nat

    minus_0_l : forall (n : nat) . 0 - n = 0 : nat

    minus_0_r : forall (n : nat) . n - 0 = n : nat

    minus_proper : forall (m n : nat) . m <= n -> m - n = 0 : nat

    minus_assoc : forall (m n p : nat) . m - n - p = m - (n + p) : nat

    minus_succ : forall (m n : nat) . succ m - succ n = m - n : nat

    minus_leq_l : forall (m n : nat) . m - n <= m

    minus_leq : forall (m m' n n' : nat) . m <= m' -> n' <= n -> m - n <= m' - n'

    minus_self : forall (n : nat) . n - n = 0 : nat

    minus_succ_l_leq : forall (m n : nat) . succ m - n <= succ (m - n)

    minus_succ_l_eq : forall (m n : nat) . n <= m -> succ m - n = succ (m - n) : nat

    plus_compat : forall (m m' n n' : nat) . m = m' : nat -> n = n' : nat -> m + n = m' + n' : nat

    minus_compat : forall (m m' n n' : nat) .
                      m = m' : nat -> n = n' : nat -> m - n = m' - n' : nat


### Maximum

    max : nat -> nat -> nat

    max_id_l : forall (n : nat) . max 0 n = n : nat

    max_id_r : forall (n : nat) . max n 0 = n : nat

    max_succ : forall (m n : nat) . max (succ m) (succ n) = succ (max m n) : nat

    max_leq_l : forall (m n : nat) . m <= max m n

    max_leq_r : forall (m n : nat) . n <= max m n

    max_lub : forall (m n p : nat) . m <= p -> n <= p -> max m n <= p

    max_eq_l : forall (m n : nat) . n <= m -> max m n = m : nat

    max_eq_r : forall (m n : nat) . m <= n -> max m n = n : nat
