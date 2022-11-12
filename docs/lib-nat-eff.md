# `NatEff` (effective comparisons for natural numbers)

    eqb : nat -> nat -> bool

    istrue_eqb : forall (m n : nat) . istrue (eqb m n) <-> m = n : nat

    leqb : nat -> nat -> bool

    istrue_leqb : forall (m n : nat) . istrue (leqb m n) <-> m <= n

    ltb : nat -> nat -> bool
        = fn m n . leqb (succ m) n

    istrue_ltb : forall (m n : nat) . istrue (ltb m n) <-> m < n
