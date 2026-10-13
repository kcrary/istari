# `Squish`

The squish type (`squish A`) is much like the squash type (`{ A }`) in
that it gives an attenuated version of the proposition, but squish is
stronger than squash.  While squash tells you that `A` is true, but
provides no ability to compute it; squish does give the ability to
compute it.  However, squish blurs out `A`'s equality entirely, so
that one cannot determine which element of `A` one has obtained.

    squish : intersect (i : level) . U i -> U i
           = fn A . quotient (x y : A) . unit

    squish_ext : forall (i : level) (A : U i) (x y : squish A) . x = y : squish A

    squish_impl_squash : forall (i : level) (A : U i) . squish A -> { A }

When a type has a trivial equality already, a squish can be eliminated:

    squish_elim : intersect (i : level) (A : U i) .
                     (forall (x y : A) . x = y : A) -g> squish A -> A

Since a squish term actually computes an element of the underlying
type, it cannot use hidden variables (which are unavailable to
computation).  This rules out the usual idiom for dealing with
squashes.  Instead, squish is best managed as a monad:

    squish_ret : intersect (i : level) (A : U i) . A -> squish A

    squish_bind : intersect (i : level) (A B : U i) . squish A -> (A -> squish B) -> squish B

    squish_bind_id_left : forall (i : level) (A B : U i) (x : A) (f : A -> squish B) .
                             squish_bind (squish_ret x) f = f x : squish B

    squish_bind_id_right : forall (i : level) (A : U i) (m : squish A) .
                              squish_bind m squish_ret = m : squish A

    squish_bind_assoc : forall
                           (i : level)
                           (A B C : U i)
                           (m : squish A)
                           (f : A -> squish B)
                           (g : B -> squish C) .
                           squish_bind (squish_bind m f) g
                             = squish_bind m (fn x . squish_bind (f x) g)
                             : squish C

Squishes arise when operation on a quotient type depends on the which
representative of the equivalence class is used.  For example, the
lemma `Real.plusr_positive_invert` states that if the sum of two
reals is positive, at least one of them must be positive.  However,
both of them might be positive, and if so, which one is chosen depends
on the representation used for the two inputs.  Consequently, we
cannot return a deterministic inhabitant of the disjunction.

    (* using real overloading *)
    Real.plusr_positive_invert : forall (x y : real) . 0 < x + y -> squish (0 < x % 0 < y)

A squish containing a universal quantifier can be commuted to within
the quantifier.  The opposite direction depends on the properties of
the domain and codomain.  There is more information in the [`Quotient`
library](quotient.html).

    squish_forall_commute : forall (i : level) (P : nat -> U i) .
                               squish (forall (x : nat) . P x) -> forall (x : nat) . squish (P x)

    squish_forall_nat : forall (i : level) (P : nat -> U i) .
                           (forall (x : nat) . Quotient.symmetrical (P x))
                           -> (forall (x : nat) . squish (P x))
                           -> squish (forall (x : nat) . P x)

    squish_symmetrical : forall (i : level) (A : U i) .
                            Quotient.symmetrical A -> Quotient.symmetrical (squish A)
