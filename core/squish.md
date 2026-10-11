open:Squish
open:Real
overload:real
# `Squish`

The squish type (`squish A`) is much like the squash type (`{ A }`) in
that it gives an attenuated version of the proposition, but squish is
stronger than squash.  While squash tells you that `A` is true, but
provides no ability to compute it; squish does give the ability to
compute it.  However, squish blurs out `A`'s equality entirely, so
that one cannot determine which element of `A` one has obtained.

    squish : type:squish
           = def:squish

    squish_ext : type:squish_ext

    squish_impl_squash : type:squish_impl_squash

When a type has a trivial equality already, a squish can be eliminated:

    squish_elim : type:squish_elim

Since a squish term actually computes an element of the underlying
type, it cannot use hidden variables (which are unavailable to
computation).  This rules out the usual idiom for dealing with
squashes.  Instead, squish is best managed as a monad:

    squish_ret : type:squish_ret

    squish_bind : type:squish_bind

    squish_bind_id_left : type:squish_bind_id_left

    squish_bind_id_right : type:squish_bind_id_right

    squish_bind_assoc : type:squish_bind_assoc

Squishes arise when operation on a quotient type depends on the which
representative of the equivalence class is used.  For example, the
lemma `Real.plusr_positive_invert` states that if the sum of two
reals is positive, at least one of them must be positive.  However,
both of them might be positive, and if so, which one is chosen depends
on the representation used for the two inputs.  Consequently, we
cannot return a deterministic inhabitant of the disjunction.

    (* using real overloading *)
    Real.plusr_positive_invert : type:Real.plusr_positive_invert

A squish containing a universal quantifier can be commuted to within
the quantifier.  The opposite direction depends on the properties of
the domain and codomain.  There is more information in the [`Quotient`
library](quotient.html).

    squish_forall_commute : type:squish_forall_commute

    squish_forall_nat : type:squish_forall_nat
