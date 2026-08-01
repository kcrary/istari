open:Squish
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
