# `SmithParadox`

Can be loaded using `File.import "smith-paradox-load.iml";`

---

Smith's paradox [1] is a proof that there exist non-admissible types,
that is, types that cannot be used with 
[fixpoint induction](../type-theory.html#partial-types).

    inadmissible_type : exists (a : U 0) . not (admiss a)

One such type is the type of partial functions from `nat` to `unit`:

    { h : nat -> partial unit | not (forall x . halts (h x)) }

Let `T` be this type, and let `f` be the function:

    fn g x . if x =? 0 then () else g (x - 1)

Since `f` defers to its argument `g`, it preserves partiality. Thus
one can show that `f : partial T -> partial T`.  If `T` were
admissible, we could conclude by fixpoint induction that 
`fix f : partial T`.  However `fix f` clearly halts, so it would
follow that `fix f : T`.  That would mean `fix f` is a partial
function, but it is easy to show that `fix f` is actually total.

---

[1] Scott Fraser Smith. *Partial Objects in Type Theory*.
Ph.D. dissertation, Cornell University. 1989.
