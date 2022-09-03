
type word

val wordSize : int

val toLargeWord : word -> word
val toLargeWordX : word -> word
val fromLargeWord : word -> word
val toInt : word -> int
val toIntX : word -> int
val fromInt : int -> word
val toLargeInt : word -> Z.t
val toLargeIntX : word -> Z.t
val fromLargeInt : Z.t -> word
val toInt64 : word -> Int64.t  (* not in basis *)

val andb : word -> word -> word
val orb : word -> word -> word
val xorb : word -> word -> word
val notb : word -> word
val shl : word -> int -> word
val shr : word -> int -> word
val ashr : word -> int -> word

val add : word -> word -> word
val sub : word -> word -> word
val mul : word -> word -> word
val div : word -> word -> word
val rem : word -> word -> word

val eq : word -> word -> bool
val neq : word -> word -> bool
val lt : word -> word -> bool
val gt : word -> word -> bool
val leq : word -> word -> bool
val geq : word -> word -> bool
val compare : word -> word -> Order.order

val toString : word -> string


