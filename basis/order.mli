
type order = LESS | EQUAL | GREATER

val intCompare : int -> int -> order
val intInfCompare : Z.t -> Z.t -> order
val stringCompare : string -> string -> order
val charCompare : char -> char -> order
