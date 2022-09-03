
(* Omits the type specification for string, so as to not use Word8Vector.
   Adds output operation.
*)

signature BYTESTRING =
   sig

      type string
      type byte = Word8.word
      type char = byte

      val maxSize : int
      val size : string -> int
      val sub : string * int -> byte
      val extract : string * int * int option -> string
      val substring : string * int * int -> string
      val isEmpty : string -> bool
      val ^ : string * string -> string
      val concat : string list -> string
      val null : string
      val str : byte -> string
      val implode : byte list -> string
      val explode : string -> byte list
      val map : (byte -> byte) -> string -> string
      val map2 : (byte * byte -> byte) -> string * string -> string
      val rev : string -> string
      val eq : string * string -> bool
      val compare : string * string -> order

      val fromString : String.string -> string
      val fromStringHex : String.string -> string option

      val toString : string -> String.string
      val toStringHex : string -> String.string
      val toStringHex' : String.string -> string -> String.string

      val output : BinIO.outstream -> string -> unit

   end
