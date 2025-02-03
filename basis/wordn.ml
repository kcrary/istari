
module type WORD =
   sig

      type word
      
      val wordSize : int
      
      val toLargeWord : word -> Word64.word
      val toLargeWordX : word -> Word64.word
      val fromLargeWord : Word64.word -> word
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
      
   end


module WordN (Size : sig val n : int end) () : WORD =
   struct

      let wordSize = Size.n

      let () = assert (wordSize < Sys.int_size)

      let mask = Int.shift_left 1 wordSize - 1
      let antimask = Int.lognot mask
      let minimum = Int.shift_left 1 (wordSize - 1)

      type nonrec word = int
      (* invariant: 0 <= w < 2^wordSize *)
      
      let toLargeWord = Word64.fromInt
      
      let toLargeWordX x =
         if x >= minimum then
            Word64.fromInt (Int.logor x antimask)
         else
            Word64.fromInt x
      
      let fromLargeWord x = Int.logand (Word64.toInt x) mask
      
      let toInt x = x
      
      let toIntX x =
         if x >= minimum then
            Int.logor x antimask
         else
            x
      
      let fromInt x = Int.logand x mask

      let toLargeInt x = Z.of_int x

      let toLargeIntX x =
         if x >= minimum then
            Z.of_int (Int.logor x antimask)
         else
            Z.of_int x

      let fromLargeInt x =
         Z.to_int (Z.logand x (Z.of_int mask))

      let toInt64 = Int64.of_int
         
      
      let andb = Int.logand
      let orb = Int.logor
      let xorb = Int.logxor

      let shl x n = Int.logand (Int.shift_left x n) mask

      let shr = Int.shift_right_logical
      
      let notb x = Int.logand (Int.lognot x) mask
      
      let ashr x n =
         Int.logand (Int.shift_right (Int.logor x antimask) n) mask
      
      let add x y =
         Int.logand (x + y) mask
      
      let sub x y =
         Int.logand (x - y) mask
      
      let mul x y =
         Int.logand (x * y) mask

      let div = Int.div
      let rem = Int.rem
      
      let eq = Int.equal
      let neq x y = not (Int.equal x y)
      let lt = (<)
      let gt = (>)
      let leq = (<=)
      let geq = (>=)
      
      let compare x y =
         if x < y then
            Order.LESS
         else if x = y then
            Order.EQUAL
         else
            Order.GREATER
      
      let digits = "0123456789ABCDEF"
      
      let rec toStringMain x acc =
         if x = 0 then
            Stringbasis.implode acc
         else
            toStringMain (Int.shift_right_logical x 4) (String.get digits (Int.logand x 15) :: acc)
         
      let toString x = toStringMain x []
      
   end
