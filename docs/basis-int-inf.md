# IntInf

    signature INT_INF =
       sig
    
          include INTEGER
    
          val pow : int -> Int.int -> int
          val log2 : int -> Int.int
          val orb : int -> int -> int
          val xorb : int -> int -> int
          val andb : int -> int -> int
          val notb : int -> int
          val shl : int -> Int.int -> int
          val shr : int -> Int.int -> int
    
       end
    
    structure IntInf : INT_INF
