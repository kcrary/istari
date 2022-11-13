# Int

    signature INTEGER =
       sig

          type int
    
          val minInt : int option
          val maxInt : int option
    
          val (~) : int -> int
          val (+) : int -> int -> int
          val (-) : int -> int -> int
          val (*) : int -> int -> int
          val div : int -> int -> int
          val rem : int -> int -> int
          val min : int -> int -> int
          val max : int -> int -> int
          val abs : int -> int
    
          val (=) : int -> int -> bool
          val (<>) : int -> int -> bool
          val (<) : int -> int -> bool
          val (>) : int -> int -> bool
          val (<=) : int -> int -> bool
          val (>=) : int -> int -> bool
          val compare : int -> int -> order
    
          val toString : int -> string
          val toInt : int -> Int.int
          val fromInt : Int.int -> int

       end
    
    structure Int : INTEGER where type int = Pervasive.int

