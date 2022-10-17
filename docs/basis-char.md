# Char

    signature CHAR =
       sig
    
          type char
    
          val ord : char -> int
          val chr : int -> char
          val (=) : char -> char -> bool
          val (<>) : char -> char -> bool
          val (<) : char -> char -> bool
          val (<=) : char -> char -> bool
          val (>) : char -> char -> bool
          val (>=) : char -> char -> bool
          val compare : char -> char -> order
    
       end
    
    structure Char : CHAR where type char = Pervasive.char
