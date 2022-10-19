# Word

    signature WORD =
       sig
    
          type word
    
          val wordSize : int
    
          val toLargeWord : word -> LargeWord.word
          val toLargeWordX : word -> LargeWord.word
          val fromLargeWord : LargeWord.word -> word
          val toInt : word -> int
          val toIntX : word -> int
          val fromInt : int -> word
          val toLargeInt : word -> IntInf.int
          val toLargeIntX : word -> IntInf.int
          val fromLargeInt : IntInf.int -> word
    
          val andb : word -> word -> word
          val orb : word -> word -> word
          val xorb : word -> word -> word
          val notb : word -> word
          val shl : word -> int -> word
          val shr : word -> int -> word
          val ashr : word -> int -> word
    
          val (+) : word -> word -> word
          val (-) : word -> word -> word
          val (*) : word -> word -> word
          val div : word -> word -> word
          val rem : word -> word -> word
    
          val (=) : word -> word -> bool
          val (<>) : word -> word -> bool
          val (<) : word -> word -> bool
          val (>) : word -> word -> bool
          val (<=) : word -> word -> bool
          val (>=) : word -> word -> bool
          val compare : word -> word -> order
    
          val toString : word -> string
    
       end
    
    structure Word : WORD
    structure Word8 : WORD
    structure Word32 : WORD
    structure Word64 : WORD
    structure LargeWord : WORD where type word = Word64.word
