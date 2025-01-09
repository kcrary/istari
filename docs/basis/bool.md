# Bool

    signature BOOL =
       sig

          type bool
    
          val not : bool -> bool
          val = : bool -> bool -> bool
          val xor : bool -> bool -> bool

       end

    structure Bool : BOOL where type bool = Pervasive.bool
