# Bool

    signature BOOL =
       sig

          type bool
    
          val not : bool -> bool

       end

    structure Bool : BOOL where type bool = Pervasive.bool
