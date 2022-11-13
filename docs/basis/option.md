# Option

    signature OPTION =
       sig
    
          datatype 'a option = NONE | SOME of 'a
    
          val getOpt : 'a option -> 'a -> 'a
          val isSome : 'a option -> bool
          val valOf : 'a option -> 'a
          val join : 'a option option -> 'a option
          val map : ('a -> 'b) -> 'a option -> 'b option
          val mapPartial : ('a -> 'b option) -> 'a option -> 'b option
          val app : ('a -> unit) -> 'a option -> unit
    
       end
    
    structure Option : OPTION where type 'a option = 'a Pervasive.option

