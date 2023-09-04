# Vector

    signature VECTOR =
       sig
    
          type 'a vector
    
          val fromList : 'a list -> 'a vector
          val tabulate : int -> (int -> 'a) -> 'a vector
          val length : 'a vector -> int
          val sub : 'a vector -> int -> 'a
    
          val foldl : ('a -> 'b -> 'b) -> 'b -> 'a vector -> 'b
          val foldli : (int -> 'a -> 'b -> 'b) -> 'b -> 'a vector -> 'b
          val foldr : ('a -> 'b -> 'b) -> 'b -> 'a vector -> 'b
          val foldri : (int -> 'a -> 'b -> 'b) -> 'b -> 'a vector -> 'b
          val app : ('a -> unit) -> 'a vector -> unit
          val appi : (int -> 'a -> unit) -> 'a vector -> unit
    
       end
    
    structure Vector : VECTOR

- `tabulate : int -> (int -> 'a) -> 'a vector`

  Applies the initializer in order of increasing index.
