# Array

    signature ARRAY =
       sig
    
          type 'a array
    
          val array : int -> 'a -> 'a array
          val fromList : 'a list -> 'a array
          val tabulate : int -> (int -> 'a) -> 'a array
          val length : 'a array -> int
          val sub : 'a array -> int -> 'a
          val update : 'a array -> int -> 'a -> unit
          val blit : 'a array -> int -> 'a array -> int -> int -> unit
          val subarray : 'a array -> int -> int -> 'a array
    
          val foldl : ('a -> 'b -> 'b) -> 'b -> 'a array -> 'b
          val foldli : (int -> 'a -> 'b -> 'b) -> 'b -> 'a array -> 'b
          val foldr : ('a -> 'b -> 'b) -> 'b -> 'a array -> 'b
          val foldri : (int -> 'a -> 'b -> 'b) -> 'b -> 'a array -> 'b
          val app : ('a -> unit) -> 'a array -> unit
          val appi : (int -> 'a -> unit) -> 'a array -> unit
    
       end
    
    structure Array : ARRAY

- `tabulate : int -> (int -> 'a) -> 'a array`

  Applies the initializer in order of increasing index.
