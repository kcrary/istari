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
    
          val find : ('a -> bool) -> 'a array -> 'a option
          val findi : (int -> 'a -> bool) -> 'a array -> 'a option
          val findmap : ('a -> 'b option) -> 'a array -> 'b option
          val findmapi : (int -> 'a -> 'b option) -> 'a array -> 'b option

        end
    
    structure Array : ARRAY

- `tabulate : int -> (int -> 'a) -> 'a array`

  Applies the initializer in order of increasing index.

- `find : ('a -> bool) -> 'a array -> 'a option`

  Applies the test in order of increasing index.

- `findi : (int -> 'a -> bool) -> 'a array -> 'a option`

  Applies the test in order of increasing index.

- `findmap : ('a -> 'b option) -> 'a array -> 'b option`

  Applies the function in order of increasing index.

- `findmapi : (int -> 'a -> 'b option) -> 'a array -> 'b option`

  Applies the function in order of increasing index.
