# Vector

    signature VECTOR =
       sig
    
          type 'a vector
    
          val fromList : 'a list -> 'a vector
          val tabulate : int -> (int -> 'a) -> 'a vector
          val length : 'a vector -> int
          val sub : 'a vector -> int -> 'a
    
          val map : ('a -> 'b) -> 'a vector -> 'b vector
          val mapi : (int -> 'a -> 'b) -> 'a vector -> 'b vector
          val foldl : ('a -> 'b -> 'b) -> 'b -> 'a vector -> 'b
          val foldli : (int -> 'a -> 'b -> 'b) -> 'b -> 'a vector -> 'b
          val foldr : ('a -> 'b -> 'b) -> 'b -> 'a vector -> 'b
          val foldri : (int -> 'a -> 'b -> 'b) -> 'b -> 'a vector -> 'b
          val app : ('a -> unit) -> 'a vector -> unit
          val appi : (int -> 'a -> unit) -> 'a vector -> unit
    
          val find : ('a -> bool) -> 'a vector -> 'a option
          val findi : (int -> 'a -> bool) -> 'a vector -> 'a option
          val findmap : ('a -> 'b option) -> 'a vector -> 'b option
          val findmapi : (int -> 'a -> 'b option) -> 'a vector -> 'b option

       end
    
    structure Vector : VECTOR

- `tabulate : int -> (int -> 'a) -> 'a vector`

  Applies the initializer in order of increasing index.

- `find : ('a -> bool) -> 'a vector -> 'a option`

  Applies the test in order of increasing index.

- `findi : (int -> 'a -> bool) -> 'a vector -> 'a option`

  Applies the test in order of increasing index.

- `findmap : ('a -> 'b option) -> 'a vector -> 'b option`

  Applies the function in order of increasing index.

- `findmapi : (int -> 'a -> 'b option) -> 'a vector -> 'b option`

  Applies the function in order of increasing index.
