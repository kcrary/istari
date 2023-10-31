# String

    signature STRING =
       sig
    
          type string
    
          val length : string -> int
          val sub : string -> int -> char
          val subOpt : string -> int -> char option
          val substring : string -> int -> int -> string
          val (^) : string -> string -> string
          val concat : string list -> string
          val concatWith : string -> string list -> string
    
          val str : char -> string
          val implode : char list -> string
          val explode : string -> char list
          
          val map : (char -> char) -> string -> string
    
          val (=) : string -> string -> bool
          val (<>) : string -> string -> bool
          val (<) : string -> string -> bool
          val (<=) : string -> string -> bool
          val (>) : string -> string -> bool
          val (>=) : string -> string -> bool
          val compare : string -> string -> order
    
          val fields : (char -> bool) -> string -> string list
    
       end
    
    structure String : STRING where type string = Pervasive.string

- `val substring : string -> int -> int -> string`

  Given `s`, `i`, and `j`, returns the substring of `s` that starts at
  position `i` and has length `j`.
