# List

    signature LIST =
       sig
    
          datatype list = nil | (::) of 'a * 'a list = Pervasive.list
    
          val null : 'a list -> bool
          val length : 'a list -> int
          val hd : 'a list -> 'a
          val tl : 'a list -> 'a list
          val nth : 'a list -> int -> 'a
          val nthOpt : 'a list -> int -> 'a option
          val take : 'a list -> int -> 'a list
          val takeOpt : 'a list -> int -> 'a list option
          val drop : 'a list -> int -> 'a list
          val dropOpt : 'a list -> int -> 'a list option
          val split : 'a list -> int -> 'a list * 'a list
          val splitOpt : 'a list -> int -> ('a list * 'a list) option
          val last : 'a list -> 'a
    
          val (@) : 'a list -> 'a list -> 'a list
          val rev : 'a list -> 'a list
          val revAppend : 'a list -> 'a list -> 'a list
          val foldl : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
          val foldr : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
          val map : ('a -> 'b) -> 'a list -> 'b list
          val mapi : (int -> 'a -> 'b) -> 'a list -> 'b list
          val mapPartial : ('a -> 'b option) -> 'a list -> 'b list
          val revMap : ('a -> 'b) -> 'a list -> 'b list
          val revMapi : (int -> 'a -> 'b) -> 'a list -> 'b list
          val app : ('a -> unit) -> 'a list -> unit
          val appi : (int -> 'a -> unit) -> 'a list -> unit
    
          val find : ('a -> bool) -> 'a list -> 'a option
          val findmap : ('a -> 'b option) -> 'a list -> 'b option
          val filter : ('a -> bool) -> 'a list -> 'a list
          val exists : ('a -> bool) -> 'a list -> bool
          val all : ('a -> bool) -> 'a list -> bool
          val tabulate : int -> (int -> 'a) -> 'a list
    
       end
    
    structure List : LIST

- `last : 'a list -> 'a`

  Returns the last element of the list.  Raises `Invalid` if the list is empty.

- `revAppend : 'a list -> 'a list -> 'a list`

  Given `l` and `l'`, returns `rev l @ l'`.

- `revMap : ('a -> 'b) -> 'a list -> 'b list`

  Given `f` and `l`, returns `rev (map f l)` but possibly more efficient.

- `revMapi : (int -> 'a -> 'b) -> 'a list -> 'b list`

  Given `f` and `l`, returns `rev (mapi f l)` but possibly more efficient.

- `tabulate : int -> (int -> 'a) -> 'a list`

  Applies the initializer in order of increasing index.
