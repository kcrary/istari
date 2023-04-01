
module type BOOL =
   sig

      type bool

      val not : bool -> bool
      
   end


type nonrec prim__int = int


module type INTEGER =
   sig

      type int

      val minInt : int option
      val maxInt : int option

      val s__t : int -> int
      val s__P : int * int -> int
      val s__M : int * int -> int
      val s__T : int * int -> int
      val div : int * int -> int
      val mod__ : int * int -> int
      val min : int * int -> int
      val max : int * int -> int
      val abs : int -> int

      val s__L : int * int -> bool
      val s__G : int * int -> bool
      val s__Le : int * int -> bool
      val (>=) : int * int -> bool
      val compare : int * int -> Order.order

      val toString : int -> string
      val toInt : int -> prim__int
      val fromInt : prim__int -> int

   end


module type INT_INF =
   sig

      include INTEGER

      val pow : int * Int.t -> int
      val log2 : int -> Int.t
      val orb : int * int -> int
      val xorb : int * int -> int
      val andb : int * int -> int
      val notb : int -> int
      val s__LL : int * Word62.word -> int
      val s__tGG : int * Word62.word -> int

   end


module type WORD =
   sig

      type word
      
      val wordSize : int
      
      val toLargeWord : word -> Word64.word
      val toLargeWordX : word -> Word64.word
      val fromLargeWord : Word64.word -> word
      val toInt : word -> int
      val toIntX : word -> int
      val fromInt : int -> word
      val toLargeInt : word -> Z.t
      val toLargeIntX : word -> Z.t
      val fromLargeInt : Z.t -> word

      val andb : word * word -> word
      val orb : word * word -> word
      val xorb : word * word -> word
      val notb : word -> word
      val s__LL : word * Word62.word -> word
      val (>>) : word * Word62.word -> word
      val s__tGG : word * Word62.word -> word
      
      val s__P : word * word -> word
      val s__M : word * word -> word
      val s__T : word * word -> word
      val div : word * word -> word
      val mod__ : word * word -> word
      
      val s__e : word * word -> bool
      val s__LG : word * word -> bool
      val s__L : word * word -> bool
      val s__G : word * word -> bool
      val s__Le : word * word -> bool
      val (>=) : word * word -> bool
      val compare : word * word -> Order.order
      
      val toString : word -> string

   end


module type STRING =
   sig

      type string

      val size : string -> int
      val sub : string * int -> char
      val substring : string * int * int -> string
      val extract : string * int * int option -> string
      val (^) : string * string -> string
      val concat : string list -> string
      val concatWith : string -> string list -> string

      val str : char -> string
      val implode : char list -> string
      val explode : string -> char list
      
      val map : (char -> char) -> string -> string

      val s__L : string * string -> bool
      val s__G : string * string -> bool
      val s__Le : string * string -> bool
      val (>=) : string * string -> bool
      val compare : string * string -> Order.order

      val fields : (char -> bool) -> string -> string list

   end


module type CHAR =
   sig

      type char
      val ord : char -> int
      val chr : int -> char

      val s__e : char * char -> bool
      val s__LG : char * char -> bool
      val s__L : char * char -> bool
      val s__G : char * char -> bool
      val s__Le : char * char -> bool
      val (>=) : char * char -> bool
      val compare : char * char -> Order.order

   end


module type LIST =
   sig

      type 'a list = [] | (::) of 'a * 'a list

      val null : 'a list -> bool
      val length : 'a list -> int
      val hd : 'a list -> 'a
      val tl : 'a list -> 'a list
      val nth : 'a list * int -> 'a
      val take : 'a list * int -> 'a list
      val drop : 'a list * int -> 'a list
      val last : 'a list -> 'a

      val (@) : 'a list * 'a list -> 'a list
      val rev : 'a list -> 'a list
      val revAppend : 'a list * 'a list -> 'a list
      val foldl : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b
      val foldr : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b
      val map : ('a -> 'b) -> 'a list -> 'b list
      val mapPartial : ('a -> 'b option) -> 'a list -> 'b list
      val app : ('a -> unit) -> 'a list -> unit

      val find : ('a -> bool) -> 'a list -> 'a option
      val filter : ('a -> bool) -> 'a list -> 'a list
      val exists : ('a -> bool) -> 'a list -> bool
      val all : ('a -> bool) -> 'a list -> bool

   end


module type LIST_PAIR =
   sig

      exception UnequalLengths

      val zip : 'a list * 'b list -> ('a * 'b) list
      val zipEq : 'a list * 'b list -> ('a * 'b) list
      val unzip : ('a * 'b) list -> 'a list * 'b list
      val app : ('a * 'b -> unit) -> 'a list * 'b list -> unit
      val appEq : ('a * 'b -> unit) -> 'a list * 'b list -> unit
      val map : ('a * 'b -> 'c) -> 'a list * 'b list -> 'c list
      val mapEq : ('a * 'b -> 'c) -> 'a list * 'b list -> 'c list
      val foldl : ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c
      val foldr : ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c
      val foldlEq : ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c
      val foldrEq : ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c
      val all : ('a * 'b -> bool) -> 'a list * 'b list -> bool
      val exists : ('a * 'b -> bool) -> 'a list * 'b list -> bool
      val allEq : ('a * 'b -> bool) -> 'a list * 'b list -> bool

   end


module type OPTION =
   sig

      type 'a option = None | Some of 'a

      val getOpt : 'a option * 'a -> 'a
      val isSome : 'a option -> bool
      val valOf : 'a option -> 'a
      val join : 'a option option -> 'a option
      val map : ('a -> 'b) -> 'a option -> 'b option
      val mapPartial : ('a -> 'b option) -> 'a option -> 'b option
      val app : ('a -> unit) -> 'a option -> unit

   end


module type ARRAY =
   sig

      type 'a array

      val array : int * 'a -> 'a array
      val fromList : 'a list -> 'a array
      val tabulate : int * (int -> 'a) -> 'a array
      val length : 'a array -> int
      val sub : 'a array * int -> 'a
      val update : 'a array * int * 'a -> unit

      val foldl : ('a * 'b -> 'b) -> 'b -> 'a array -> 'b
      val foldli : (int * 'a * 'b -> 'b) -> 'b -> 'a array -> 'b
      val foldr : ('a * 'b -> 'b) -> 'b -> 'a array -> 'b
      val foldri : (int * 'a * 'b -> 'b) -> 'b -> 'a array -> 'b
      val app : ('a -> unit) -> 'a array -> unit
      val appi : (int * 'a -> unit) -> 'a array -> unit

   end


module type MONO_ARRAY =
   sig

      type elem
      type array

      val array : int * elem -> array
      val fromList : elem list -> array
      val tabulate : int * (int -> elem) -> array
      val length : array -> int
      val sub : array * int -> elem
      val update : array * int * elem -> unit

      val foldl : (elem * 'b -> 'b) -> 'b -> array -> 'b
      val foldli : (int * elem * 'b -> 'b) -> 'b -> array -> 'b
      val foldr : (elem * 'b -> 'b) -> 'b -> array -> 'b
      val foldri : (int * elem * 'b -> 'b) -> 'b -> array -> 'b
      val app : (elem -> unit) -> array -> unit
      val appi : (int * elem -> unit) -> array -> unit

   end


module type MONO_ARRAY_SLICE =
   sig

      type elem
      type array
      type slice

      val full : array -> slice
      val slice : array * int * int option -> slice
      val subslice : slice * int * int option -> slice
      val base : slice -> array * int * int

      val length : slice -> int
      val sub : slice * int -> elem
      val update : slice * int * elem -> unit

      val foldl : (elem * 'b -> 'b) -> 'b -> slice -> 'b
      val foldli : (int * elem * 'b -> 'b) -> 'b -> slice -> 'b
      val foldr : (elem * 'b -> 'b) -> 'b -> slice -> 'b
      val foldri : (int * elem * 'b -> 'b) -> 'b -> slice -> 'b
      val app : (elem -> unit) -> slice -> unit
      val appi : (int * elem -> unit) -> slice -> unit

   end


module type IO =
   sig

      type ioerr
      exception Io of ioerr

   end


module type TEXT_IO =
   sig

      type instream
      type outstream

      val input1 : instream -> char option
      val inputN : instream * int -> string
      val inputLine : instream -> string option

      val output1 : outstream * char -> unit
      val output : outstream * string -> unit
      val flushOut : outstream -> unit

      val openIn : string -> instream
      val closeIn : instream -> unit
      val openOut : string -> outstream
      val openAppend : string -> outstream
      val closeOut : outstream -> unit

      val stdIn : instream
      val stdOut : outstream
      val stdErr : outstream

      val print : string -> unit

   end


module type BIN_IO =
   sig

      type instream
      type outstream

      val input1 : instream -> Word8.word option

      val output1 : outstream * Word8.word -> unit
      val flushOut : outstream -> unit

      val openIn : string -> instream
      val closeIn : instream -> unit
      val openOut : string -> outstream
      val openAppend : string -> outstream
      val closeOut : outstream -> unit

   end


module type GENERAL =
   sig

      exception Div
      exception Fail of string
      exception Subscript


      (* For interfacing with IML code. Not part of the SML basis. *)
      exception Invalid of string

      val s__b : 'a ref -> 'a
      val s__ce : 'a ref * 'a -> unit
      val o : ('b -> 'c) * ('a -> 'b) -> 'a -> 'c

      type order = Order.order = LESS | EQUAL | GREATER
      type nonrec exn = exn
      type nonrec unit = unit
   
   end
