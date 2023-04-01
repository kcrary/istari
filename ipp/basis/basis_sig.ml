
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
      val s__P : int -> int -> int
      val s__M : int -> int -> int
      val s__T : int -> int -> int
      val div : int -> int -> int
      val rem : int -> int -> int
      val min : int -> int -> int
      val max : int -> int -> int
      val abs : int -> int

      val divmod : int -> int -> int * int

      val s__e : int -> int -> bool
      val s__LG : int -> int -> bool
      val s__L : int -> int -> bool
      val s__G : int -> int -> bool
      val s__Le : int -> int -> bool
      val (>=) : int -> int -> bool
      val compare : int -> int -> Order.order

      val toString : int -> string
      val toStringStd : int -> string
      val toInt : int -> prim__int
      val fromInt : prim__int -> int

   end


module type INT_INF =
   sig

      include INTEGER

      val pow : int -> Int.t -> int
      val log2 : int -> Int.t
      val orb : int -> int -> int
      val xorb : int -> int -> int
      val andb : int -> int -> int
      val notb : int -> int
      val shl : int -> Int.t -> int
      val shr : int -> Int.t -> int

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
      
      val andb : word -> word -> word
      val orb : word -> word -> word
      val xorb : word -> word -> word
      val notb : word -> word
      val shl : word -> int -> word
      val shr : word -> int -> word
      val ashr : word -> int -> word
      
      val s__P : word -> word -> word
      val s__M : word -> word -> word
      val s__T : word -> word -> word
      val div : word -> word -> word
      val rem : word -> word -> word
      
      val s__e : word -> word -> bool
      val s__LG : word -> word -> bool
      val s__L : word -> word -> bool
      val s__G : word -> word -> bool
      val s__Le : word -> word -> bool
      val (>=) : word -> word -> bool
      val compare : word -> word -> Order.order
      
      val toString : word -> string

   end


module type STRING =
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

      val s__e : string -> string -> bool
      val s__LG : string -> string -> bool
      val s__L : string -> string -> bool
      val s__G : string -> string -> bool
      val s__Le : string -> string -> bool
      val (>=) : string -> string -> bool
      val compare : string -> string -> Order.order

      val fields : (char -> bool) -> string -> string list

   end


module type CHAR =
   sig

      type char
      val ord : char -> int
      val chr : int -> char

      val s__e : char -> char -> bool
      val s__LG : char -> char -> bool
      val s__L : char -> char -> bool
      val s__G : char -> char -> bool
      val s__Le : char -> char -> bool
      val (>=) : char -> char -> bool
      val compare : char -> char -> Order.order

   end


module type LIST =
   sig

      type 'a list = [] | (::) of 'a * 'a list

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
      val app : ('a -> unit) -> 'a list -> unit
      val appi : (int -> 'a -> unit) -> 'a list -> unit

      val find : ('a -> bool) -> 'a list -> 'a option
      val findmap : ('a -> 'b option) -> 'a list -> 'b option
      val filter : ('a -> bool) -> 'a list -> 'a list
      val exists : ('a -> bool) -> 'a list -> bool
      val all : ('a -> bool) -> 'a list -> bool

   end


module type LIST_PAIR =
   sig

      exception UnequalLengths

      val zip : 'a list -> 'b list -> ('a * 'b) list
      val zipEq : 'a list -> 'b list -> ('a * 'b) list
      val unzip : ('a * 'b) list -> 'a list * 'b list
      val app : ('a -> 'b -> unit) -> 'a list -> 'b list -> unit
      val appEq : ('a -> 'b -> unit) -> 'a list -> 'b list -> unit
      val map : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
      val mapEq : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
      val foldl : ('a -> 'b -> 'c -> 'c) -> 'c -> 'a list -> 'b list -> 'c
      val foldr : ('a -> 'b -> 'c -> 'c) -> 'c -> 'a list -> 'b list -> 'c
      val foldlEq : ('a -> 'b -> 'c -> 'c) -> 'c -> 'a list -> 'b list -> 'c
      val foldrEq : ('a -> 'b -> 'c -> 'c) -> 'c -> 'a list -> 'b list -> 'c
      val all : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
      val exists : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
      val allEq : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

   end


module type OPTION =
   sig

      type 'a option = None | Some of 'a

      val getOpt : 'a option -> 'a -> 'a
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


module type IO =
   sig
      (* This is abstract, because we cannot reconcile the different data carried by 
         I/O errors in the SML and OCaml bases.  The programmer must match using a
         wildcard.
      *)
      type ioerr
      exception Io of ioerr
      val ioerrToString : ioerr -> string
   end


module type TEXT_IO =
   sig

      type instream
      type outstream

      val input1 : instream -> char option
      val inputN : instream -> int -> string
      val inputLine : instream -> string option

      val output1 : outstream -> char -> unit
      val output : outstream -> string -> unit
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

      val output1 : outstream -> Word8.word -> unit
      val flushOut : outstream -> unit

      val openIn : string -> instream
      val closeIn : instream -> unit
      val openOut : string -> outstream
      val openAppend : string -> outstream
      val closeOut : outstream -> unit

   end


module type GENERAL =
   sig

      type order = Order.order = LESS | EQUAL | GREATER
      type nonrec exn = exn
      type nonrec unit = unit

      exception Div
      exception Fail of string
      exception Invalid of string

      (* NB: For interfacing with SML basis only. IML Basis does not raise Subscript. *)
      exception Subscript

      val s__b : 'a ref -> 'a
      val s__ce : 'a ref -> 'a -> unit 
      val ($) : ('a -> 'b) -> 'a -> 'b

      val fst : 'a * 'b -> 'a
      val snd : 'a * 'b -> 'b
      val n1of3 : 'a * 'b * 'c -> 'a
      val n2of3 : 'a * 'b * 'c -> 'b
      val n3of3 : 'a * 'b * 'c -> 'c

   end


module type CONT =
   sig

      type 'a cont

      val callcc : ('a cont -> 'a) -> 'a
      val throw : 'a cont -> 'a -> 'b

   end
