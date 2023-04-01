
(* Stripped-down copies of signatures from the SML basis. *)

signature Smlbasis__BOOL =
   sig

      type bool

      val not : bool -> bool
      
   end


signature Smlbasis__INTEGER =
   sig

      type int

      val minInt : int option
      val maxInt : int option

      val ~ : int -> int
      val + : int * int -> int
      val - : int * int -> int
      val * : int * int -> int
      val div : int * int -> int
      val mod : int * int -> int
      val min : int * int -> int
      val max : int * int -> int
      val abs : int -> int

      val < : int * int -> bool
      val > : int * int -> bool
      val <= : int * int -> bool
      val >= : int * int -> bool
      val compare : int * int -> order

      val toString : int -> string
      val toInt : int -> Int.int
      val fromInt : Int.int -> int

   end


signature Smlbasis__INT_INF =
   sig

      include Smlbasis__INTEGER

      val pow : int * Int.int -> int
      val log2 : int -> Int.int
      val orb : int * int -> int
      val xorb : int * int -> int
      val andb : int * int -> int
      val notb : int -> int
      val << : int * Word.word -> int
      val ~>> : int * Word.word -> int

   end


signature Smlbasis__WORD =
   sig

      type word

      val wordSize : int

      val toLargeWord : word -> LargeWord.word
      val toLargeWordX : word -> LargeWord.word
      val fromLargeWord : LargeWord.word -> word
      val toInt : word -> int
      val toIntX : word -> int
      val fromInt : int -> word
      val toLargeInt : word -> IntInf.int
      val toLargeIntX : word -> IntInf.int
      val fromLargeInt : IntInf.int -> word

      val andb : word * word -> word
      val orb : word * word -> word
      val xorb : word * word -> word
      val notb : word -> word
      val << : word * Word.word -> word
      val >> : word * Word.word -> word
      val ~>> : word * Word.word -> word

      val + : word * word -> word
      val - : word * word -> word
      val * : word * word -> word
      val div : word * word -> word
      val mod : word * word -> word

      val < : word * word -> bool
      val > : word * word -> bool
      val <= : word * word -> bool
      val >= : word * word -> bool
      val compare : word * word -> order

      val toString : word -> string

   end


signature Smlbasis__STRING =
   sig

      type string

      val size : string -> int
      val sub : string * int -> char
      val substring : string * int * int -> string
      val extract : string * int * int option -> string
      val ^ : string * string -> string
      val concat : string list -> string
      val concatWith : string -> string list -> string

      val str : char -> string
      val implode : char list -> string
      val explode : string -> char list
      
      val map : (char -> char) -> string -> string

      val < : string * string -> bool
      val <= : string * string -> bool
      val > : string * string -> bool
      val >= : string * string -> bool
      val compare : string * string -> order

      val fields : (char -> bool) -> string -> string list

   end


signature Smlbasis__CHAR =
   sig

      type char

      val ord : char -> int
      val chr : int -> char

      val < : char * char -> bool
      val <= : char * char -> bool
      val > : char * char -> bool
      val >= : char * char -> bool
      val compare : char * char -> order

   end


signature Smlbasis__LIST =
   sig

      datatype list = datatype list

      val null : 'a list -> bool
      val length : 'a list -> int
      val hd : 'a list -> 'a
      val tl : 'a list -> 'a list
      val nth : 'a list * int -> 'a
      val take : 'a list * int -> 'a list
      val drop : 'a list * int -> 'a list
      val last : 'a list -> 'a

      val @ : 'a list * 'a list -> 'a list
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


signature Smlbasis__LIST_PAIR =
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


signature Smlbasis__OPTION =
   sig

      datatype 'a option = NONE | SOME of 'a

      val getOpt : 'a option * 'a -> 'a
      val isSome : 'a option -> bool
      val valOf : 'a option -> 'a
      val join : 'a option option -> 'a option
      val map : ('a -> 'b) -> 'a option -> 'b option
      val mapPartial : ('a -> 'b option) -> 'a option -> 'b option
      val app : ('a -> unit) -> 'a option -> unit

   end


signature Smlbasis__ARRAY =
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


signature Smlbasis__MONO_ARRAY =
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


signature Smlbasis__MONO_ARRAY_SLICE =
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


signature Smlbasis__IO =
   sig
      (* This is abstract, because we cannot reconcile the different data carried by 
         I/O errors in the SML and OCaml bases.  The programmer must match using a
         wildcard.
      *)
      type ioerr
      exception Io of ioerr
   end


signature Smlbasis__TEXT_IO =
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


signature Smlbasis__BIN_IO =
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


signature Smlbasis__GENERAL =
   sig

      datatype order = datatype General.order
      type exn = exn
      type unit = unit
   
      exception Div
      exception Fail of string
      exception Subscript

      (* For interfacing with IML code. Not part of the SML basis. *)
      exception Invalid of string

      val ! : 'a ref -> 'a
      val := : 'a ref * 'a -> unit
      val o : ('b -> 'c) * ('a -> 'b) -> 'a -> 'c

   end


signature IML__SMLBASIS =
   sig

      structure Bool : Smlbasis__BOOL where type bool = Bool.bool
      structure Int : Smlbasis__INTEGER where type int = Int.int
      structure IntInf : Smlbasis__INT_INF where type int = IntInf.int
      structure Word : Smlbasis__WORD where type word = Word.word
      structure LargeWord : Smlbasis__WORD where type word = Word64.word
      structure Word8 : Smlbasis__WORD where type word = Word8.word
      structure Word32 : Smlbasis__WORD where type word = Word32.word
      structure Word64 : Smlbasis__WORD where type word = Word64.word
      structure String : Smlbasis__STRING where type string = String.string
      structure Char : Smlbasis__CHAR where type char = Char.char
      structure List : Smlbasis__LIST
      structure ListPair : Smlbasis__LIST_PAIR
      structure Option : Smlbasis__OPTION where type 'a option = 'a Option.option
      structure Array : Smlbasis__ARRAY where type 'a array = 'a Array.array
      structure Word8Array : Smlbasis__MONO_ARRAY where type elem = Word8.word where type array = Word8Array.array 
      structure Word8ArraySlice : Smlbasis__MONO_ARRAY_SLICE where type elem = Word8.word where type array = Word8Array.array where type slice = Word8ArraySlice.slice
      structure IO : Smlbasis__IO
      structure TextIO : Smlbasis__TEXT_IO where type instream = TextIO.instream where type outstream = TextIO.outstream
      structure BinIO : Smlbasis__BIN_IO where type instream = BinIO.instream where type outstream = BinIO.outstream
      structure General : Smlbasis__GENERAL

      val s__e : ''a * ''a -> bool
      val <> : ''a * ''a -> bool

   end


structure OriginalBasis =
   struct

      structure Bool = Bool
      structure Int = Int
      structure IntInf = IntInf
      structure Word64 = Word64
      structure LargeWord = Word64
      structure Word = Word

      structure Word8 =
         struct
            open Word8
        
            (* work around bug in 32-bit SML/NJ *)
            fun toLargeInt x = IntInf.fromInt (Word8.toInt x)
            fun toLargeIntX x = IntInf.fromInt (Word8.toIntX x)
         end

      structure Word32 = Word32
      structure LargeWord = LargeWord
      structure String = String
      structure Char = Char
      structure List = List
      structure ListPair = ListPair
      structure Option = Option
      structure Array = Array
      structure Word8Array = Word8Array
      structure Word8ArraySlice = Word8ArraySlice

      structure General =
         struct
            open General

            exception Invalid = Basis.General.Invalid
         end

      structure IO = IO
      structure TextIO = TextIO
      structure BinIO = BinIO

   end
   

structure Smlbasis :> IML__SMLBASIS =
   struct

      open OriginalBasis

      structure IO =
         struct
            type ioerr = {name : string, function : string, cause : exn}
            exception Io = IO.Io
         end

      (* really calling polyEqual (of course) *)
      fun s__e (x, y) = x = y
      fun op <> (x, y) = x <> y

   end
