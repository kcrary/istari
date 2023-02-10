
signature Basis__BOOL =
   sig

      type bool

      val not : bool -> bool
      
   end


signature Basis__INTEGER =
   sig

      type int

      val minInt : int option
      val maxInt : int option

      val ~ : int -> int
      val + : int -> int -> int
      val - : int -> int -> int
      val * : int -> int -> int
      val div : int -> int -> int
      val rem : int -> int -> int
      val min : int -> int -> int
      val max : int -> int -> int
      val abs : int -> int

      val divmod : int -> int -> int * int

      val s__e : int -> int -> bool
      val <> : int -> int -> bool
      val < : int -> int -> bool
      val > : int -> int -> bool
      val <= : int -> int -> bool
      val >= : int -> int -> bool
      val compare : int -> int -> order

      val toString : int -> string
      val toStringStd : int -> string
      val toInt : int -> Int.int
      val fromInt : Int.int -> int

   end


signature Basis__INT_INF =
   sig

      include Basis__INTEGER

      val pow : int -> Int.int -> int
      val log2 : int -> Int.int
      val orb : int -> int -> int
      val xorb : int -> int -> int
      val andb : int -> int -> int
      val notb : int -> int
      val shl : int -> Int.int -> int
      val shr : int -> Int.int -> int

   end


signature Basis__WORD =
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

      val andb : word -> word -> word
      val orb : word -> word -> word
      val xorb : word -> word -> word
      val notb : word -> word
      val shl : word -> int -> word
      val shr : word -> int -> word
      val ashr : word -> int -> word

      val + : word -> word -> word
      val - : word -> word -> word
      val * : word -> word -> word
      val div : word -> word -> word
      val rem : word -> word -> word

      val s__e : word -> word -> bool
      val <> : word -> word -> bool
      val < : word -> word -> bool
      val > : word -> word -> bool
      val <= : word -> word -> bool
      val >= : word -> word -> bool
      val compare : word -> word -> order

      val toString : word -> string

   end


signature Basis__STRING =
   sig

      type string

      val length : string -> int
      val sub : string -> int -> char
      val subOpt : string -> int -> char option
      val substring : string -> int -> int -> string
      val ^ : string -> string -> string
      val concat : string list -> string
      val concatWith : string -> string list -> string

      val str : char -> string
      val implode : char list -> string
      val explode : string -> char list
      
      val map : (char -> char) -> string -> string

      val s__e : string -> string -> bool
      val <> : string -> string -> bool
      val < : string -> string -> bool
      val <= : string -> string -> bool
      val > : string -> string -> bool
      val >= : string -> string -> bool
      val compare : string -> string -> order

      val fields : (char -> bool) -> string -> string list

   end


signature Basis__CHAR =
   sig

      type char

      val ord : char -> int
      val chr : int -> char
      val s__e : char -> char -> bool
      val <> : char -> char -> bool
      val < : char -> char -> bool
      val <= : char -> char -> bool
      val > : char -> char -> bool
      val >= : char -> char -> bool
      val compare : char -> char -> order

   end


signature Basis__LIST =
   sig

      datatype list = datatype list

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

      val @ : 'a list -> 'a list -> 'a list
      val rev : 'a list -> 'a list
      val revAppend : 'a list -> 'a list -> 'a list
      val foldl : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
      val foldr : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
      val map : ('a -> 'b) -> 'a list -> 'b list
      val mapPartial : ('a -> 'b option) -> 'a list -> 'b list
      val mapi : (int -> 'a -> 'b) -> 'a list -> 'b list
      val app : ('a -> unit) -> 'a list -> unit
      val appi : (int -> 'a -> unit) -> 'a list -> unit

      val find : ('a -> bool) -> 'a list -> 'a option
      val findmap : ('a -> 'b option) -> 'a list -> 'b option
      val filter : ('a -> bool) -> 'a list -> 'a list
      val exists : ('a -> bool) -> 'a list -> bool
      val all : ('a -> bool) -> 'a list -> bool

   end


signature Basis__OPTION =
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


signature Basis__ARRAY =
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


signature Basis__IO =
   sig
      (* This is abstract, because we cannot reconcile the different data carried by 
         I/O errors in the SML and OCaml bases.  The programmer must match using a
         wildcard.
      *)
      type ioerr
      exception Io of ioerr
      val ioerrToString : ioerr -> string
   end


signature Basis__TEXT_IO =
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


signature Basis__BIN_IO =
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


signature Basis__GENERAL =
   sig

      datatype order = datatype General.order
      type exn = exn
      type unit = unit
   
      (* The SML basis's Chr, Size, and Subscript all map to Invalid.
         Bind, Match, and Overflow are unhandleable.
      *)

      exception Div
      exception Fail of string
      exception Invalid of string

      (* NB: For interfacing with SML basis only. IML Basis does not raise Subscript. *)
      exception Subscript

      val ! : 'a ref -> 'a
      val := : 'a ref -> 'a -> unit 
      val $ : ('a -> 'b) -> 'a -> 'b

      val fst : 'a * 'b -> 'a
      val snd : 'a * 'b -> 'b
      val n1of3 : 'a * 'b * 'c -> 'a
      val n2of3 : 'a * 'b * 'c -> 'b
      val n3of3 : 'a * 'b * 'c -> 'c

   end


signature Basis__CONT =
   sig

      type 'a cont
      val callcc : ('a cont -> 'a) -> 'a
      val throw : 'a cont -> 'a -> 'b

   end


signature IML__BASIS =
   sig

      structure Bool : Basis__BOOL where type bool = Bool.bool
      structure Int : Basis__INTEGER where type int = Int.int
      structure IntInf : Basis__INT_INF where type int = IntInf.int
      structure Word : Basis__WORD where type word = Word.word
      structure LargeWord : Basis__WORD where type word = Word64.word
      structure Word8 : Basis__WORD where type word = Word8.word
      structure Word32 : Basis__WORD where type word = Word32.word
      structure Word64 : Basis__WORD where type word = Word64.word
      structure String : Basis__STRING where type string = String.string
      structure Char : Basis__CHAR where type char = Char.char
      structure List : Basis__LIST
      structure Option : Basis__OPTION where type 'a option = 'a Option.option
      structure Array : Basis__ARRAY where type 'a array = 'a Array.array
      structure IO : Basis__IO
      structure TextIO : Basis__TEXT_IO where type instream = TextIO.instream where type outstream = TextIO.outstream
      structure BinIO : Basis__BIN_IO where type instream = BinIO.instream where type outstream = BinIO.outstream
      structure General : Basis__GENERAL
      structure Cont : Basis__CONT

   end


functor IML__WordToBasisWord (structure W : WORD
                              val eq : W.word * W.word -> bool) 
   :> Basis__WORD where type word = W.word =
   struct

      type word = W.word
      val wordSize = W.wordSize
      val toLargeWord = W.toLargeWord
      val toLargeWordX = W.toLargeWordX
      val fromLargeWord = W.fromLargeWord
      val toInt = W.toInt
      val toIntX = W.toIntX
      val fromInt = W.fromInt
      val toLargeInt = W.toLargeInt
      val toLargeIntX = W.toLargeIntX
      val fromLargeInt = W.fromLargeInt
      fun andb x y = W.andb (x, y)
      fun orb x y = W.orb (x, y)
      fun xorb x y = W.xorb (x, y)
      val notb = W.notb
      fun shl x y = W.<< (x, Word.fromInt y)
      fun shr x y = W.>> (x, Word.fromInt y)
      fun ashr x y = W.~>> (x, Word.fromInt y)
      fun op + x y = W.+ (x, y)
      fun op - x y = W.- (x, y)
      fun op * x y = W.* (x, y)
      fun op div x y = W.div (x, y)
      fun op rem x y = W.mod (x, y)
      fun s__e x y = eq (x, y)
      fun op <> x y = not (eq (x, y))
      fun op < x y = W.< (x, y)
      fun op > x y = W.> (x, y)
      fun op <= x y = W.<= (x, y)
      fun op >= x y = W.>= (x, y)
      fun compare x y = W.compare (x, y)
      val toString = W.toString

   end


structure Basis :> IML__BASIS =
   struct

      exception Invalid of string

      structure Bool :> Basis__BOOL where type bool = Bool.bool =
         struct

            datatype bool = datatype bool
            val not = Bool.not

         end

      structure IntInf :> Basis__INT_INF where type int = IntInf.int =
         struct

            type int = IntInf.int
            val minInt = IntInf.minInt
            val maxInt = IntInf.maxInt

            fun divmod x y =
               let
                  val qr as (q, r) = IntInf.quotRem (x, y)
               in
                  if r >= 0 then
                     qr
                  else if y >= 0 then
                     (q - 1, r + y)
                  else
                     (q + 1, r - y)
               end

            val ~ = IntInf.~
            fun op + x y = IntInf.+ (x, y)
            fun op - x y = IntInf.- (x, y)
            fun op * x y = IntInf.* (x, y)
            fun op div x y = IntInf.quot (x, y)
            fun op rem x y = IntInf.rem (x, y)
            fun min x y = IntInf.min (x, y)
            fun max x y = IntInf.max (x, y)
            val abs = IntInf.abs
            fun s__e (x : int) (y : int) = x = y
            val op <> = fn (x : int) => fn (y : int) => x <> y
            fun op < (x : int) (y : int) = IntInf.< (x, y)
            fun op > (x : int) (y : int) = IntInf.> (x, y)
            fun op <= (x : int) (y : int) = IntInf.<= (x, y)
            fun op >= (x : int) (y : int) = IntInf.>= (x, y)
            fun compare x y = IntInf.compare (x, y)
            val toString = IntInf.toString
            val fromInt = IntInf.fromInt
            val toInt = IntInf.toInt

            fun toStringStd x =
               if IntInf.< (x, 0) then
                  "-" ^ IntInf.toString (IntInf.~ x)
               else
                  IntInf.toString x
            
            fun pow x y = IntInf.pow (x, y)
            val log2 = IntInf.log2
            fun orb x y = IntInf.orb (x, y)
            fun xorb x y = IntInf.xorb (x, y)
            fun andb x y = IntInf.andb (x, y)
            val notb = IntInf.notb
            
            fun shl x y =
               if Int.< (y, 0) then
                  raise (Invalid "negative shift")
               else
                  IntInf.<< (x, Word.fromInt y)

            fun shr x y =
               if Int.< (y, 0) then
                  raise (Invalid "negative shift")
               else
                  IntInf.~>> (x, Word.fromInt y)

         end

      structure Int :> Basis__INTEGER where type int = Int.int =
         struct

            type int = Int.int
            val minInt = Int.minInt
            val maxInt = Int.maxInt

            fun divmod x y =
               let
                  val q = Int.quot (x, y)
                  val r = Int.rem (x, y)
               in
                  if r >= 0 then
                     (q, r)
                  else if y >= 0 then
                     (q - 1, r + y)
                  else
                     (q + 1, r - y)
               end
            
            val ~ = Int.~
            fun op + x y = Int.+ (x, y)
            fun op - x y = Int.- (x, y)
            fun op * x y = Int.* (x, y)
            fun op div x y = Int.quot (x, y)
            fun op rem x y = Int.rem (x, y)
            fun min x y = Int.min (x, y)
            fun max x y = Int.max (x, y)
            val abs = Int.abs
            fun s__e (x : int) (y : int) = x = y
            val op <> = fn (x : int) => fn (y : int) => x <> y
            fun op < (x : int) (y : int) = Int.< (x, y)
            fun op > (x : int) (y : int) = Int.> (x, y)
            fun op <= (x : int) (y : int) = Int.<= (x, y)
            fun op >= (x : int) (y : int) = Int.>= (x, y)
            fun compare x y = Int.compare (x, y)
            val toString = Int.toString

            fun toStringStd x =
               if Int.< (x, 0) then
                  "-" ^ Int.toString (~ x)
               else
                  Int.toString x
            
            fun fromInt x = x
            fun toInt x = x

         end

      structure Word :> Basis__WORD where type word = Word.word =
         IML__WordToBasisWord (structure W = Word
                               val eq : word * word -> bool = op =)

      structure Word64 :> Basis__WORD where type word = Word64.word =
         IML__WordToBasisWord (structure W = Word64
                               val eq : Word64.word * Word64.word -> bool = op =)

      structure LargeWord = Word64

      structure Word8 :> Basis__WORD where type word = Word8.word =
         struct
            structure W =
               IML__WordToBasisWord (structure W = Word8
                                     val eq : Word8.word * Word8.word -> bool = op =)
      
            open W

            (* work around bug in 32-bit SML/NJ *)
            fun toLargeInt x = IntInf.fromInt (Word8.toInt x)
            fun toLargeIntX x = IntInf.fromInt (Word8.toIntX x)
         end

      structure Word32 :> Basis__WORD where type word = Word32.word =
         IML__WordToBasisWord (structure W = Word32
                               val eq : Word32.word * Word32.word -> bool = op =)

      structure String :> Basis__STRING where type string = String.string =
         struct

            type string = String.string

            val length = String.size

            fun sub s x =
               String.sub (s, x)
               handle Subscript => raise (Invalid "subscript")

            fun subOpt s x =
               SOME (String.sub (s, x))
               handle Subscript => NONE

            fun substring s x y =
               String.substring (s, x, y)
               handle Subscript => raise (Invalid "subscript")

            fun op ^ x y =
               String.^ (x, y)
               handle Size => raise (Invalid "size")

            fun concat l =
               String.concat l
               handle Size => raise (Invalid "size")

            fun concatWith str l =
               String.concatWith str l
               handle Size => raise (Invalid "size")

            val str = String.str

            fun implode l =
               String.implode l
               handle Size => raise (Invalid "size")

            val explode = String.explode
            val map = String.map
            
            fun s__e (x : string) (y : string) = x = y 
            val op <> = fn (x : string) => fn (y : string) => x <> y
            fun op < x y = String.< (x, y)
            fun op > x y = String.> (x, y)
            fun op <= x y = String.<= (x, y)
            fun op >= x y = String.>= (x, y)
            fun compare x y = String.compare (x, y)

            val fields = String.fields
      
         end

      structure Char :> Basis__CHAR where type char = Char.char =
         struct

            open Char

            fun chr i =
               Char.chr i
               handle Chr => raise (Invalid "char out of range")

            fun s__e (x : char) (y : char) = x = y 
            val op <> = fn (x : char) => fn (y : char) => x <> y
            fun op < x y = Char.< (x, y)
            fun op > x y = Char.> (x, y)
            fun op <= x y = Char.<= (x, y)
            fun op >= x y = Char.>= (x, y)
            fun compare x y = Char.compare (x, y)
      
         end

      structure List :> Basis__LIST =
         struct

            open List

            fun hd l =
               (case l of
                   x :: _ => x
                 | [] => raise (Invalid "empty"))

            fun tl l =
               (case l of
                   _ :: x => x
                 | [] => raise (Invalid "empty"))

            fun nth l n = 
               List.nth (l, n)
               handle Subscript => raise (Invalid "subscript")

            fun nthOpt l n =
               SOME (List.nth (l, n))
               handle Subscript => NONE

            fun take l n = 
               List.take (l, n)
               handle Subscript => raise (Invalid "subscript")

            fun takeOpt l n =
               SOME (List.take (l, n))
               handle Subscript => NONE
              
            fun drop l n =
               List.drop (l, n)
               handle Subscripot => raise (Invalid "subscript")

            fun dropOpt l n =
               SOME (List.drop (l, n))
               handle Subscript => NONE

            fun splitOptMain l n acc =
               if n = 0 then
                  SOME (rev acc, l)
               else
                  (case l of
                      nil => NONE

                    | h :: t => splitOptMain t (n-1) (h :: acc))

            fun split l n =
               (case splitOptMain l n [] of
                   NONE => raise (Fail "too short")
                 | SOME ls => ls)

            fun splitOpt l n = splitOptMain l n []

            fun last l =
               List.last l
               handle Empty => raise (Invalid "empty")
               

            fun op @ x y = List.@ (x, y)
            fun revAppend l1 l2 = List.revAppend (l1, l2)
            fun foldl f b l = List.foldl (fn (x, y) => f x y) b l
            fun foldr f b l = List.foldr (fn (x, y) => f x y) b l

            fun mapiMain f i l =
               (case l of
                   nil => nil
                 | h :: t => f i h :: mapiMain f (i+1) t)

            fun mapi f l = mapiMain f 0 l

            fun appiMain f i l =
               (case l of
                   nil => ()

                 | h :: t =>
                      (
                      f i h;
                      appiMain f (i+1) t
                      ))

            fun appi f l = appiMain f 0 l
      
            fun findmap f l =
               (case l of
                   [] => NONE
      
                 | x :: rest =>
                      (case f x of
                          NONE => findmap f rest
      
                        | y => y))

         end

      structure Option :> Basis__OPTION where type 'a option = 'a Option.option =
         struct

            open Option

            fun getOpt x y = Option.getOpt (x, y)

            fun valOf x =
               (case x of
                   NONE => raise (Invalid "is NONE")

                 | SOME y => y)
      
         end

      structure Array :> Basis__ARRAY where type 'a array = 'a Array.array =
         struct

            open Array

            fun array n x =
               Array.array (n, x)
               handle Size => raise (Invalid "size")

            fun fromList l =
               Array.fromList l
               handle Size => raise (Invalid "size")

            fun tabulate n f =
               Array.tabulate (n, f)
               handle Size => raise (Invalid "size")

            fun sub a n =
               Array.sub (a, n)
               handle Subscript => raise (Invalid "subscript")

            fun update a n x =
               Array.update (a, n, x)
               handle Subscript => raise (Invalid "subscript")

            fun foldl f z a = Array.foldl (fn (x, y) => f x y) z a
            fun foldli f z a = Array.foldli (fn (i, x, y) => f i x y) z a
            fun foldr f z a = Array.foldr (fn (x, y) => f x y) z a
            fun foldri f z a = Array.foldri (fn (i, x, y) => f i x y) z a
            fun appi f a = Array.appi (fn (i, x) => f i x) a

            fun blit src i dst j n =
               ArraySlice.copy {src = ArraySlice.slice (src, i, SOME n),
                                dst = dst,
                                di = j}
               handle Subscript => raise (Invalid "blit")

            fun subarray a i n =
               let
                  val a' = Array.array (n, Array.sub (a, 0))
               in
                  ArraySlice.copy {src = ArraySlice.slice (a, i, SOME n),
                                   dst = a',
                                   di = 0};
                  a'
               end
               handle Subscript => raise (Invalid "subarray")
 
         end


      structure IO :> Basis__IO =
         struct
      
            type ioerr = {name : string, function : string, cause : exn}
            exception Io = IO.Io
            fun ioerrToString ioerr = exnMessage (IO.Io ioerr)
      
         end


      structure TextIO :> Basis__TEXT_IO where type instream = TextIO.instream where type outstream = TextIO.outstream =
         struct

            open TextIO

            fun inputN s i = TextIO.inputN (s, i)
            fun output1 s ch = TextIO.output1 (s, ch)
            fun output s str = TextIO.output (s, str)

         end


      structure BinIO :> Basis__BIN_IO where type instream = BinIO.instream where type outstream = BinIO.outstream =
         struct

            open BinIO

            fun inputN s i = BinIO.inputN (s, i)
            fun output1 s ch = BinIO.output1 (s, ch)
            fun output s str = BinIO.output (s, str)

         end


      structure General :> Basis__GENERAL =
         struct

            datatype order = datatype General.order
            type exn = exn
            type unit = unit

            exception Div = Div
            exception Fail = Fail
            exception Invalid = Invalid
            exception Subscript = Subscript

            val ! = General.!
            fun op := x y = General.:= (x, y)
            fun op $ f x = f x

            fun fst (x, y) = x
            fun snd (x, y) = y
            fun n1of3 (x, y, z) = x
            fun n2of3 (x, y, z) = y
            fun n3of3 (x, y, z) = z

         end

      structure Cont :> Basis__CONT = SMLofNJ.Cont

   end
