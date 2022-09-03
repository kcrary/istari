
signature ORDERED =
   sig
      type t
         
      val eq : t * t -> bool
      val compare : t * t -> order
   end


structure IntOrdered
   :> ORDERED where type t = int
   =
   struct
      type t = int

      val eq : int * int -> bool = fn _ => false
      fun compare _ = LESS
   end


signature PRE_DICT =
   sig
      type key
      type 'a dict

      val empty : 'a dict
      val insert : 'a dict -> key -> 'a -> 'a dict
      val find : 'a dict -> key -> 'a option

   end


functor RedBlackPreDict (structure Key : ORDERED)
   :> PRE_DICT where type key = Key.t
   =
   struct
      type key = Key.t
      type 'a dict = unit

      val empty = ()
      fun insert _ _ _ = ()
      fun find _ _ = NONE

   end



signature COMMAND_LINE =
   sig

      type 'a parser

      exception Error of string

      (* Note: all combinators commit when they return. There is no backtracking into
         earlier combinators to look for other matches.
      *)

      val return   : 'a -> 'a parser
      val string   : string parser

      val reject   : 'a parser
      val error    : string parser -> 'a parser

      val seq      : 'a parser -> 'b parser -> ('a * 'b) parser
      val or       : 'a parser list -> 'a parser
      val map      : ('a -> 'b) -> 'a parser -> 'b parser

      (* fold f x p = use p as many times as possible, folding the results *)
      val fold     : ('a * 'b -> 'b) -> 'b -> 'a parser -> 'b parser

      (* test f p = if f <next-elem> then p else backtrack *)
      val test     : (string -> bool) -> 'a parser -> 'a parser

      (* eof matches only at the end of the input *)
      val eof      : unit parser

      (* backtracking from within cut skips the enclosing or/fold *)
      val cut      : 'a parser -> 'a parser

      val parse    : 'a parser -> string list -> 'a

      val backtrack : unit -> 'a
 


      type log
      type ('a, 'b) key

      val blank    : log
      val write    : ('a, 'b) key -> 'a -> log -> log
      val read     : ('a, 'b) key -> log -> 'b

      datatype ('a, 'b) machine =
         Machine of { write : 'a -> ('a, 'b) machine,
                      read  : log -> 'b }

      val key      : ('a, 'b) machine -> ('a, 'b) key



      (* Conversions (backtrack if they fail) *)

      val stringToBool : string -> bool



      (* Standard error messages *)

      (* #2 expects #1 *)
      val expects  : string -> string -> string

      (* unexpected argument #1 *)
      val unexpected : string -> string

      (* unrecognized option #1 *)
      val unrecognized : string -> string



      (* Derived forms *)

      (* eq x y = x = y *)
      val eq       : string -> string -> bool

      (* forget p = map (fn _ => ()) p *)
      val forget   : 'a parser -> unit parser

      (* match f = test f (forget string) *)
      val match    : (string -> bool) -> unit parser

      val seq3 : 'a parser -> 'b parser -> 'c parser -> ('a * 'b * 'c) parser
      val seq4 : 'a parser -> 'b parser -> 'c parser -> 'd parser -> ('a * 'b * 'c * 'd) parser

      (* seqfst p q = map fst (seq p q) *)
      val seqfst   : 'a parser -> 'b parser -> 'a parser

      (* seqsnd p q = map snd (seq p q) *)
      val seqsnd   : 'a parser -> 'b parser -> 'b parser

      (* seqf = seqsnd *)
      val seqf     : 'a parser -> 'b parser -> 'b parser

      (* seql ps = List.foldl (fn (p, q) => map (op ::) (seq p q)) (return []) ps *)
      val seql     : 'a parser list -> 'a list parser

      (* trap err p = or [p, error (return err)] *)
      val trap     : string -> 'a parser -> 'a parser
      
      (* mapCompose f p = map (fun g => f o g) p *)
      val mapCompose : ('b -> 'c) -> ('a -> 'b) parser -> ('a -> 'c) parser

      (* foldCompose p = fold (op o) id p *)
      val foldCompose : ('a -> 'a) parser -> ('a -> 'a) parser

      (* mapw k p = map (write k) p *)
      val mapw     : ('a, 'b) key -> 'a parser -> (log -> log) parser

      (* ty = map stringToTy string *)
      val bool     : bool parser

      (* exactly str = match (eq str) *)
      val exactly  : string -> unit parser

      (* unitOpt str k v = map (fn () => write k v) (exactly str) *)
      val unitOpt  : string -> ('a, 'b) key -> 'a -> (log -> log) parser

      (* tyOpt str k = seqf (exactly str) (trap (expects <what> str) (map (write k) ty)) *)
      val boolOpt  : string -> (bool, 'a) key -> (log -> log) parser



      (* Common machines *)

      val default  : 'a -> ('a, 'a) machine
      val default' : (log -> 'a) -> ('a, 'a) machine
      val option   : ('a, 'a option) machine
      val list     : ('a, 'a list) machine

      val mapIn    : ('a -> 'b) -> ('b, 'c) machine -> ('a, 'c) machine
      val mapOut   : ('b -> 'c) -> ('a, 'b) machine -> ('a, 'c) machine

      type 'a id_key = ('a, 'a) key
      type 'a option_key = ('a, 'a option) key
      type 'a list_key = ('a, 'a list) key

      (* limit i err m raises (Error err) after the ith write *)
      val limit    : int -> string -> ('a, 'b) machine -> ('a, 'b) machine

      (* once = limit 1 *)
      val once     : string -> ('a, 'b) machine -> ('a, 'b) machine

   end


structure CommandLine :> COMMAND_LINE =
   struct

      type 'a parser = string list -> 'a * string list

      exception Error of string
      exception Backtrack of int

      fun return x l = (x, l)

      fun string l =
         (case l of
             nil => raise (Backtrack 0)

           | str :: rest => (str, rest))

      fun reject l = raise (Backtrack 0)

      fun error p l =
         let
            val (err, _) = p l
         in
            raise (Error err)
         end

      fun seq p q l1 =
         let
            val (x, l2) = p l1
            val (y, l3) = q l2
         in
            ((x, y), l3)
         end

      fun seq3 p q r l1 =
         let
            val (x, l2) = p l1
            val (y, l3) = q l2
            val (z, l4) = r l3
         in
            ((x, y, z), l4)
         end

      fun seq4 p q r s l1 =
         let
            val (x, l2) = p l1
            val (y, l3) = q l2
            val (z, l4) = r l3
            val (w, l5) = s l4
         in
            ((x, y, z, w), l5)
         end

      fun or ps l =
         let
            fun loop ps =
               (case ps of
                   nil => raise (Backtrack 0)

                 | p :: rest =>
                      (p l
                       handle (Backtrack i) => 
                          if i = 0 then
                             loop rest
                          else
                             raise (Backtrack (i-1))))
         in
            loop ps
         end

      fun map f p l =
         let
            val (x, l') = p l
         in
            (f x, l')
         end

      fun fold f z p l =
         (let
             val (x, l') = p l
          in
             fold f (f (x, z)) p l'
          end
          handle (Backtrack i) =>
             if i = 0 then
                (z, l)
             else
                raise (Backtrack (i-1)))

      fun test f p l =
         (case l of
             nil => raise (Backtrack 0)
             
           | str :: rest =>
                if f str then
                   p l
                else
                   raise (Backtrack 0))

      fun eof l =
         (case l of
             nil => ((), nil)

           | _ :: _ => raise (Backtrack 0))

      fun cut p l =
         (p l
          handle (Backtrack i) => raise (Backtrack (i+1)))

      fun parse p l =
         ((case p l of
              (x, nil) => x
 
            | (_, str :: _) => raise (Error ("unexpected argument " ^ str)))
          handle (Backtrack _) => raise (Error "cannot parse command-line arguments"))
             

      fun backtrack () = raise (Backtrack 0)


      
      structure D = RedBlackPreDict (structure Key = IntOrdered)

      type log = exn D.dict

      type ('a, 'b) key = ('a -> log -> log) * (log -> 'b)

      datatype ('a, 'b) machine =
         Machine of { write : 'a -> ('a, 'b) machine,
                      read  : log -> 'b }

      val blank = D.empty

      fun write (wr, _) = wr
      fun read (_, rd) = rd

      val cur = ref 0

      fun ('a, 'b) key (m : ('a, 'b) machine) =
         let
            val i = !cur
            val () = cur := i + 1

            exception E of ('a, 'b) machine

            fun get log =
               (case D.find log i of
                   NONE => m

                 | SOME (E m') => m'

                 | SOME _ =>
                      raise (Fail "impossible"))

            fun wr x log =
               let
                  val Machine {write, ...} = get log
               in
                  D.insert log i (E (write x))
               end

            fun rd log =
               let
                  val Machine {read, ...} = get log
               in
                  read log
               end
         in
            (wr, rd)
         end



      fun stringToBool str =
         (case str of
             "true" => true
           | "false" => false
           | "yes" => true
           | "no" => false
           | "on" => true
           | "off" => false
           | _ => raise (Backtrack 0))




      fun expects str1 str2 = str2 ^ " expects " ^ str1
      fun unexpected str = "unexpected argument " ^ str
      fun unrecognized str = "unrecognized option " ^ str



      fun cons (x, y) = x :: y
      fun compose (f, g) x = f (g x)
      fun rev l = (case l of nil => nil | x :: xs => rev xs @ [x])



      fun eq (x : string) y = x = y

      fun forget p = map (fn _ => ()) p

      fun match f = test f (forget string)

      fun seqfst p q = map (fn (x, y) => x) (seq p q)

      fun seqsnd p q = map (fn (x, y) => y) (seq p q)

      val seqf = seqsnd

      fun seql ps = foldl (fn (p, q) => map cons (seq p q)) (return []) ps

      fun trap err p = or [p, error (return err)]

      fun mapCompose f p = map (fn g => fn x => f (g x)) p

      fun foldCompose p = fold compose (fn x => x) p

      fun mapw k p = map (write k) p

      val bool = map stringToBool string

      fun exactly (str : string) = match (fn str' => str = str')

      fun unitOpt str k v = map (fn () => write k v) (exactly str)

      fun boolOpt str k = seqf (exactly str) (trap (expects "a boolean argument" str) (map (write k) bool))

      fun default x =
         Machine { write = default, read = (fn _ => x) }
         
      fun default' f =
         Machine { write = default, read = f }

      fun optionWrite x =
         Machine { write = optionWrite, read = (fn _ => SOME x) }

      val option =
         Machine { write = optionWrite, read = (fn _ => NONE) }
         
      fun listWrite l x =
         Machine { write = listWrite (x :: l),
                   read = (fn _ => rev (x :: l)) }

      val list =
         Machine { write = (fn x => listWrite [] x), read = (fn _ => []) }

      fun mapIn f (Machine { write, read }) =
         let
            fun wt x = mapIn f (write (f x))
         in
            Machine {write=wt, read=read}
         end

      fun mapOut f (Machine { write, read }) =
         let
            fun wt x = mapOut f (write x)
            fun rd log = f (read log)
         in
            Machine {write=wt, read=rd}
         end
               

      type 'a id_key = ('a, 'a) key
      type 'a option_key = ('a, 'a option) key
      type 'a list_key = ('a, 'a list) key

      fun limit i err (Machine {write, read}) =
         let
            fun wt x =
               if i <= 0 then
                  raise (Error err)
               else
                  limit (i-1) err (write x)
         in
            Machine {write=wt, read=read}
         end

      fun once err = limit 1 err

   end
