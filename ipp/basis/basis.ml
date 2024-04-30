
include Basis_sig


module Bool : BOOL with type bool = bool =
   struct

      type bool = Bool.t = false | true 
      let not = not 
      
   end


module Int : INTEGER with type int = int =
   struct

      type nonrec int = int
      let minInt = Some min_int
      let maxInt = Some max_int
      let s__t = (~-)
      let s__P = (+)
      let s__M = (-) 
      let s__T = ( * ) 
      let div = (/)
      let rem = Int.rem
      let min x y = if x < y then x else y
      let max x y = if x > y then x else y
      let abs = Int.abs

      let divmod x y =
         let q = Int.div x y 
         in
         let r = Int.rem x y
         in
            if r >= 0 then
               (q, r)
            else if y >= 0 then
               (q - 1, r + y)
            else
               (q + 1, r - y)

      let s__e = Int.equal
      let s__LG x y = not (Int.equal x y)
      let s__L = (<) 
      let s__G = (>) 
      let s__Le = (<=)
      let (>=) = (>=) 
      let compare = Order.intCompare

      let toStringStd = Int.to_string

      let toString x =
         if x < 0 then
            "~" ^ Int.to_string (- x)
         else
            Int.to_string x

      let fromInt x = x
      let toInt x = x

      let rec natrecUpLoop f x i n =
         if i = n then
            x
         else
            natrecUpLoop f (f i x) (i+1) n

      let natrecUp f x n =
         if n < 0 then
            raise (Invalid_argument "negative argument to natrecUp")
         else
            natrecUpLoop f x 0 n

      let rec natrecDownLoop f x i =
         if i = 0 then
            x
         else
            let i' = i - 1
            in
               natrecDownLoop f (f i' x) i'

      let natrecDown f x n =
         if n < 0 then
            raise (Invalid_argument "negative argument to natrecDown")
         else
            natrecDownLoop f x n

   end


module IntInf : INT_INF with type int = Z.t =
   struct

      type nonrec int = Z.t
      let minInt = None
      let maxInt = None
      let s__t = Z.neg
      let s__P = Z.add
      let s__M = Z.sub
      let s__T = Z.mul 
      let div = Z.div
      let rem = Z.rem
      let min x y = if Z.lt x y then x else y
      let max x y = if Z.gt x y then x else y
      let abs = Z.abs
      let s__e = Z.equal
      let s__LG x y = not (Z.equal x y)
      let s__L = Z.lt 
      let s__G = Z.gt
      let s__Le = Z.leq
      let (>=) = Z.geq
      let compare = Order.intInfCompare

      let toStringStd = Z.to_string

      let toString x =
         if Z.lt x Z.zero then
            "~" ^ Z.to_string (Z.neg x)
         else
            Z.to_string x

      let divmod = Z.ediv_rem

      let fromInt = Z.of_int
      let toInt = Z.to_int

      let rec natrecUpLoop f x i n =
         if Z.equal i n then
            x
         else
            natrecUpLoop f (f i x) (Z.add i Z.one) n

      let natrecUp f x n =
         if Z.lt n Z.zero then
            raise (Invalid_argument "negative argument to IntInf.natrecUp")
         else
            natrecUpLoop f x Z.zero n

      let rec natrecDownLoop f x i =
         if Z.equal i Z.zero then
            x
         else
            let i' = Z.sub i Z.one
            in
               natrecDownLoop f (f i' x) i'

      let natrecDown f x n =
         if Z.lt n Z.zero then
            raise (Invalid_argument "negative argument to IntInf.natrecDown")
         else
            natrecDownLoop f x n

      let pow = Z.pow
      let log2 = Z.log2
      let orb = Z.logor
      let xorb = Z.logxor
      let andb = Z.logand
      let notb = Z.lognot
      let shl = Z.shift_left
      let shr = Z.shift_right

   end


module Word64 : WORD with type word = Word64.word =
   struct

      include Word64

      let s__P = add
      let s__M = sub
      let s__T = mul
      let s__e = eq
      let s__LG = neq
      let s__L = lt
      let s__G = gt
      let s__Le = leq
      let (>=) = geq

   end


module LargeWord = Word64


module Word8 : WORD with type word = Word8.word =
   struct

      include Word8

      let s__P = add
      let s__M = sub
      let s__T = mul
      let s__e = eq
      let s__LG = neq
      let s__L = lt
      let s__G = gt
      let s__Le = leq
      let (>=) = geq

   end


module Word32 : WORD with type word = Word32.word =
   struct

      include Word32

      let s__P = add
      let s__M = sub
      let s__T = mul
      let s__e = eq
      let s__LG = neq
      let s__L = lt
      let s__G = gt
      let s__Le = leq
      let (>=) = geq

   end


module Word : WORD with type word = Word62.word =
   struct

      include Word62

      let s__P = add
      let s__M = sub
      let s__T = mul
      let s__e = eq
      let s__LG = neq
      let s__L = lt
      let s__G = gt
      let s__Le = leq
      let (>=) = geq

   end


module String : STRING with type string = string =
   struct

      let fields b str =
         let k = String.length str
         in
         let rec loop i j acc =
            if j >= k then
               String.sub str i (j-i) :: acc
            else if b (String.get str j) then
               loop (j+1) (j+1) (String.sub str i (j-i) :: acc)
            else
               loop i (j+1) acc
         in
            List.rev (loop 0 0 [])
      
      type nonrec string = string

      let length = String.length
      let sub = String.get

      let subOpt s i =
         try
            Some (String.get s i)
         with (Invalid_argument _) -> None

      let substring = String.sub
      let (^) = (^)
      let concat = String.concat ""
      let concatWith = String.concat
      let str ch = String.make 1 ch
      let implode = Stringbasis.implode
      let explode = Stringbasis.explode
      let map = String.map

      let s__e = String.equal
      let s__LG x y = not (String.equal x y)
      let s__L x y = String.compare x y < 0
      let s__G x y = String.compare x y > 0
      let s__Le x y = String.compare x y <= 0
      let (>=) x y = String.compare x y >= 0
      let compare = Order.stringCompare

   end


module Char : CHAR with type char = char =
   struct

      type nonrec char = char

      let ord = Char.code
      let chr = Char.chr

      let s__e = Char.equal
      let s__LG x y = not (Char.equal x y)
      let s__L x y = Char.compare x y < 0
      let s__G x y = Char.compare x y > 0
      let s__Le x y = Char.compare x y <= 0
      let (>=) x y = Char.compare x y >= 0
      let compare = Order.charCompare
      
   end


module List : LIST with type 'a list = 'a list =
   struct

      type 'a list = 'a List.t = [] | (::) of 'a * 'a list

      let null l =
         (match l with
             [] -> true
           | _ :: _ -> false)

      let length = List.length

      let hd l =
         (match l with
             [] -> raise (Invalid_argument "empty")

           | x :: _ -> x)

      let tl l =
         (match l with
             [] -> raise (Invalid_argument "empty")

           | _ :: x -> x)

      let nth l i =
         try
            List.nth l i
         with (Failure _) -> raise (Invalid_argument "subscript")

      let nthOpt = List.nth_opt

      let rec takeOptMain l n acc =
         if n = 0 then
            Some (List.rev acc)
         else if n < 0 then
            raise (Invalid_argument "subscript")
         else
            (match l with
             | [] -> None
             | h :: t -> takeOptMain t (n-1) (h :: acc))

      let take l n =
         (match takeOptMain l n [] with
          | None -> raise (Invalid_argument "subscript")

          | Some x -> x)

      let takeOpt l n = takeOptMain l n []

      let rec dropOptMain l n =
         if n = 0 then
            Some l
         else if n < 0 then
            raise (Invalid_argument "subscript")
         else
            (match l with
             | [] -> None
             | _ :: t -> dropOptMain t (n-1))

      let drop l n =
         (match dropOptMain l n with
          | None -> raise (Invalid_argument "subscript")

          | Some x -> x)

      let dropOpt l n = dropOptMain l n

      let rec splitOptMain l n acc =
         if n = 0 then
            Some (List.rev acc, l)
         else
            (match l with
             | [] -> None
             | h :: t -> splitOptMain t (n-1) (h :: acc))

      let split l n =
         (match splitOptMain l n [] with
          | None -> raise (Invalid_argument "subscript")
          | Some x -> x)

      let splitOpt l n = splitOptMain l n []

      let rec last =
         function
         | [] -> raise (Invalid_argument "empty")
         | [x] -> x
         | _ :: t -> last t

      let (@) = List.append
      let rev = List.rev
      let revAppend = List.rev_append
      let foldl f b l = List.fold_left (fun y x -> f x y) b l
      let foldr f b l = List.fold_right f l b
      let map = List.map
      let mapi = List.mapi
      let mapPartial = List.filter_map
      let revMap = List.rev_map
      let app = List.iter
      let appi = List.iteri
      let find = List.find_opt
      let filter = List.filter
      let exists = List.exists
      let all = List.for_all
      let findmap = List.find_map

      let revMapi f l =
         let (_, l') =
            List.fold_left
               (fun (i, l') x -> (i+1, f i x :: l'))
               (0, [])
               l
         in
            l'

      let rec tabulateLoop i n f acc =
         if i = n then
            List.rev acc
         else
            tabulateLoop (i+1) n f (f i :: acc)

      let tabulate n f =
         if n < 0 then
            raise (Invalid_argument "size")
         else
            tabulateLoop 0 n f []

   end


(* Can't use any of OCaml's list pair utilities because they handle
   unequal lengths differently.
*)

module ListPair : LIST_PAIR =
   struct

      exception UnequalLengths

      let rec foldl f z l1 l2 =
         (match (l1, l2) with
             ([], _) -> z

           | (_, []) -> z

           | (x :: rest1, y :: rest2) ->
                foldl f (f x y z) rest1 rest2)

      let rec foldr f z l1 l2 =
         (match (l1, l2) with
             ([], _) -> z

           | (_, []) -> z

           | (x :: rest1, y :: rest2) ->
                f x y (foldr f z rest1 rest2))

      let rec foldlEq f z l1 l2 =
         (match (l1, l2) with
             ([], []) -> z

           | (x :: rest1, y :: rest2) ->
                foldlEq f (f x y z) rest1 rest2

           | _ -> raise UnequalLengths)

      let rec foldrEq f z l1 l2 =
         (match (l1, l2) with
             ([], []) -> z

           | (x :: rest1, y :: rest2) ->
                f x y (foldrEq f z rest1 rest2)

           | _ -> raise UnequalLengths)

      let zip l1 l2 = foldr (fun x y l -> (x, y) :: l) [] l1 l2
      let zipEq l1 l2 = foldrEq (fun x y l -> (x, y) :: l) [] l1 l2
      
      let rec unzip l =
         (match l with
             [] -> ([], [])

           | (x, y) :: rest ->
                let (l1, l2) = unzip rest
                in
                   (x :: l1, y :: l2))

      let rec app f l1 l2 =
         (match (l1, l2) with
             ([], _) -> ()
           | (_, []) -> ()

           | (x :: rest1, y :: rest2) ->
                (
                f x y;
                app f rest1 rest2
                ))

      let rec appEq f l1 l2 =
         (match (l1, l2) with
             ([], []) -> ()

           | (x :: rest1, y :: rest2) ->
                (
                f x y;
                appEq f rest1 rest2
                )

           | _ -> raise UnequalLengths)

      let map f l1 l2 = foldr (fun x y l -> f x y :: l) [] l1 l2
      let mapEq f l1 l2 = foldrEq (fun x y l -> f x y :: l) [] l1 l2

      let rec all f l1 l2 =
         (match (l1, l2) with
             ([], _) -> true

           | (_, []) -> true

           | (x :: rest1, y :: rest2) ->
                f x y
                &&
                all f rest1 rest2)

      let rec allEq f l1 l2 =
         (match (l1, l2) with
             ([], []) -> true

           | (x :: rest1, y :: rest2) ->
                f x y
                &&
                all f rest1 rest2

           | _ -> false)

      let rec exists f l1 l2 =
         (match (l1, l2) with
             ([], _) -> false

           | (_, []) -> false

           | (x :: rest1, y :: rest2) ->
                f x y
                ||
                exists f rest1 rest2)

   end


module Option : OPTION with type 'a option = 'a option =
   struct

      type nonrec 'a option = 'a option = None | Some of 'a

      let getOpt xo y =
         (match xo with
             None -> y
           | Some x -> x)

      let isSome = Option.is_some
      let valOf = Option.get
      let join = Option.join
      let map = Option.map
      let mapPartial x y = Option.bind y x
      let app = Option.iter
      
   end


(* Need this before Array is shadowed. *)
module Vector : VECTOR =
   struct

      type nonrec 'a vector = 'a array

      let fromList = Array.of_list
      let tabulate = Array.init  (* I am told that we can rely on init applying the initializer in increasing order. *)
      let length = Array.length
      let sub = Array.get
      let foldl f b a = Array.fold_left (fun y x -> f x y) b a
      let foldr f b a = Array.fold_right f a b
      let app = Array.iter
      let appi = Array.iteri
      let map = Array.map
      let mapi = Array.mapi

      let foldli f b a =
         let (_, y) = Array.fold_left (fun (i, y) x -> (i+1, f i x y)) (0, b) a
         in
            y

      let foldri f b a =
         let (_, y) = Array.fold_right (fun x (i, y) -> (i+1, f i x y)) a (0, b)
         in
            y

      let findi f a =
         let len = Array.length a
         in
         let rec loop i =
            if i >= len then
               None
            else
               let x = Array.get a i
               in
                  if f i x then
                     Some x
                  else
                     loop (i+1)
         in
            loop 0

      let find f a = findi (fun _ -> f) a

      let findmapi f a =
         let len = Array.length a
         in
         let rec loop i =
            if i >= len then
               None
            else
               (match f i (Array.get a i) with
                   None ->
                      loop (i+1)

                 | Some _ as ans -> ans)
         in
            loop 0

      let findmap f a = findmapi (fun _ -> f) a

   end


module Array : ARRAY with type 'a array = 'a array =
   struct

      type nonrec 'a array = 'a array

      let array = Array.make
      let fromList = Array.of_list
      let tabulate = Array.init  (* I am told that we can rely on init applying the initializer in increasing order. *)
      let length = Array.length
      let sub = Array.get
      let update = Array.set
      let foldl f b a = Array.fold_left (fun y x -> f x y) b a
      let foldr f b a = Array.fold_right f a b
      let app = Array.iter
      let appi = Array.iteri
      let blit = Array.blit
      let subarray = Array.sub

      let foldli f b a =
         let (_, y) = Array.fold_left (fun (i, y) x -> (i+1, f i x y)) (0, b) a
         in
            y

      let foldri f b a =
         let (_, y) = Array.fold_right (fun x (i, y) -> (i+1, f i x y)) a (0, b)
         in
            y

      let findi f a =
         let len = Array.length a
         in
         let rec loop i =
            if i >= len then
               None
            else
               let x = Array.get a i
               in
                  if f i x then
                     Some x
                  else
                     loop (i+1)
         in
            loop 0

      let find f a = findi (fun _ -> f) a

      let findmapi f a =
         let len = Array.length a
         in
         let rec loop i =
            if i >= len then
               None
            else
               (match f i (Array.get a i) with
                   None ->
                      loop (i+1)

                 | Some _ as ans -> ans)
         in
            loop 0

      let findmap f a = findmapi (fun _ -> f) a

   end


module IO : IO =
   struct

      type ioerr = string
      exception Io = Sys_error
      let ioerrToString str = str

   end


module TextIO : TEXT_IO =
   struct

      type instream = Stdlib.in_channel * bool ref
      type outstream = Stdlib.out_channel * bool ref

      let input1 (inc, closed) =
         if !closed then
            None
         else
            try
               Some (Stdlib.input_char inc)
            with
               End_of_file -> None

      let buffer = Bytes.create 256

      let inputN (inc, closed) n =
         if !closed then
            ""
         else
            let buf =
               if n <= 256 then
                  buffer
               else
                  Bytes.create n
            in
            let m = Stdlib.input inc buf 0 n
            in
               Bytes.sub_string buf 0 m

      let inputLine (inc, closed) =
         if !closed then
            None
         else
            try
               Some (Stdlib.input_line inc ^ "\n")
            with
               End_of_file -> None

      let output1 (outc, closed) ch = 
         if !closed then
            ()
         else
            Stdlib.output_char outc ch

      let output (outc, closed) str = 
         if !closed then
            ()
         else
            Stdlib.output_string outc str

      let flushOut (outc, closed) =
         if !closed then
            ()
         else
            Stdlib.flush outc

      let openIn filename = (Stdlib.open_in filename, ref false)

      let closeIn (outc, closed) = 
         (
         closed := true;
         Stdlib.close_in outc
         )

      let openOut filename = (Stdlib.open_out filename, ref false)

      let openAppend filename =
         (Stdlib.open_out_gen [Stdlib.Open_append; Stdlib.Open_creat] 0o644 filename, ref false)

      let closeOut (outc, closed) = 
         (
         closed := true;
         Stdlib.close_out outc
         )

      let stdIn = (Stdlib.stdin, ref false)
      let stdOut = (Stdlib.stdout, ref false)
      let stdErr = (Stdlib.stderr, ref false)

      let print = print_string

   end


module BinIO : 
   sig
      include BIN_IO
      val outputString : outstream -> string -> unit
   end
   =
   struct

      type instream = Stdlib.in_channel * bool ref
      type outstream = Stdlib.out_channel * bool ref

      let input1 (inc, closed) =
         if !closed then
            None
         else
            try
               Some (Word8.fromInt (Stdlib.input_byte inc))
            with
               End_of_file -> None

      let output1 (outc, closed) ch = 
         if !closed then
            ()
         else
            Stdlib.output_byte outc (Word8.toInt ch)

      let flushOut (outc, closed) =
         if !closed then
            ()
         else
            Stdlib.flush outc

      let openIn filename = (Stdlib.open_in_bin filename, ref false)

      let closeIn (outc, closed) = 
         (
         closed := true;
         Stdlib.close_in outc
         )

      let openOut filename = (Stdlib.open_out_bin filename, ref false)

      let openAppend filename =
         (Stdlib.open_out_gen [Stdlib.Open_append; Stdlib.Open_creat; Stdlib.Open_binary] 0o644 filename, ref false)

      let closeOut (outc, closed) = 
         (
         closed := true;
         Stdlib.close_out outc
         )

      let outputString (outc, closed) str = 
         if !closed then
            ()
         else
            Stdlib.output_string outc str

   end


module General : GENERAL =
   struct

      type order = Order.order = LESS | EQUAL | GREATER
      type nonrec exn = exn
      type nonrec unit = unit
      
      exception Div = Stdlib.Division_by_zero
      exception Fail = Stdlib.Failure
      exception Invalid = Stdlib.Invalid_argument
      exception Subscript

      let s__b = (!)
      let s__ce = (:=)
      let ($) f x = f x

      let fst (x, y) = x
      let snd (x, y) = y
      let n1of3 (x, y, z) = x
      let n2of3 (x, y, z) = y
      let n3of3 (x, y, z) = z

   end


module Cont : CONT =
   struct

      type 'a cont = unit

      let callcc f = f ()

      let throw () x =
         raise (General.Fail "Continuations not implemented.")

   end
