
include Smlbasis_sig


exception Subscript = Basis.General.Subscript


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
      let s__P (x, y) = x + y
      let s__M (x, y) = x - y
      let s__T (x, y) = x * y

      let div (x, y) =
         (match (x >= 0, y >= 0) with
             (true, true) -> x / y
           | (false, false) -> x / y
           | (false, true) -> (x - y + 1) / y
           | (true, false) -> (x - y - 1) / y)

      let mod__ (x, y) =
         let z = x mod y
         in
            if y >= 0 then
               if z >= 0 then
                  z
               else
                  z + y
            else
               if z <= 0 then
                  z
               else
                  z + y

      let min (x, y) = if x < y then x else y
      let max (x, y) = if x > y then x else y
      let abs = Int.abs

      let s__L (x, y) = x < y
      let s__G (x, y) = x > y
      let s__Le (x, y) = x <= y
      let (>=) (x, y) = x >= y

      let compare (x, y) =
         if x < y then
            Order.LESS
         else if x = y then
            Order.EQUAL
         else
            Order.GREATER

      let toString = Int.to_string

      let fromInt x = x
      let toInt x = x

   end


module IntInf : INT_INF with type int = Z.t =
   struct

      type nonrec int = Z.t
      let minInt = None
      let maxInt = None
      let s__t = Z.neg
      let s__P (x, y) = Z.add x y
      let s__M (x, y) = Z.sub x y
      let s__T (x, y) = Z.mul x y

      let div (x, y) =
         (match (Z.geq x Z.zero, Z.geq y Z.zero) with
             (true, true) -> Z.div x y
           | (false, false) -> Z.div x y
           | (false, true) -> Z.div (Z.add (Z.sub x y) Z.one) y
           | (true, false) -> Z.div (Z.sub (Z.sub x y) Z.one) y)

      let mod__ (x, y) =
         let z = Z.rem x y
         in
            if Z.geq y Z.zero then
               if Z.geq z Z.zero then
                  z
               else
                  Z.add z y
            else
               if Z.leq z Z.zero then
                  z
               else
                  Z.add z y

      let min (x, y) = if Z.lt x y then x else y
      let max (x, y) = if Z.gt x y then x else y
      let abs = Z.abs
      let s__LG (x, y) = not (Z.equal x y)
      let s__L (x, y) = Z.lt x y
      let s__G (x, y) = Z.gt x y
      let s__Le (x, y) = Z.leq x y
      let (>=) (x, y) = Z.geq x y
      let compare (x, y) = Order.intInfCompare x y

      let toString = Z.to_string
      let fromInt = Z.of_int
      let toInt = Z.to_int

      let pow (x, y) = Z.pow x y
      let log2 = Z.log2
      let orb (x, y) = Z.logor x y
      let xorb (x, y) = Z.logxor x y
      let andb (x, y) = Z.logand x y
      let notb = Z.lognot
      let s__LL (x, y) = Z.shift_left x (Word62.toInt y)
      let s__tGG (x, y) = Z.shift_right x (Word62.toInt y)

   end


module Word64 : WORD with type word = Word64.word =
   struct

      include Word64

      let andb (x, y) = andb x y
      let orb (x, y) = orb x y
      let xorb (x, y) = xorb x y
      let s__LL (x, y) = shl x (Word62.toInt y)
      let (>>) (x, y) = shr x (Word62.toInt y)
      let s__tGG (x, y) = ashr x (Word62.toInt y)
      let s__P (x, y) = add x y
      let s__M (x, y) = sub x y
      let s__T (x, y) = mul x y
      let div (x, y) = div x y
      let mod__ (x, y) = rem x y
      let s__e (x, y) = eq x y
      let s__LG (x, y) = neq x y
      let s__L (x, y) = lt x y
      let s__G (x, y) = gt x y
      let s__Le (x, y) = leq x y
      let (>=) (x, y) = geq x y
      let compare (x, y) = compare x y

   end


module LargeWord = Word64


module Word : WORD with type word = Word62.word =
   struct

      include Word62

      let andb (x, y) = andb x y
      let orb (x, y) = orb x y
      let xorb (x, y) = xorb x y
      let s__LL (x, y) = shl x (Word62.toInt y)
      let (>>) (x, y) = shr x (Word62.toInt y)
      let s__tGG (x, y) = ashr x (Word62.toInt y)
      let s__P (x, y) = add x y
      let s__M (x, y) = sub x y
      let s__T (x, y) = mul x y
      let div (x, y) = div x y
      let mod__ (x, y) = rem x y
      let s__e (x, y) = eq x y
      let s__LG (x, y) = neq x y
      let s__L (x, y) = lt x y
      let s__G (x, y) = gt x y
      let s__Le (x, y) = leq x y
      let (>=) (x, y) = geq x y
      let compare (x, y) = compare x y

   end


module Word8 : WORD with type word = Word8.word =
   struct

      include Word8

      let andb (x, y) = andb x y
      let orb (x, y) = orb x y
      let xorb (x, y) = xorb x y
      let s__LL (x, y) = shl x (Word62.toInt y)
      let (>>) (x, y) = shr x (Word62.toInt y)
      let s__tGG (x, y) = ashr x (Word62.toInt y)
      let s__P (x, y) = add x y
      let s__M (x, y) = sub x y
      let s__T (x, y) = mul x y
      let div (x, y) = div x y
      let mod__ (x, y) = rem x y
      let s__e (x, y) = eq x y
      let s__LG (x, y) = neq x y
      let s__L (x, y) = lt x y
      let s__G (x, y) = gt x y
      let s__Le (x, y) = leq x y
      let (>=) (x, y) = geq x y
      let compare (x, y) = compare x y

   end


module Word32 : WORD with type word = Word32.word =
   struct

      include Word32

      let andb (x, y) = andb x y
      let orb (x, y) = orb x y
      let xorb (x, y) = xorb x y
      let s__LL (x, y) = shl x (Word62.toInt y)
      let (>>) (x, y) = shr x (Word62.toInt y)
      let s__tGG (x, y) = ashr x (Word62.toInt y)
      let s__P (x, y) = add x y
      let s__M (x, y) = sub x y
      let s__T (x, y) = mul x y
      let div (x, y) = div x y
      let mod__ (x, y) = rem x y
      let s__e (x, y) = eq x y
      let s__LG (x, y) = neq x y
      let s__L (x, y) = lt x y
      let s__G (x, y) = gt x y
      let s__Le (x, y) = leq x y
      let (>=) (x, y) = geq x y
      let compare (x, y) = compare x y

   end



module String : STRING with type string = string =
   struct

      include Basis.String

      let size x = length x

      let sub (x, y) =
         try
            sub x y
         with Invalid_argument _ -> raise Subscript

      let substring (x, y, z) =
         try
            substring x y z
         with Invalid_argument _ -> raise Subscript

      let extract (str, i, lenopt) =
         try
            (match lenopt with
                Some len -> String.sub str i len
   
              | None -> String.sub str i (String.length str - i))
         with Invalid_argument _ -> raise Subscript

      let (^) (x, y) = x ^ y
      let s__L (x, y) = (<) x y
      let s__G (x, y) = (>) x y
      let s__Le (x, y) = (<=) x y
      let (>=) (x, y) = (>=) x y
      let compare (x, y) = compare x y

      let fields = Basis.String.fields

   end


module Char : CHAR with type char = char =
   struct

      type nonrec char = char

      let ord = Char.code
      let chr = Char.chr

      let s__e (x, y) = Char.equal x y
      let s__LG (x, y) = not (Char.equal x y)
      let s__L (x, y) = Char.compare x y < 0
      let s__G (x, y) = Char.compare x y > 0
      let s__Le (x, y) = Char.compare x y <= 0
      let (>=) (x, y) = Char.compare x y >= 0
      let compare (x, y) = Order.charCompare x y
      
   end


module List : LIST with type 'a list = 'a list =
   struct

      include Basis.List

      let nth (l, n) =
         try
            List.nth l n
         with (Failure _ | Invalid_argument _) -> raise Subscript

      let take (l, n) =
         try
            take l n
         with Invalid_argument _ -> raise Subscript

      let drop (l, n) =
         try
            drop l n
         with Invalid_argument _ -> raise Subscript

      let (@) (x, y) = x @ y
      let revAppend (x, y) = List.rev_append x y
      let foldl f b l = List.fold_left (fun y x -> f (x, y)) b l
      let foldr f b l = List.fold_right (fun x y -> f (x, y)) l b

      let rec tabulateLoop i n f acc =
         if i = n then
            List.rev acc
         else
            tabulateLoop (i+1) n f (f i :: acc)

      let tabulate (n, f) =
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

      exception UnequalLengths = Basis.ListPair.UnequalLengths

      let rec foldl f z l12 =
         (match l12 with
             ([], _) -> z

           | (_, []) -> z

           | (x :: rest1, y :: rest2) ->
                foldl f (f (x, y, z)) (rest1, rest2))

      let rec foldr f z l12 =
         (match l12 with
             ([], _) -> z

           | (_, []) -> z

           | (x :: rest1, y :: rest2) ->
                f (x, y, foldr f z (rest1, rest2)))

      let rec foldlEq f z l12 =
         (match l12 with
             ([], []) -> z

           | (x :: rest1, y :: rest2) ->
                foldlEq f (f (x, y, z)) (rest1, rest2)

           | _ -> raise UnequalLengths)

      let rec foldrEq f z l12 =
         (match l12 with
             ([], []) -> z

           | (x :: rest1, y :: rest2) ->
                f (x, y, foldrEq f z (rest1, rest2))

           | _ -> raise UnequalLengths)

      let zip l12 = foldr (fun (x, y, l) -> (x, y) :: l) [] l12
      let zipEq l12 = foldrEq (fun (x, y, l) -> (x, y) :: l) [] l12
      
      let rec unzip l =
         (match l with
             [] -> ([], [])

           | (x, y) :: rest ->
                let (l1, l2) = unzip rest
                in
                   (x :: l1, y :: l2))

      let rec app f l12 =
         (match l12 with
             ([], _) -> ()
           | (_, []) -> ()

           | (x :: rest1, y :: rest2) ->
                (
                f (x, y);
                app f (rest1, rest2)
                ))

      let rec appEq f l12 =
         (match l12 with
             ([], []) -> ()

           | (x :: rest1, y :: rest2) ->
                (
                f (x, y);
                appEq f (rest1, rest2)
                )

           | _ -> raise UnequalLengths)

      let map f l12 = foldr (fun (x, y, l) -> f (x, y) :: l) [] l12
      let mapEq f l12 = foldrEq (fun (x, y, l) -> f (x, y) :: l) [] l12

      let rec all f l12 =
         (match l12 with
             ([], _) -> true

           | (_, []) -> true

           | (x :: rest1, y :: rest2) ->
                f (x, y)
                &&
                all f (rest1, rest2))

      let rec allEq f l12 =
         (match l12 with
             ([], []) -> true

           | (x :: rest1, y :: rest2) ->
                f (x, y)
                &&
                allEq f (rest1, rest2)

           | _ -> false)

      let rec exists f l12 =
         (match l12 with
             ([], _) -> false

           | (_, []) -> false

           | (x :: rest1, y :: rest2) ->
                f (x, y)
                ||
                exists f (rest1, rest2))

   end


module Option : OPTION with type 'a option = 'a option =
   struct

      type nonrec 'a option = 'a option = None | Some of 'a

      let getOpt (xo, y) =
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


(* Before Array so as not to have the primitive Array library shadowed yet. *)
module Word8Array : MONO_ARRAY with type elem = Word8.word with type array = Word8.word array =
   struct

      type elem = Word8.word
      type nonrec array = elem array

      let array (n, x) = Array.make n x
      let fromList = Array.of_list
      let tabulate (n, f) = Array.init n f
      let length = Array.length

      let sub (a, i) =
         try
            Array.get a i
         with Invalid_argument _ -> raise Subscript
         
      let update (a, i, x) =
         try
            Array.set a i x
         with Invalid_argument _ -> raise Subscript

      let foldl f b a = Array.fold_left (fun y x -> f (x, y)) b a
      let foldr f b a = Array.fold_right (fun x y -> f (x, y)) a b
      let app = Array.iter
      let appi f a = Array.iteri (fun i x -> f (i, x)) a

      let foldli f b a =
         let (_, y) = Array.fold_left (fun (i, y) x -> (i+1, f (i, x, y))) (0, b) a
         in
            y

      let foldri f b a =
         let (_, y) = Array.fold_right (fun x (i, y) -> (i-1, f (i, x, y))) a (Array.length a - 1, b)
         in
            y

   end


module Word8ArraySlice : MONO_ARRAY_SLICE with type elem = Word8.word with type array = Word8.word array with type slice = (Word8.word array * int * int) =
   struct

      type elem = Word8.word
      type nonrec slice = elem array * int * int
      type nonrec array = elem array

      let full a = (a, 0, Array.length a)

      let slice (a, i, sz) =
         let len = Array.length a
         in
         let j =
            (match sz with
                None -> len

              | Some l -> i + l)
         in
            if i < 0 || j < i || j > len then
               raise Subscript
            else
               (a, i, j)

      let subslice ((a, i, j), b, sz) =
         let i' = i + b
         in
         let j' =
            (match sz with
                None -> j
                
              | Some l -> i' + l)
         in
            if i' < i || j' < i' || j' > j then
               raise Subscript
            else
               (a, i', j')

      let base (a, i, j) = (a, i, j-i)

      let length (_, i, j) = j - i

      let sub ((a, i, j), k) =
         let k' = i + k
         in
            if k < 0 || k' >= j then
               raise Subscript
            else
               Array.get a k'
         
      let update ((a, i, j), k, x) =
         let k' = i + k
         in
            if k < 0 || k' >= j then
               raise Subscript
            else
               Array.set a k' x

      let rec scan f x i halt inc =
         if i = halt then
            x
         else
            scan f (f i x) (i+inc) halt inc

      let foldl f x (a, i, j) =
         scan (fun k y -> f (Array.get a k, y)) x i j 1

      let foldli f x (a, i, j) =
         scan (fun k y -> f (k-i, Array.get a k, y)) x i j 1

      let foldr f x (a, i, j) =
         scan (fun k y -> f (Array.get a (k-1), y)) x j i (-1)

      let foldri f x (a, i, j) =
         scan (fun k y -> f (k-1-i, Array.get a (k-1), y)) x j i (-1)

      let app f (a, i, j) =
         scan (fun k () -> (f (Array.get a k); ())) () i j 1

      let appi f (a, i, j) =
         scan (fun k () -> (f (k-i, Array.get a k); ())) () i j 1

   end


(* Before Array so as not to have the primitive Array library shadowed yet. *)
module Vector : VECTOR =
   struct

      type nonrec 'a vector = 'a array

      let fromList = Array.of_list
      
      let tabulate (n, f) = Array.init n f

      let length = Array.length

      let sub (a, i) =
         try
            Array.get a i
         with Invalid_argument _ -> raise Subscript
         
      let foldl f b a = Array.fold_left (fun y x -> f (x, y)) b a
      let foldr f b a = Array.fold_right (fun x y -> f (x, y)) a b
      let app = Array.iter
      let appi f a = Array.iteri (fun i x -> f (i, x)) a

      let foldli f b a =
         let (_, y) = Array.fold_left (fun (i, y) x -> (i+1, f (i, x, y))) (0, b) a
         in
            y

      let foldri f b a =
         let (_, y) = Array.fold_right (fun x (i, y) -> (i-1, f (i, x, y))) a (Array.length a - 1, b)
         in
            y

   end


module Array : ARRAY with type 'a array = 'a array =
   struct

      type nonrec 'a array = 'a array

      let array (n, x) = Array.make n x
      let fromList = Array.of_list

      let tabulate (n, f) = Array.init n f

      let length = Array.length

      let sub (a, i) =
         try
            Array.get a i
         with Invalid_argument _ -> raise Subscript
         
      let update (a, i, x) =
         try
            Array.set a i x
         with Invalid_argument _ -> raise Subscript

      let foldl f b a = Array.fold_left (fun y x -> f (x, y)) b a
      let foldr f b a = Array.fold_right (fun x y -> f (x, y)) a b
      let app = Array.iter
      let appi f a = Array.iteri (fun i x -> f (i, x)) a

      let rec tabulateLoop i n f acc =
         if i = n then
            Array.of_list (List.rev acc)
         else
            tabulateLoop (i+1) n f (f i :: acc)
         
      let tabulate (n, f) =
         if n < 0 then
            raise (Invalid_argument "size")
         else
            tabulateLoop 0 n f []

      let foldli f b a =
         let (_, y) = Array.fold_left (fun (i, y) x -> (i+1, f (i, x, y))) (0, b) a
         in
            y

      let foldri f b a =
         let (_, y) = Array.fold_right (fun x (i, y) -> (i-1, f (i, x, y))) a (Array.length a - 1, b)
         in
            y

   end



module IO : IO =
   struct

      type ioerr = string
      exception Io = Sys_error

   end



module TextIO : TEXT_IO with type instream = Basis.TextIO.instream with type outstream = Basis.TextIO.outstream =
   struct

      include Basis.TextIO

      let inputN (s, n) = inputN s n
      let output1 (s, ch) = output1 s ch
      let output (s, str) = output s str

   end


module BinIO : BIN_IO with type instream = Basis.BinIO.instream with type outstream = Basis.BinIO.outstream =
   struct

      include Basis.BinIO

      let output1 (s, ch) = output1 s ch

   end



module General : GENERAL =
   struct

      type order = Order.order = LESS | EQUAL | GREATER
      type nonrec exn = exn
      type nonrec unit = unit
      
      exception Div = Stdlib.Division_by_zero
      exception Fail = Failure
      exception Subscript = Subscript
      exception Invalid = Stdlib.Invalid_argument

      let s__b = (!)
      let s__ce (x, y) = x := y
      let o (f, g) x = f (g x)

   end


let s__e (x, y) = x = y
let s__LG (x, y) = x <> y
let eq = Stdlib.(=)
let neq = Stdlib.(<>)
