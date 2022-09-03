
type nonrec word = int64

let wordSize = Sys.int_size

let toLargeWord x = x
let toLargeWordX x = x
let fromLargeWord x = x
let toInt = Int64.to_int
let toIntX = Int64.to_int
let fromInt = Int64.of_int
let toInt64 x = x

let two_power_64 = Z.pow (Z.of_int 2) 64

let toLargeInt x =
   if Int64.compare x 0L < 0 then
      Z.add two_power_64 (Z.of_int64 x)
   else
      Z.of_int64 x

let toLargeIntX = Z.of_int64
let fromLargeInt = Z.to_int64

let andb = Int64.logand
let orb = Int64.logor
let xorb = Int64.logxor
let notb = Int64.lognot
let shl = Int64.shift_left
let shr = Int64.shift_right_logical
let ashr = Int64.shift_right

let add = Int64.add
let sub = Int64.sub
let mul = Int64.mul
let div = Int64.unsigned_div
let rem = Int64.unsigned_rem

let eq = Int64.equal
let neq x y = not (Int64.equal x y)
let lt x y = Int64.unsigned_compare x y < 0
let gt x y = Int64.unsigned_compare x y > 0
let leq x y = Int64.unsigned_compare x y <= 0
let geq x y = Int64.unsigned_compare x y >= 0

let compare x y =
   let z = Int64.unsigned_compare x y
   in
      if z = 0 then
         Order.EQUAL
      else if z < 0 then
         Order.LESS
      else
         Order.GREATER

let digits = "0123456789ABCDEF"

let rec toStringMain x acc =
   if x = 0L then
      Stringbasis.implode acc
   else
      toStringMain (Int64.shift_right_logical x 4) (String.get digits (Int64.to_int (Int64.logand x 15L)) :: acc)
   
let toString x = toStringMain x []
