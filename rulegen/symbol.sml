(*
structure Symbol =
   SymbolFun (structure Value = StringHashable)

structure SymbolHashable =
   SymbolHashableFun (structure Symbol = Symbol)

structure SymbolOrdered =
   SymbolOrderedFun (structure Symbol = Symbol)
*)

structure Symbol =
   struct

      type value = string
      type symbol = string

      val eq = op = : string * string -> bool
      val compare = String.compare

      fun fromValue x = x
      fun toValue x = x
      
      fun hash x = StringHashable.hash

   end

structure SymbolHashable = StringHashable

structure SymbolOrdered = StringOrdered
