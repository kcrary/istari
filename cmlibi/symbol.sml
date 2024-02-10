
functor SymbolFun (structure Value : HASHABLE
                   val gensymValue : int -> Value.t)
   :> SYMBOL where type value = Value.t
   =
   struct

      type value = Value.t

      structure H = HashTable (structure Key = Value)

      val nextIndex = ref 0
      val nextGensym = ref ~1

      val table : (int * value) H.table = H.table 1001

      type symbol = int * value
            
      fun eq ((n1:int, _), (n2, _)) = n1 = n2
             
      fun compare ((n1, _), (n2, _)) = Int.compare (n1, n2)
            
      fun fromValue v =
         H.lookupOrInsert table v
         (fn () =>
             let val n = !nextIndex
             in
                nextIndex := n + 1;
                (n, v)
             end)
             
      fun toValue (n, v) =
         if n >= 0 then
            v
         else
            gensymValue (~n)

      fun hash (n, _) = Word.fromInt n


      val v0 = gensymValue 0

      fun gensym () =
         let val n = !nextGensym
         in
            nextGensym := n - 1;
            (n, v0)
         end

      fun isGensym (n, _) = n < 0

   end


functor SymbolOrderedFun (structure Symbol : SYMBOL)
   :> ORDERED where type t = Symbol.symbol
   =
   struct
      type t = Symbol.symbol

      val eq = Symbol.eq
      val compare = Symbol.compare
   end


functor SymbolHashableFun (structure Symbol : SYMBOL)
   :> HASHABLE where type t = Symbol.symbol
   =
   struct
      type t = Symbol.symbol

      val eq = Symbol.eq
      val hash = Symbol.hash
   end
