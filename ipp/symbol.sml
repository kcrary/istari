
(*
These are all provided by cmlib/defaults.sml

structure Symbol =
   SymbolFun (structure Value = StringHashable)

structure SymbolHashable =
   SymbolHashableFun (structure Symbol = Symbol)

structure SymbolHashTable =
   HashTable (structure Key = SymbolHashable)

structure SymbolOrdered =
   SymbolOrderedFun (structure Symbol = Symbol)

*)

structure SymbolPickleable =
   SymbolPickleableFun (structure Value = StringPickleable
                        structure Symbol = Symbol)

structure SymbolDict =
   SplayDict (structure Key = SymbolOrdered)

structure SymbolSet =
   SplaySet (structure Elem = SymbolOrdered)

structure SymbolListHashable =
   ListHashable (structure Elem = SymbolHashable)
