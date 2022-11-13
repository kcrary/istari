# Unify

    (* abbreviated *)
    signature UNIFY =
       sig
    
          type term
          type ebind
          type sub
    
          val unify : term -> term -> unit
    
          val solve : unit -> bool
    
          val unify1 : term -> term -> bool  (* unify followed by solve *)
    
          val errorMessage : string ref
    
          (* setEbindSub E s m  sets  E[s] := m, bool indicates success *)
          val setEbindSub : ebind -> sub -> term -> bool
    
       end
