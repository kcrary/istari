# RefineTactic

    signature REFINE_TACTIC =
       sig
    
          val refine : Rule.rule -> Tactic.tactic
    
          (* invokes the extra continuation if the refinement fails due to hidden variables *)
          val refineHV : Rule.rule -> (unit -> Tactic.answer) -> Tactic.tactic
    
       end
