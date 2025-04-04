
structure Rule =
   struct

      type symbol = Symbol.symbol

      datatype term =
         Var     of int
       | Varfar  of int  (* refers to the far context in an lrule *)
       | Const   of symbol
       | Lam     of term
       | App     of term * term
       | Pair    of term * term
       | Pi1     of term
       | Pi2     of term
       | Next    of term
       | Prev    of term
       | Triv
       | Metavar of symbol * sub

      and sub =
         Shift of int
       | Dot of term * sub
       | ComposeShiftFar of sub  (* s o [^l] where l is the length of the second context *)
       | Under of sub            (* 0 . 1 ... l-1 . s o [^ l] *)

      datatype hyp =
         Tm of term
       | Tml of term
       | Tmh of term
       | Tmlh of term
       | Tp
       | Tpl
       | Tph

      (* hypotheses are given newest first *)
      type rule = 
         (bool * hyp list * term * symbol option) list
         * term * term

      type lrule =
         (bool * hyp list * sub option * term * symbol option) list
         * hyp list * term * term

      datatype clause =
         Rule of symbol * rule * bool  (* true indicates axiom *)
       | LRule of symbol * lrule

   end
