
structure Syntax =
   struct

      type symbol = Symbol.symbol

      datatype term =
         Var of symbol
       | Const of symbol
       | Metavar of symbol * sub

       | Lam of symbol * term
       | App of term * term

       | Pair of term * term
       | Pi1 of term
       | Pi2 of term

       | Next of term
       | Prev of term

       | Triv

      withtype sub = (term * symbol) list


      datatype class =
         Tm of term
       | Tml of term
       | Tmh of term
       | Tmlh of term
       | Tp
       | Tpl
       | Tph


      type hyp = symbol * class


      (* ([... (promotei, Gi, Ci, xi) ...], C, M)
         is
         ... promotei(H), Gi |- Ci ext xi ...
         ------------------------------------
         H |- C ext M

         (hypotheses are given newest first)
      *)
      type rule =
         (bool * hyp list * term * symbol option) list
         * term * term


      (* ([... premisei ...], G, C, M)
         is
         ... premisei ...
         --------------------
         H1, G, H2 |- C ext M

         where premise (promotei, Gi, SOME si, Ci, xi)
         is
         promote(H1), Gi, H2[si] |- Ci ext xi

         and premise (promotei, Gi, NONE, Ci, xi)
         is
         promote(H1), Gi |- Ci ext xi
      *)
      type lrule =
         (bool * hyp list * sub option * term * symbol option) list
         * hyp list * term * term

      datatype clause =
         Rule of symbol * rule * bool  (* true indicates axiom *)
       | LRule of symbol * lrule

   end