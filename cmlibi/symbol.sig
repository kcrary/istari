
signature SYMBOL =
   sig

      type value
      type symbol

      val eq : symbol * symbol -> bool
      val compare : symbol * symbol -> order

      val gensym : unit -> symbol
      val isGensym : symbol -> bool

      (* toValue o fromValue = identity
         the reverse holds as long as the symbol is not a gensym
      *)
      val fromValue : value -> symbol
      val toValue : symbol -> value

      val hash : symbol -> word

   end
