
signature SPAN =
   sig

      type pos = int
      type span = pos * pos

      val join : span -> span -> span

   end


structure Span :> SPAN =
   struct

      type pos = int
      type span = pos * pos

      fun join (l, _) (_, r) = (l, r)

   end