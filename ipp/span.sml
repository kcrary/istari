
signature SPAN =
   sig

      type pos = int * int
      type span = pos * pos

      val origin : pos

      val add : pos -> int -> pos
      val addnl : pos -> pos

      val join : span -> span -> span

   end


structure Span :> SPAN =
   struct

      type pos = int * int
      type span = pos * pos

      val origin = (1, 0)  (* starting from 1 is gross, but standard *)

      fun add (row, col) d = (row, col+d)
      fun addnl (row, col) = (row+1, 0)

      fun join (l, _) (_, r) = (l, r)

   end