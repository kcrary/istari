
functor NarrowOutputFun (Output : OUTPUT) :> OUTPUT where type t = Output.t =
   struct

      type t = Output.t

      val enter = Output.enter
      val leave = Output.leave

      val width = ref 0

      fun init x =
         (
         width := 0;
         Output.init x
         )

      fun findSpace str i =
         if i >= String.size str then
            NONE
         else if String.sub (str, i) = #" " then
            SOME i
         else
            findSpace str (i+1)

      fun write str = 
         if !width + String.size str > 60 then
            (case findSpace str 0 of
                SOME i =>
                   (
                   Output.write (String.substring (str, 0, i));
                   Output.write "\n";
                   width := 0;
                   write (String.extract (str, i+1, NONE))
                   )

              | NONE =>
                   (
                   Output.write str;
                   width := !width + String.size str
                   ))
         else
            (
            Output.write str;
            width := !width + String.size str
            )

   end
