
structure Nonce :> NONCE =
   struct

      val n = Susp.delay (fn () => ConvertWord.intInfToWord32 (Time.toMilliseconds (Time.now ())))

      fun nonce () = Susp.force n

   end
