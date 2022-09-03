
structure Stream 
   :> STREAM
   =
   struct

      open Susp

      datatype 'a front = Nil | Cons of 'a * 'a stream
      withtype 'a stream = 'a front susp

      val front = force
      fun eager f = delay (fn () => f)
      val lazy = delay

      fun fromProcess f = 
          lazy
          (fn () => 
                 (case f () of
                     NONE =>
                        Nil
                   | SOME x =>
                        Cons (x, fromProcess f)))

      fun fromList l =
          lazy
          (fn () => 
                 (case l of
                     [] => Nil
                   | h :: t => Cons (h, fromList t)))

      fun fromLoop f seed =
          lazy
          (fn () =>
              (case f seed of
                  NONE =>
                     Nil
                | SOME (seed', x) =>
                     Cons (x, fromLoop f seed')))

      fun fromString str =
         let
            val len = String.size str

            fun loop i =
               lazy
               (fn () =>
                   if i = len then
                      Nil
                   else
                      Cons (String.sub (str, i), loop (i+1)))
         in
            loop 0
         end
            
      fun fromBytestring str =
         let
            val len = Bytestring.size str

            fun loop i =
               lazy
               (fn () =>
                   if i = len then
                      Nil
                   else
                      Cons (Bytestring.sub (str, i), loop (i+1)))
         in
            loop 0
         end
            
      fun fromTextInstream ins =
         lazy
         (fn () =>
             (case TextIO.input1 ins of
                 NONE =>
                    (
                    TextIO.closeIn ins;
                    Nil
                    )

               | SOME x =>
                    Cons (x, fromTextInstream ins)))

      fun fromBinInstream ins =
         lazy
         (fn () =>
             (case BinIO.input1 ins of
                 NONE =>
                    (
                    BinIO.closeIn ins;
                    Nil
                    )

               | SOME x =>
                    Cons (x, fromBinInstream ins)))

      fun fix f = f (lazy (fn () => front (fix f)))

      exception Empty

      fun hd s =
          (case front s of
              Nil =>
                 raise Empty
            | Cons (x, _) =>
                 x)

      fun tl s =
          (case front s of
              Nil =>
                 raise Empty
            | Cons (_, s') =>
                 s')

       
      fun op @ (s1, s2) =
          lazy
          (fn () =>
              (case front s1 of
                  Nil =>
                     front s2
                | Cons (h, t) =>
                     Cons (h, t @ s2)))


      fun take (s, n) =
          if n < 0 then
             raise (Fail "invalid subscript")
          else if n = 0 then
             []
          else
             (case front s of
                 Nil =>
                    raise Empty
               | Cons (x, s') =>
                    x :: take (s', n-1))

      fun drop (s, n) =
          if n < 0 then
             raise (Fail "invalid subscript")
          else if n = 0 then
             s
          else
             (case front s of
                 Nil =>
                    raise Empty
               | Cons (x, s') =>
                    drop (s', n-1))

      fun map f s =
          lazy
          (fn () =>
                 (case front s of
                     Nil =>
                        Nil
                   | Cons (x, s') =>
                        Cons (f x, map f s')))

      fun app f s =
         (case front s of 
             Nil => ()
           | Cons (x, s') => (f x; app f s'))


      fun fold f x s =
         (case front s of
             Nil => x
           | Cons (h, t) =>
                f (h, Susp.delay (fn () => fold f x t)))

      fun toList s =
         (case front s of
             Nil => nil
           | Cons (h, t) => h :: toList t)

   end
