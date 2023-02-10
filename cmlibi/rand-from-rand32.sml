
functor RandFromRand32 (structure Rand32 : RAND32)
   :>
   RAND
   where type seed = Rand32.seed
   =
   struct

      open Rand32

      val i0 = IntInf.fromInt 0
      val i1 = IntInf.fromInt 1

      val w0 = Word32.fromInt 0
      val w1 = Word32.fromInt 1

      fun randBool () = Word32.andb (randWord32 (), w1) = w0

      fun randWord8 () = ConvertWord.word32ToWord8 (randWord32 ())

      fun randBits bits =
         let
            fun loop acc n =
               if n = 0 then
                  acc
               else
                  IntInf.orb (IntInf.<< (acc, 0w32), ConvertWord.word32ToIntInf (randWord32 ()))

            val words = bits div 32
            val extra = bits mod 32
         in
            if extra = 0 then
               loop i0 words
            else
               loop 
               (ConvertWord.word32ToIntInf
                   (Word32.andb (randWord32 (), Word32.- (Word32.<< (w1, Word.fromInt extra), w1))))
               words
         end

      fun randIntInf max =
         if IntInf.<= (max, i0) then
            raise (General.Invalid "randIntInf")
         else
            let
               val x = randBits (IntInf.log2 max + 1)
            in
               if IntInf.>= (x, max) then
                  randIntInf max
               else
                  x
            end

      (* If we knew the size of an int, we could hardcode something better than this. *)
      fun randInt max =
         IntInf.toInt (randIntInf (IntInf.fromInt max))

   end
