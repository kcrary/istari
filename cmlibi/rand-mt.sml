
(* Mersenne Twister algorithm *)

(* Just as the one in CMLIB, except it does not automatically seed using the time. *)

structure MTRand32 :> RAND32 where type seed = Word32.word =
   struct

      structure A = Array
      structure W = Word32
      type word32 = Word32.word

      val w0 = Word32.fromInt 0
      val w1 = Word32.fromInt 1

      val degree = 624
      val middle = 397

      val twist : word32 = Word32.fromLargeInt 0x9908b0dfI
      val tempermask1 : word32 = Word32.fromLargeInt 0x9d2c5680I
      val tempermask2 : word32 = Word32.fromLargeInt 0xefc60000I

      val indexr = ref 0
      val mt : word32 A.array = Array.array (degree, w0)

      type seed = word32

      val number = Word32.fromLargeInt 1812433253I
      val w8000 = Word32.fromLargeInt 0x80000000I
      val w7fff = Word32.fromLargeInt 0x7fffffffI

      fun reseed seed =
         let
            fun initLoop i =
               if i >= degree then
                  ()
               else
                  (
                  A.update (mt, i,
                            W.+ (W.* (number, W.xorb (A.sub (mt, i-1), W.>> (A.sub (mt, i-1), 0w30))),
                                 Word32.fromInt i));
                  initLoop (i+1)
                  )
         in
            A.update (mt, 0, seed);
            initLoop 1;
            indexr := 0
         end

      val () = reseed w0

      fun generateRaw i =
         if i >= degree then
            ()
         else
            let
               val y =
                  W.orb (W.andb (A.sub (mt, i), w8000),
                         W.andb (A.sub (mt, (i+1) mod degree), w7fff))

               val z =
                  W.xorb (A.sub (mt, (i + middle) mod degree), W.>> (y, 0w1))
            in
               if W.andb (y, w1) = w0 then
                  A.update (mt, i, z)
               else
                  A.update (mt, i, W.xorb (z, twist));

               generateRaw (i+1)
            end
         
      fun randWord32 () =
         let
            val i = !indexr
            val () = indexr := (i + 1) mod degree

            val () =
               if i = 0 then
                  generateRaw 0
               else
                  ()
            
            val y = A.sub (mt, i)
            val y = W.xorb (y, W.>> (y, 0w11))
            val y = W.xorb (y, W.andb (W.<< (y, 0w7), tempermask1))
            val y = W.xorb (y, W.andb (W.<< (y, 0w15), tempermask2))
            val y = W.xorb (y, W.>> (y, 0w18))
         in
            y
         end

   end

structure MTRand = RandFromRand32 (structure Rand32 = MTRand32)
