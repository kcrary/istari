
(* This should work with older versions of SML/NJ (before version 110.89)
   in which Word is 31 bits and LargeWord is 32 bits.

   To match the IML basis, LargeWord must be 64 bits, despite being 32 bits
   in this version of the SML basis.

   Code mostly borrowed from convert-word-nj.sml.
*)

structure ConvertWord : CONVERT_WORD =
   struct

      type word = Word.word
      type word8 = Word8.word
      type word32 = Word32.word
      type word64 = Word64.word
      type wordlg = word64



      (* A lot of this could be simpler if LargeWord were the largest word size,
         like the basis documentation states.  Unfortunately, some 32-bit versions
         of SML/NJ supported 64-bit words, but didn't use Word64 for LargeWord.
         Also, Word64 didn't implement toLarge and fromLarge, which would have been
         useful.
      *)


      fun word8ToWord31 w = Word31.fromLarge (Word8.toLarge w)
      fun word8ToWord31X w = Word31.fromLarge (Word8.toLargeX w)
      fun word8ToWord32 w = Word32.fromLarge (Word8.toLarge w)
      fun word8ToWord32X w = Word32.fromLarge (Word8.toLargeX w)
      fun word8ToWord64 w = Word64.fromInt (Word8.toInt w)

      (* Work around SML/NJ bug. *)
      fun word8ToIntInf w = LargeInt.fromInt (Word8.toInt w)

      fun word8ToWord64X w =
         let
            val x = word8ToWord64 w
            
            open Word64
         in
            orb (x, andb (0wxffffffffffffff00, xorb (>> (andb (x, 0wx80), 0w7), 0w1) - 0w1))
         end

      fun word31ToWord8 w = Word8.fromLarge (Word31.toLarge w)
      fun word31ToWord32 w = Word32.fromLarge (Word31.toLarge w)
      fun word31ToWord32X w = Word32.fromLarge (Word31.toLargeX w)
      val word31ToIntInf = Word31.toLargeInt

      fun word31ToWord64 w = 
         (* probably inefficient, since LargeInt is infinite precision *)
         Word64.fromLargeInt (Word31.toLargeInt w)

      fun word31ToWord64X w =
         let
            val x = word31ToWord64 w
            
            open Word64
         in
            orb (x, andb (0wxFFFFFFFF80000000, xorb (>> (andb (x, 0wx40000000), 0w30), 0w1) - 0w1))
         end


      fun word32ToWord8 w = Word8.fromLarge (Word32.toLarge w)
      fun word32ToWord31 w = Word31.fromLarge (Word32.toLarge w)
      fun word32ToWord64 w = Word64.fromLargeInt (Word32.toLargeInt w)
      val word32ToIntInf = Word32.toLargeInt

      fun word32ToWord64X w =
         let
            val x = word32ToWord64 w
            
            open Word64
         in
            orb (x, andb (0wxFFFFFFFF00000000, xorb (>> (andb (x, 0wx80000000), 0w31), 0w1) - 0w1))
         end

      fun word64ToWord8 w = Word8.fromInt (Word64.toInt (Word64.andb (w, 0wxff)))
      fun word64ToWord31 w = Word31.fromLargeInt (Word64.toLargeInt (Word64.andb (w, 0wx7fffffff)))
      fun word64ToWord32 w = Word32.fromLargeInt (Word64.toLargeInt (Word64.andb (w, 0wxffffffff)))
      val word64ToIntInf = Word64.toLargeInt


      val intInfToWord8 = Word8.fromLargeInt
      val intInfToWord31 = Word31.fromLargeInt
      val intInfToWord32 = Word32.fromLargeInt
      val intInfToWord64 = Word64.fromLargeInt


      fun word32ToBytesB w =
         let
            val a = Word8Array.array (4, 0w0)
         in
            PackWord32Big.update (a, 0, Word32.toLargeWord w);
            Word8Array.vector a
         end

      fun word32ToBytesL w =
         let
            val a = Word8Array.array (4, 0w0)
         in
            PackWord32Little.update (a, 0, Word32.toLargeWord w);
            Word8Array.vector a
         end

      fun word31ToBytesB w =
         word32ToBytesB (word31ToWord32 w)

      fun word31ToBytesL w =
         word32ToBytesL (word31ToWord32 w)

      fun word64ToBytesB w =
         let
            val a = Word8Array.array (8, 0w0)
         in
            PackWord32Big.update (a, 0, Word32.toLarge (word64ToWord32 (Word64.>> (w, 0w32))));
            PackWord32Big.update (a, 1, Word32.toLarge (word64ToWord32 w));
            Word8Array.vector a
         end

      fun word64ToBytesL w =
         let
            val a = Word8Array.array (8, 0w0)
         in
            PackWord32Little.update (a, 1, Word32.toLarge (word64ToWord32 (Word64.>> (w, 0w32))));
            PackWord32Little.update (a, 0, Word32.toLarge (word64ToWord32 w));
            Word8Array.vector a
         end
         

      exception ConvertWord

      fun bytesToWord31B s =
         if Bytestring.size s <> 4 orelse Word8.> (Bytestring.sub (s, 0), 0wx7f) then
            raise ConvertWord
         else
            Word31.fromLarge (PackWord32Big.subVec (s, 0))

      fun bytesToWord31L s =
         if Bytestring.size s <> 4 orelse Word8.> (Bytestring.sub (s, 3), 0wx7f) then
            raise ConvertWord
         else
            Word31.fromLarge (PackWord32Little.subVec (s, 0))

      fun bytesToWord32B s =
         if Bytestring.size s <> 4 then
            raise ConvertWord
         else
            Word32.fromLarge (PackWord32Big.subVec (s, 0))

      fun bytesToWord32L s =
         if Bytestring.size s <> 4 then
            raise ConvertWord
         else
            Word32.fromLarge (PackWord32Little.subVec (s, 0))

      fun bytesToWord64B s =
         if Bytestring.size s <> 8 then
            raise ConvertWord
         else
            Word64.orb (Word64.<< (word32ToWord64 (Word32.fromLarge (PackWord32Big.subVec (s, 0))), 0w32),
                        word32ToWord64 (Word32.fromLarge (PackWord32Big.subVec (s, 1))))

      fun bytesToWord64L s =
         if Bytestring.size s <> 8 then
            raise ConvertWord
         else
            Word64.orb (Word64.<< (word32ToWord64 (Word32.fromLarge (PackWord32Little.subVec (s, 1))), 0w32),
                        word32ToWord64 (Word32.fromLarge (PackWord32Little.subVec (s, 0))))



      (* This stuff depends on the size of Word. *)

      val wordToWord8 = word31ToWord8
      fun wordToWord31 w = w
      val wordToWord32 = word31ToWord32
      val wordToWord32X = word31ToWord32X
      val wordToWord64 = word31ToWord64
      val wordToWord64X = word31ToWord64X
      val wordToIntInf = word31ToIntInf
      val wordToBytesB = word31ToBytesB
      val wordToBytesL = word31ToBytesL

      val word8ToWord = word8ToWord31
      val word8ToWordX = word8ToWord31X
      fun word31ToWord w = w
      fun word31ToWordX w = w
      val word32ToWord = word32ToWord31
      val word32ToWordX = word32ToWord31
      val word64ToWord = word64ToWord31
      val word64ToWordX = word64ToWord31
      val intInfToWord = intInfToWord31
      val bytesToWordB = bytesToWord31B
      val bytesToWordL = bytesToWord31L

      val wordLgToWord = word64ToWord
      val wordLgToWord8 = word64ToWord8
      val wordLgToWord32 = word64ToWord32
      val wordLgToWord32X = word64ToWord32
      fun wordLgToWord64 w = w
      fun wordLgToWord64X w = w
      val wordLgToIntInf = word64ToIntInf
      val wordLgToBytesB = word64ToBytesB
      val wordLgToBytesL = word64ToBytesL

      val wordToWordLg = wordToWord64
      val word8ToWordLg = word8ToWord64
      val word8ToWordLgX = word8ToWord64X
      val word32ToWordLg = word32ToWord64
      val word32ToWordLgX = word32ToWord64X
      fun word64ToWordLg w = w
      fun word64ToWordLgX w = w
      val intInfToWordLg = intInfToWord64
      val bytesToWordLgB = bytesToWord64B
      val bytesToWordLgL = bytesToWord64L


      (* Word31 is unsupported *)

      type word31 = unit

      fun wordToWord31 w = ()
      fun wordLgToWord31 w = ()
      fun word8ToWord31 w = ()
      fun word8ToWord31X w = ()
      fun word32ToWord31 w = ()
      fun word64ToWord31 w = ()
      fun intInfToWord31 _ = ()

      fun bytesToWord31B s = ()
      fun bytesToWord31L s = ()

      fun word31ToWord w = 0w0 : Word.word
      fun word31ToWordX w = 0w0 : Word.word
      fun word31ToWordLg w = 0w0 : Word64.word
      fun word31ToWordLgX w = 0w0 : Word64.word
      fun word31ToWord8 w = 0w0 : Word8.word
      fun word31ToWord32 w = 0w0 : Word32.word
      fun word31ToWord32X w = 0w0 : Word32.word
      fun word31ToWord64 w = 0w0 : Word64.word
      fun word31ToWord64X w = 0w0 : Word64.word
      fun word31ToIntInf w = 0 : IntInf.int

      fun word31ToBytesB w = Bytestring.null
      fun word31ToBytesL w = Bytestring.null

   end
