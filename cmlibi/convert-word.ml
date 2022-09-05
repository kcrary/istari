
open Convert_word_sig ;;
open Bytestring ;;

module ConvertWord : CONVERT_WORD
                     with type word = Word62.word
                     with type wordlg = Word64.word
                     with type word8 = Word8.word
                     with type word32 = Word32.word
                     with type word64 = Word64.word
   =
   struct

      type word = Word62.word
      type wordlg = Word64.word
      type word8 = Word8.word
      type word32 = Word32.word
      type word64 = Word64.word

      type word31 = unit

      let word8ToWord32 w = Word32.fromLargeWord (Word8.toLargeWord w)
      let word8ToWord32X w = Word32.fromLargeWord (Word8.toLargeWordX w)
      let word8ToWord64 w = Word64.fromLargeWord (Word8.toLargeWord w)
      let word8ToWord64X w = Word64.fromLargeWord (Word8.toLargeWordX w)
      let word8ToIntInf w = Word8.toLargeInt w

      let word32ToWord8 w = Word8.fromLargeWord (Word32.toLargeWord w)
      let word32ToWord64 w = Word64.fromLargeWord (Word32.toLargeWord w)
      let word32ToWord64X w = Word64.fromLargeWord (Word32.toLargeWordX w)
      let word32ToIntInf = Word32.toLargeInt

      let word64ToWord8 w = Word8.fromLargeWord (Word64.toLargeWord w)
      let word64ToWord32 w = Word32.fromLargeWord (Word64.toLargeWord w)
      let word64ToIntInf = Word64.toLargeInt

      let intInfToWord8 = Word8.fromLargeInt
      let intInfToWord32 = Word32.fromLargeInt
      let intInfToWord64 = Word64.fromLargeInt

      let rec conv w n acc =
         if n = 0 then
            acc
         else
            conv
               (Int64.shift_right_logical w 8)
               (n-1)
               (Word8.fromInt (Int64.to_int (Int64.logand w 255L)) :: acc)
      
      let word32ToBytesB w =
         Bytestring.implode (conv (Word32.toInt64 w) 4 [])

      let word32ToBytesL w =
         Bytestring.implode (List.rev (conv (Word32.toInt64 w) 4 []))

      let word64ToBytesB w =
         Bytestring.implode (conv (Word64.toInt64 w) 8 [])

      let word64ToBytesL w =
         Bytestring.implode (List.rev (conv (Word64.toInt64 w) 8 []))


      exception ConvertWord

      let rec count f i j inc acc =
         if i = j then
            acc
         else
            count f (i + inc) j inc (f i acc)
         

      let zero32 = Word32.fromInt 0

      let rec bytesToWord32B s =
         if Bytestring.size s <> 4 then
            raise ConvertWord
         else
            count
               (fun i acc -> 
                   Word32.orb
                      (Word32.shl acc 8)
                      (Word32.fromInt (Word8.toInt (Bytestring.sub (s, i)))))
               0 4 1 zero32

      let rec bytesToWord32L s =
         if Bytestring.size s <> 4 then
            raise ConvertWord
         else
            count
               (fun i acc -> 
                   Word32.orb
                      (Word32.shl acc 8)
                      (Word32.fromInt (Word8.toInt (Bytestring.sub (s, i-1)))))
               4 0 (-1) zero32

      let zero64 = Word64.fromInt 0

      let rec bytesToWord64B s =
         if Bytestring.size s <> 8 then
            raise ConvertWord
         else
            count
               (fun i acc -> 
                   Word64.orb
                      (Word64.shl acc 8)
                      (Word8.toLargeWord (Bytestring.sub (s, i))))
               0 4 1 zero64

      let rec bytesToWord64L s =
         if Bytestring.size s <> 8 then
            raise ConvertWord
         else
            count
               (fun i acc -> 
                   Word64.orb
                      (Word64.shl acc 8)
                      (Word8.toLargeWord (Bytestring.sub (s, i-1))))
               4 0 (-1) zero64

            



      (* This stuff depends on the size of LargeWord. *)

      let wordToWord8 w = Word8.fromLargeWord (Word62.toLargeWord w)
      let wordToWord32 w = Word32.fromLargeWord (Word62.toLargeWord w)
      let wordToWord32X w = Word32.fromLargeWord (Word62.toLargeWordX w)
      let wordToWord64 w = Word64.fromLargeWord (Word62.toLargeWord w)
      let wordToWord64X w = Word64.fromLargeWord (Word62.toLargeWordX w)
      let wordToIntInf = Word62.toLargeInt
      let wordToBytesB w = word32ToBytesB (wordToWord32 w)
      let wordToBytesL w = word32ToBytesL (wordToWord32 w)

      let word8ToWord w = Word62.fromLargeWord (Word8.toLargeWord w)
      let word8ToWordX w = Word62.fromLargeWord (Word8.toLargeWordX w)
      let word32ToWord w = Word62.fromLargeWord (Word32.toLargeWord w)
      let word32ToWordX w = Word62.fromLargeWord (Word32.toLargeWordX w)
      let word64ToWord w = Word62.fromLargeWord (Word64.toLargeWord w)
      let word64ToWordX w = Word62.fromLargeWord (Word64.toLargeWordX w)
      let intInfToWord = Word62.fromLargeInt
      let bytesToWordB w = word32ToWord (bytesToWord32B w)
      let bytesToWordL w = word32ToWord (bytesToWord32L w)

      let wordLgToWord = Word62.fromLargeWord
      let wordLgToWord8 = Word8.fromLargeWord
      let wordLgToWord32 w = Word32.fromLargeWord w
      let wordLgToWord32X w = Word32.fromLargeWord w
      let wordLgToWord64 w = w
      let wordLgToWord64X w = w
      let wordLgToIntInf = Word64.toLargeInt
      let wordLgToBytesB w = word64ToBytesB w
      let wordLgToBytesL w = word64ToBytesL w

      let wordToWordLg = Word62.toLargeWord
      let word8ToWordLg = Word8.toLargeWord
      let word8ToWordLgX = Word8.toLargeWordX
      let word32ToWordLg = Word32.toLargeWord
      let word32ToWordLgX = Word32.toLargeWordX
      let word64ToWordLg w = w
      let word64ToWordLgX w = w
      let intInfToWordLg = Word64.fromLargeInt
      let bytesToWordLgB w = bytesToWord64B w
      let bytesToWordLgL w = bytesToWord64L w

      let wordToWord31 w = ()
      let wordLgToWord31 w = ()
      let word8ToWord31 w = ()
      let word8ToWord31X w = ()
      let word32ToWord31 w = ()
      let word64ToWord31 w = ()
      let intInfToWord31 _ = ()

      let bytesToWord31B s = ()
      let bytesToWord31SB s = ()
      let bytesToWord31L s = ()
      let bytesToWord31SL s = ()

      let word31ToWord w = Word62.fromInt 0
      let word31ToWordX w = Word62.fromInt 0
      let word31ToWordLg w = Word64.fromInt 0
      let word31ToWordLgX w = Word64.fromInt 0
      let word31ToWord8 w = Word8.fromInt 0
      let word31ToWord32 w = Word32.fromInt 0
      let word31ToWord32X w = Word32.fromInt 0
      let word31ToWord64 w = Word64.fromInt 0
      let word31ToWord64X w = Word64.fromInt 0
      let word31ToIntInf w = Basis.IntInf.fromInt 0

      let word31ToBytesB w = Bytestring.null
      let word31ToBytesL w = Bytestring.null

   end
