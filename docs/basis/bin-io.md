# BinIO

    signature BIN_IO =
       sig
    
          type instream
          type outstream
    
          val input1 : instream -> Word8.word option
    
          val output1 : outstream -> Word8.word -> unit
          val flushOut : outstream -> unit
    
          val openIn : string -> instream
          val closeIn : instream -> unit
          val openOut : string -> outstream
          val openAppend : string -> outstream
          val closeOut : outstream -> unit
    
       end
    
    structure BinIO : BIN_IO
