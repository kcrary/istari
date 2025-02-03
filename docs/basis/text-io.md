# TextIO

    signature TEXT_IO =
       sig
    
          type instream
          type outstream
    
          val input1 : instream -> char option
          val inputN : instream -> int -> string
          val inputLine : instream -> string option
    
          val output1 : outstream -> char -> unit
          val output : outstream -> string -> unit
          val flushOut : outstream -> unit
    
          val openIn : string -> instream
          val closeIn : instream -> unit
          val openOut : string -> outstream
          val openAppend : string -> outstream
          val closeOut : outstream -> unit
    
          val stdIn : instream
          val stdOut : outstream
          val stdErr : outstream
    
          val print : string -> unit
    
       end

    structure TextIO : TEXT_IO

File names are always represented as [Unix
paths](path.html#windows-paths-as-unix-paths), regardless of the
platform.
