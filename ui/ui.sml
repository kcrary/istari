
(* Protocol between the UI and the REPL:

   REPL -> UI
   ----------
   ^A m <message> ^B : display message
   ^A b ^B           : sound bell
   ^A c <number> ^B  : move cursor to indicated line
   ^A r ^B           : set glyph to ready
   ^A p ^B           : set glyph to ready-partial
   ^A w ^B           : set glyph to working
   ^A f ^B           : flush
   ^A i <text> ^B    : insert text into buffer

   UI -> REPL
   ----------
   ^A <number> \n    : rewind to indicated line
   ^B <code> \n      : interject with code
   ^E \n             : done sending
   ^F \n             : acknowledge flush

   The UI always ends every send with an escape sequence, so that is the only
   time the Repl can block.

*)


signature UI =
   sig
      
      val allowBeep : bool ref

      (* actions to make the UI do something *)

      val output : string -> unit       (* ordinary output *)
      val message : string -> unit      (* show message in the echo area *)
      val beep : unit -> unit           (* sound the bell if allowBeep is set *)
      val moveCursor : int -> unit      (* move the cursor to the indicated line *)
      val ready : unit -> unit          (* set the cursor glyph *)
      val readyPartial : unit -> unit   (* set the cursor glyph *)
      val working : unit -> unit        (* set the cursor glyph *)
      val flush : unit -> unit          (* induce the UI to send FlushAck *)


      (* input message received from the UI *)

      datatype input =
         Line of string          (* nonempty, ends in newline *)
       | Interjection of string  (* nonempty, ends in newline *)
       | Ready                   (* ask for acknowledgement when ready *)
       | FlushAck                (* acknowledge a flush request *)
       | Rewind of int           (* rewind to the indicated line *)
       | ChannelClosed

      val input : unit -> input

   end


structure NullUI :> UI =
   struct

      val allowBeep = ref true

      fun output str = print str

      fun message _ = ()

      fun beep () = ()

      fun moveCursor _ = ()

      fun ready () = ()

      fun readyPartial () = ()

      fun working () = ()

      fun flush () = ()

      datatype input =
         Line of string
       | Interjection of string
       | Ready
       | FlushAck
       | Rewind of int
       | ChannelClosed

      fun input () = 
         (case TextIO.inputLine TextIO.stdIn of
             NONE => ChannelClosed

           | SOME str => Line str)

   end


structure UI :> UI =
   struct

      val allowBeep = ref true

      fun output str = print str

      fun message str =
         (
         print "\^Am";
         print str;
         print "\^B"
         )

      fun beep () =
         if !allowBeep then
            print "\^Ab\^B"
         else
            ()

      fun moveCursor n =
         (
         print "\^Ac";
         print (Int.toString n);
         print "\^B"
         )

      fun ready () =
         (
         print "\^Ar\^B";
         TextIO.flushOut TextIO.stdOut
         )

      fun readyPartial () =
         (
         print "\^Ap\^B";
         TextIO.flushOut TextIO.stdOut
         )

      fun working () =
         (
         print "\^Aw\^B";
         TextIO.flushOut TextIO.stdOut
         )

      fun flush () =
         (
         print "\^Af\^B";
         TextIO.flushOut TextIO.stdOut
         )

      datatype input =
         Line of string
       | Interjection of string
       | Ready
       | FlushAck
       | Rewind of int
       | ChannelClosed

      fun input () =
         (case TextIO.inputLine TextIO.stdIn of
             NONE => ChannelClosed

           | SOME str =>
                (case String.sub (str, 0) of
                    #"\^A" =>
                       Rewind (Option.getOpt (Int.fromString (String.extract (str, 1, NONE)), 0))

                  | #"\^B" =>
                       Interjection (String.extract (str, 1, NONE))

                  | #"\^E" =>
                       Ready

                  | #"\^F" =>
                       FlushAck

                  | _ => Line str))

   end
