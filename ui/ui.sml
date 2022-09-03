
signature UI =
   sig

      val on : bool ref  (* is the UI active? *)
      val allowBeep : bool ref

      val message : string -> unit
      val beep : unit -> unit
      val cursorUp : int -> unit
      val ready : unit -> unit
      val readyPartial : unit -> unit

      datatype input =
         Line of string  (* nonempty, ends in newline *)

       | Rewind of int
       | Interject of string
       | ShowState
       | ChannelClosed

      val input : unit -> input

   end


(* Protocol between the REPL and the UI, if Repl.ui is set:

   REPL -> UI
   ----------
   ^A m <message> ^B : display message
   ^A b ^B           : sound bell
   ^A c <number> ^B  : move cursor up <number> lines
   ^A r ^B           : ready for input
   ^A p ^B           : ready for input (partial input)

   UI -> REPL
   ----------
   ^A <number> \n    : rewind to line <number>
   ^B <code> \n      : interject with code
   ^D \n             : show state

   (The reason UI -> REPL uses special codes, rather than just function calls,
   is to arrange not to screw up the REPL's idea of what line we're on.)
*)


structure UI :> UI =
   struct

      val on = ref false

      val allowBeep = ref true

      fun message str =
         if !on then
            (
            print "\^Am";
            print str;
            print "\^B"
            )
         else
            ()

      fun beep () =
         if !on andalso !allowBeep then
            print "\^Ab\^B"
         else
            ()

      fun cursorUp n =
         if !on then
            (
            print "\^Ac";
            print (Int.toString n);
            print "\^B"
            )
         else
            ()

      fun ready () =
         if !on then
            (
            print "\^Ar\^B";
            TextIO.flushOut TextIO.stdOut
            )
         else
            ()

      fun readyPartial () =
         if !on then
            (
            print "\^Ap\^B";
            TextIO.flushOut TextIO.stdOut
            )
         else
            ()

      datatype input =
         Line of string       (* nonempty, ends in newline *)

       | Rewind of int
       | Interject of string  (* nonempty, ends in newline *)
       | ShowState
       | ChannelClosed

      fun input () =
         (case TextIO.inputLine TextIO.stdIn of
             NONE => ChannelClosed

           | SOME str =>
                (case String.sub (str, 0) of
                    #"\^A" =>
                       Rewind (Option.getOpt (Int.fromString (String.extract (str, 1, NONE)), 0))

                  | #"\^B" =>
                       Interject (String.extract (str, 1, NONE))

                  | #"\^D" =>
                       ShowState

                  | _ => Line str))

   end
