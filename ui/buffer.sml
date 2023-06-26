
signature BUFFER =
   sig

      exception Interjection of char Stream.stream
      exception Rewind of int
      exception Exit

      (* new a b

         a: the beginning of the preceding gap (possibly empty)
         b: the line number we're starting on
      *)
      val new : int -> int -> char Stream.stream

      (* Notify buffer that we've completed a directive.  For signal to work properly,
         the users of the stream should not consume any more of the stream than necessary.
      *)
      val signal : unit -> unit

      val onReadyHook : (unit -> unit) ref

   end


functor UIBuffer (structure UI : UI
                  structure Memory : MEMORY) :> BUFFER =
   struct

      exception Interjection of char Stream.stream
      exception Rewind of int
      exception Exit


      (* We don't want the UI to block while we process large inputs, so we buffer them. *)
      val buffered : UI.input IQueue.iqueue = IQueue.iqueue ()

      fun flushLoop () =
         (case UI.input () of
             UI.FlushAck => ()

           | UI.ChannelClosed => raise Exit

           | _ => flushLoop ())

      fun flush () =
         (
         IQueue.reset buffered;
         UI.flush ();
         flushLoop ()
         )



      fun bufferLoop () =
         let
            val inp = UI.input ()
         in
            IQueue.insert buffered inp;

            (case inp of
                UI.Line _ => bufferLoop ()

              | _ => ())
         end

      fun rawInput () =
         if IQueue.isEmpty buffered then
            (
            bufferLoop ();
            rawInput ()
            )
         else
            IQueue.remove buffered



      val onReadyHook = ref (fn () => ())

      val theRow = ref 0
      val complete = ref true
      val gapStart : int option ref = ref NONE  (* 'a' from Memory *)

      fun input () =
         (case rawInput () of
             UI.Line str => str

           | UI.Interjection str =>
                raise (Interjection (Stream.fromString str))

           | UI.Ready =>
                (
                !onReadyHook ();

                if !complete then
                   UI.ready ()
                else
                   UI.readyPartial ();

                input ()
                )

           | UI.FlushAck =>
                raise (Fail "unexpected flush acknowledgement")

           | UI.Rewind n =>
                raise (Rewind n)

           | UI.ChannelClosed =>
                raise Exit)


      fun signal () =
         (
         complete := true;
         gapStart := NONE
         )


      fun inputLoop () =
         let
            val row = !theRow

            val () =
               (* if we're still in blank space, set/update the lightweight checkpoint *)
               if !complete then
                  (case !gapStart of
                      NONE =>
                         (
                         gapStart := SOME row;
                         Memory.setLocation (row, row)
                         )
   
                    | SOME gs =>
                         Memory.setLocation (gs, row))
               else
                  ()

            val str = input ()
            val row' = row + 1;
         in
            theRow := row';
            UI.working ();
            UI.moveCursor row';
            stringLoop str 0 (String.size str)
         end


      and stringLoop str i j =
         if i >= j then
            inputLoop ()
         else
            let
               val ch = String.sub (str, i)
            in
               if Char.isSpace ch then
                  ()
               else
                  complete := false;

               Stream.Cons (ch, Stream.lazy (fn () => stringLoop str (i+1) j))
            end


      fun new a b =
         (
         flush ();
         UI.ready ();
         Memory.setLocation (a, b);
         theRow := b;
         complete := true;
         gapStart := SOME a;
         Stream.lazy inputLoop
         )

   end


structure SimpleBuffer :> BUFFER =
   struct

      exception Interjection of char Stream.stream
      exception Rewind of int
      exception Exit


      val complete = ref true


      fun signal () = complete := true


      val onReadyHook = ref (fn () => ())


      val primaryPrompt = "% "
      val secondaryPrompt = "= "


      fun input () =
         (
         if !complete then
            print primaryPrompt
         else
            print secondaryPrompt;

         (case TextIO.inputLine TextIO.stdIn of
             NONE => raise Exit

           | SOME str => str)
         )
         

      fun inputLoop () =
         let
            val str = input ()
         in
            stringLoop str 0 (String.size str)
         end


      and stringLoop str i j =
         if i >= j then
            inputLoop ()
         else
            let
               val ch = String.sub (str, i)
            in
               if Char.isSpace ch then
                  ()
               else
                  complete := false;

               Stream.Cons (ch, Stream.lazy (fn () => stringLoop str (i+1) j))
            end


      fun new _ _ =
         (
         complete := true;
         Stream.lazy (fn () => inputLoop ())
         )

   end
