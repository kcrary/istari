
signature MEMORY =
   sig

      val advanceLine : unit -> unit

      (* Indicates the beginning of (possibly empty) dead space. *)
      val deadspace : unit -> unit

      (* Asks the Prover for a checkpoint.  Saves it in the ring buffer. *)
      val checkpoint : unit -> unit

      (* Is passed a checkpoint.  Saves it permanently (until rewound). *)
      val persistentCheckpoint : (unit -> unit) -> unit

      (* Must follow checkpoint (not persistentCheckpoint).  Removes the checkpoint,
         adjust the current line to the starting line, and moves the cursor up, but
         does not rewind the state.
      *)
      val uncheckpoint : unit -> unit

      (* Removes the last checkpoint, and adjusts the curent line up one.  Does not move
         the cursor or rewind the state.  For undoing commands sent surreptitiously to the
         Repl.
      *)
      val undo : unit -> unit

      (* Discards the last checkpoint.  Does nothing else. *)
      val discard : unit -> unit

      (* Rewinds the state to the last checkpoint no later than !currentline - n.
         Resets the beginning of deadspace to what it was then.
      *)
      val rewind : int -> unit

      (* First () argument captures the state; second restores it. *)
      val rewindHook : (unit -> unit -> bool) ref

      (* Resets to the initial state. *)
      val resetHook : (unit -> unit) ref

   end


functor MemoryFun (val withHandler : 'a -> (unit -> 'a) -> 'a)
   :> MEMORY
   =
   struct

      val currentLine = ref 0
      val deadspaceLine = ref 0
      val startingDeadLine = ref 0  (* deadspace line of the last checkpoint *)
      val startingLine = ref 0      (* line of the last checkpoint *)

      val historySize = 200
      val maxint = Option.valOf Int.maxInt
      val blank = (maxint, maxint, (fn () => false))

      (* first int: start of dead space, second int: start of content *)
      val history : (int * int * (unit -> bool)) Array.array =
         Array.array (historySize, blank)

      (* cursor points to next checkpoint *)
      val cursor = ref 0

      val ancientHistory : (int * int * (unit -> unit)) list ref = ref []

      val rewindHook = ref (fn () => fn () => false)
      val resetHook = ref (fn () => ())


      fun advanceLine () =
         currentLine := !currentLine + 1

      fun deadspace () =
         deadspaceLine := !currentLine

      fun checkpoint () =
         (
         startingDeadLine := !deadspaceLine;
         startingLine := !currentLine;
         Array.update (history, !cursor, (!deadspaceLine, !currentLine, !rewindHook ()));
         cursor := (!cursor + 1) mod historySize
         )

      fun persistentCheckpoint f =
         (
         ancientHistory :=
         (!startingDeadLine, !startingLine, f) :: !ancientHistory
         )

      fun discard () =
         (
         cursor := (!cursor - 1) mod historySize;
         Array.update (history, !cursor, blank)
         )

      fun uncheckpoint () =
         (
         UI.cursorUp (!currentLine - !startingLine);
         currentLine := !startingLine;
         discard ()
         )

      fun undo () =
         (
         currentLine := !currentLine - 1;
         discard ()
         )

      fun memoryHole () =
         let
            fun loop i =
               if i = historySize then
                  ()
               else
                  (
                  Array.update (history, i, blank);
                  loop (i+1)
                  )
         in
            loop 0
         end
         
      fun rewind n =
         let
            val curr = !currentLine

            (* don't go negative, even if the user adds lines top of the file *)
            val target = Int.max (curr - n, 0)

            fun ancientLoop l =
               (case l of
                   [] =>
                      (
                      ancientHistory := [];
                      deadspaceLine := 0;
                      currentLine := 0;
                      UI.cursorUp curr;
                      !resetHook ()
                      )

                 |  (deadline, line, f) :: rest =>
                      if deadline <= target then
                         let
                            val actual = Int.min (target, line)
                         in
                            ancientHistory := rest;
                            deadspaceLine := deadline;
                            currentLine := actual;
                            UI.cursorUp (curr - actual);
                            withHandler () f
                         end
                      else
                         ancientLoop rest)

            fun tidyAncientLoop actual l =
               (case l of
                   [] =>
                      ancientHistory := []

                 | (_, line, _) :: rest =>
                      if actual <= line then
                         tidyAncientLoop actual rest
                      else
                         ancientHistory := l)

            fun loop first i =
               let
                  val (deadline, line, f) = Array.sub (history, i)
               in
                  if deadline <= target then
                     if first orelse withHandler false f then
                        (* the rewind succeeded, if attempted *)
                        let
                           val actual = Int.min (target, line)
                        in
                           Array.update (history, i, blank);
                           cursor := i;
                           tidyAncientLoop actual (!ancientHistory);
                           deadspaceLine := deadline;
                           currentLine := actual;
                           UI.cursorUp (curr - actual)
                        end
                     else
                        (* Cannot be rewound.  Empty the ring buffer (nothing else in it
                           will be any better), and look for a persistent checkpoint.
                        *)
                        (
                        memoryHole ();
                        ancientLoop (!ancientHistory)
                        )
                  else if line = maxint then
                     (
                     ancientLoop (!ancientHistory)
                     )
                  else
                     (
                     Array.update (history, i, blank);
                     loop false ((i - 1) mod historySize)
                     )
               end
         in
            loop true ((!cursor - 1) mod historySize)
         end

   end
