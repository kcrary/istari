
signature MEMORY =
   sig

      (* (a, b) where b is the line of interest, and a is the first line of any blank space
         that precedes it.
      *)
      type location = int * int


      (* Create a tentative checkpoint at the current location.
         A tentative checkpoint carries no rewind data and is overwritten by the
         next call to setLocation.
      *)
      val setLocation : location -> unit


      (* Obtains a checkpoint.  Saves it at the current tentative checkpoint, making it
         non-tentative.  Ignored if the last checkpoint is not tentative.
      *)
      val checkpoint : unit -> unit


      (* Make the last checkpoint persistent. *)
      val saveLast : unit -> unit

      
      (* Restores the most recent checkpoint such that its location is (a, b) and
         a <= n.  Returns its location.  If the last such non-persistent checkpoint
         fails, then restores the most recent such persistent checkpoint instead.
      *)
      val rewind : int -> location


      (* Restores the last checkpoint.  Returns its location. *)
      val rewindLast : unit -> location


      (* Callback for Memory to capture the state.  The first () argument captures
         the state; the second restores it.
      *)
      val rewindHook : (unit -> unit -> bool) ref


      (* Callback for Memory to reset to the initial state. *)
      val resetHook : (unit -> unit) ref

   end


structure NullMemory :> MEMORY =
   struct

      type location = int * int

      fun setLocation _ = ()
      fun checkpoint () = ()
      fun saveLast () = ()
      fun rewind _ = (1, 0)
      fun rewindLast () = (1, 0)

      val rewindHook = ref (fn () => fn () => false)
      val resetHook = ref (fn () => ())

   end


structure Memory :> MEMORY =
   struct

      type location = int * int

      val rewindHook = ref (fn () => fn () => false)
      val resetHook = ref (fn () => ())


      val historySize = 200
      val maxInt = Option.valOf Int.maxInt
      fun noop () = true
      val blank = (maxInt, maxInt, false, noop)

      (* each entry is (a, b, tentative, the_checkpoint) *)
      val history : (int * int * bool * (unit -> bool)) Array.array =
         Array.array (historySize, blank)

      (* cursor points to last entry *)
      val cursor = ref 0

      val persistentHistory : (int * int * (unit -> bool)) list ref = ref []


      fun setLocation (a, b) =
         let
            val (_, _, tentative, _) = Array.sub (history, !cursor)
         in
            if tentative then
               ()
            else
               cursor := (!cursor + 1) mod historySize;

            Array.update (history, !cursor, (a, b, true, noop))
         end


      fun checkpoint () =
         let
            val (a, b, tentative, _) = Array.sub (history, !cursor)
         in
            if tentative then
               Array.update (history, !cursor, (a, b, false, !rewindHook ()))
            else
               ()
         end


      fun saveLast () =
         let
            val (a, b, _, ckpt) = Array.sub (history, !cursor)
         in
            if a = maxInt then
               ()
            else
               persistentHistory := (a, b, ckpt) :: !persistentHistory
         end
               

      fun eraseRingbuffer i =
         if i >= historySize then
            ()
         else
            (
            Array.update (history, i, blank);
            eraseRingbuffer (i+1)
            )


      fun tidyPersistentLoop n l =
         (case l of
             [] =>
                persistentHistory := []

           | (a, _, _) :: rest =>
                if n <= a then
                   tidyPersistentLoop n rest
                else
                   persistentHistory := l)
            

      fun rewind n =
         let
            fun persistentLoop l =
               (case l of
                   [] =>
                      (
                      persistentHistory := [];
                      !resetHook ();
                      (1, 1)
                      )

                 | (a, b, ckpt) :: rest =>
                      if a <= n then
                         (
                         ckpt ();  (* ignore bool result *)
                         persistentHistory := rest;
                         (a, b)
                         )
                      else
                         persistentLoop rest)

            fun loop i =
               let
                  val (a, b, _, ckpt) = Array.sub (history, i)
               in
                  if a <= n then
                     if ckpt () then
                        (* The rewind succeeded. *)
                        (
                        Array.update (history, i, blank);
                        cursor := (i - 1) mod historySize;
                        tidyPersistentLoop a (!persistentHistory);
                        (a, b)
                        )
                     else
                        (* The rewind failed.  Nothing else in the ring buffer
                           will be any better, so erase it and resort to the
                           persistent history.
                        *)
                        (
                        eraseRingbuffer 0;
                        persistentLoop (!persistentHistory)
                        )
                  else if a = maxInt then
                     (* Exhausted the ring buffer. *)
                     persistentLoop (!persistentHistory)
                  else
                     (
                     Array.update (history, i, blank);
                     loop ((i - 1) mod historySize)
                     )
               end
         in
            loop (!cursor)
         end
   

      fun rewindLast () = rewind maxInt

   end
