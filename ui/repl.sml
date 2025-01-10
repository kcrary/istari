
signature REPL_HOOKS =
   sig

      (* Callback to be called on uncaught exceptions. *)
      val exceptionHandler : (exn -> bool) ref

      (* Callback to capture the prover's state.  The first () argument captures the
         state; the second restores it.
      *)
      val checkpoint : (unit -> unit -> bool) ref

      (* Callback to reset the prover to its initial state. *)
      val reset : (unit -> unit) ref

      (* Callbacks to display certain information. *)
      val onReady : (unit -> unit) ref
      val onRewind : (unit -> unit) ref

   end


(* This operations are made available to the user. *)
signature CTRL =
   sig

      val use : string -> unit      (* use an IML file *)
      val exit : unit -> 'a

      val pwd : unit -> string
      val cd : string -> unit

      val printDepth : int ref
      val printLength : int ref
      val stringLength : int ref
      val gcMessages : bool -> unit
      val allowBeep : bool ref
      val backtrace : bool ref

   end


signature REPL =
   sig

      val run : unit -> unit

      (* load the indicated file, as it it were being used, true result indicates success *)
      val batch : string -> bool

      structure Hooks : REPL_HOOKS

   end


signature RECOVER_REPL =
   sig

      (* Recover from an interruption. *)
      val recover : unit -> unit

   end


functor ReplFun (structure Platform : PLATFORM)
   :>
   sig
      structure Repl : REPL
      structure Ctrl : CTRL
      structure RecoverRepl : RECOVER_REPL
      structure RecoverReplInside : RECOVER_REPL
   end
   =
   struct

      (* constants to conform to Emacs's conventions *)
      val firstRow = 1
      val firstCol = 0
      val interjectionRow = 0  (* basically arbitrary *)


      exception Exit = Buffer.Exit
      exception Exception
      exception SilentException

      val theTempFilename = ref "/dev/null"


      (* ReplFun's caller fills these in. *)
      structure Hooks =
         struct

            val exceptionHandler : (exn -> bool) ref = ref (fn _ => false)
            val checkpoint = Memory.rewindHook
            val reset = Memory.resetHook
            val onReady = ref (fn () => ())
            val onRewind = ref (fn () => ())

         end



      (* Miscellany *)

      val backtrace = ref false

      fun displayUncaughtException exn =
         (
         print "Uncaught exception: ";
         print (exnMessage exn);
         print "\n";

         if !backtrace then
            (case Platform.exnHistory exn of
                [] => ()
              | l => 
                   (
                   print "\nBacktrace:\n";
                   app (fn str => (print str; print "\n")) l
                   ))
         else
            ()
         )

      fun onReady () =
         (!Hooks.onReady ()
          handle exn =>
             (
             displayUncaughtException exn;
             print "\nFatal error: uncaught exception raised in ready information.\n";
             raise Exit
             ))

      fun onRewind () =
         (!Hooks.onRewind ()
          handle exn =>
             (
             displayUncaughtException exn;
             print "\nFatal error: uncaught exception raised in rewind information.\n";
             raise Exit
             ))

      val () = Buffer.onReadyHook := onReady



      (* Executing IML *)

      fun showIppError sourcename source msg place =
         if Error.isUnknown place then
            (case sourcename of
                NONE =>
                   (
                   print "\nError: ";
                   print msg
                   )

              | SOME name =>
                   (
                   print "\n";
                   print name;
                   print ":? Error: ";
                   print msg;
                   print "\n"
                   ))
         else
            let
               val span as ((row1, col1), (row2, col2)) =
                  (case place of
                      Error.SPAN span => span

                    | Error.POS pos => (pos, pos)

                    | Error.UNKNOWN => raise (Fail "impossible"))
            in
               print "\n";

               (case sourcename of
                   NONE => ()
                 | SOME name =>
                      (
                      print name;
                      print ":"
                      ));
   
               print (Int.toString row1);
               print ".";
               print (Int.toString col1);
               print "-";
               print (Int.toString row2);
               print ".";
               print (Int.toString col2);
               print " Error: ";
               print msg;
               print "\n";
   
               ShowContext.display source span
            end
            

      (* This will also handle lexing errors that arise in s. *)
      fun parse sourcename source s =
         Incremental.parse s
         handle
            Error.Error (msg, place) =>
               (
               showIppError sourcename source msg place;
               raise Exception
               )
               

      fun handleExn exn =
         (case exn of
             Exit => raise Exit

           | SilentException => raise SilentException

           | _ =>
                (
                onReady ();
                print "\n";

                if !Hooks.exceptionHandler exn then
                   ()
                else
                   displayUncaughtException exn;

                Incremental.undo ();
                raise Exception
                ))

      
      (* source is the full character stream; p is drawn from the middle of it *)
      fun execute sourcename source p =
         let
            val p' =
               Incremental.compile p
               handle
                  Error.Error (msg, place) =>
                     (
                     showIppError sourcename source msg place;
                     raise Exception
                     )
         in
            SubRepl.errorDetected := false;
   
            SubRepl.errorHandler := 
               (fn (_, span, msg) =>
                   (
                   print "\n";
                   Incremental.showErrorMessage p' span source sourcename msg
                   ));
   
            (* suppress the message generated by use *)
            SubRepl.skipLine := true;
   
            (Platform.use (!theTempFilename)
             handle exn => handleExn exn);
   
            if !SubRepl.errorDetected then
               (
               Incremental.undo ();
               raise Exception
               )
            else
               ()
         end



      (* Using IML source files *)

      fun useLoop sourcename source s runCommands =
         (case Stream.front s of
             Stream.Nil => ()

           | Stream.Cons _ =>
                let
                   val (p, s') = parse sourcename source s
                in
                   execute sourcename source p;
                   runCommands ();
                   useLoop sourcename source s' runCommands
                end)


      fun ippuse filename runCommands =
         let
            val filename =
               Path.canonize filename
               handle Path.Path =>
                  raise (Error.GeneralError ("bad path name " ^ filename))

            val olddir = OS.FileSys.getDir ()

            val (newdir, _) = Path.split filename

            val () = OS.FileSys.chDir newdir

            val () =
               (
               print "[opening ";
               print filename;
               print "]\n"
               )

            val ins =
               TextIO.openIn filename
               handle exn => handleExn exn

            val strm = Stream.fromTextInstream ins
            val source = ShowContext.streamToSource firstRow strm
            val s = Incremental.lex strm Span.origin
         in
            Finally.finally
               (fn () => useLoop (SOME filename) source s runCommands)
               (fn () => 
                   (
                   TextIO.closeIn ins;
                   OS.FileSys.chDir olddir
                   ))
         end



      (* The command loop

         IML's behavior here is different from SML/NJ.

         In SML/NJ, when you "use" a file, this is what happens:

         1. the declaration containing the use is typechecked and compiled
         2. the compiled code is executed
         3. during that execution, any "use" happens immediately, which results in
            more execution and more bindings are introduced
         4. the binding resulting from the original declaration is introduced

         Some consequences:
         - bindings from the used file are not visible to the original declaration
           (because it was typechecked and compiled before the used file)

         - side effects from the used file *are* visible to the original declaration

         - if the used file raises an exception, the original declaration's binding
           never takes place (because the side-effect preempts it)

         - oddly, if the used file contains a type error, "use" terminates successfully,
           so the original declaration's binding does take place

         We rely on SML/NJ's behavior -- specifically how side-effects take place
         immediately -- but do not reproduce it.


         In IML, when you "use" a file, this is what happens:

         1. the declaration containing the use is typechecked and compiled
         2. the compiled code is executed
         3. during that execution, any "use" enqueues a USE command, and then returns
         4. the binding resulting from the original declaration is introduced
         5. enqueued commands take place

         (Actually, 4 happens before 2, and is undone if 2 or 3 fails, but the user
         can't tell that.)

         Consequently:
         - side effects from the used file are *not* visible to the original declaration
         - an exception does not stop the original binding from taking place

         In principle we could emulate SML/NJ's behavior, but that would require
         re-engineering the IML's incremental interface to separate compiling IML
         code from introducing the resulting binding.  It doesn't seem worth it to do
         that just to get the same behavior as SML/NJ in a corner case.
      *)

      datatype command =
         USE of string

      (* Any commands enqueued during a command go into a fresh queue that
         is processed before returning to the original queue.  Notionally
         we have a stack of queues, but each queue other than the top one
         are stored in the control flow.
      *)
      val commands : command IQueue.iqueue ref = ref (IQueue.iqueue ())

      fun runCommands () =
         let
            val q = !commands
         in
            if IQueue.isEmpty q then
               ()
            else
               let
                  val command = IQueue.remove q

                  val newq = IQueue.iqueue ()
               in
                  commands := newq;
   
                  Finally.finally
                     (fn () => 
                         (case command of
                             USE filename => ippuse filename runCommands))
                     (fn () => commands := q);

                  runCommands ()
               end
         end



      (* The REPL's main loop(s) *)

      (* Keeps processing the input as long as no exceptional conditions arise.

         source is the original character source (i.e., not advanced as we go along)
      *)
      fun mainLoop source s =
         let
            val (p, s') = parse NONE source s
         in
            (* does nothing if there's not a checkpoint location waiting for this *)
            Memory.checkpoint ();

            execute NONE source p;
            runCommands ();
            Buffer.signal ();
            mainLoop source s'
         end
            

      (* Process an interjection input.  Unlike mainLoop, it can finish.  Also, it
         doesn't save checkpoints and doesn't involve the buffer.
      *)
      fun interjectLoop source s =
         (case Stream.front s of
             Stream.Nil => ()

           | _ =>
                let
                   val (p, s') = parse NONE source s
                in
                   execute NONE source p;
                   runCommands ();
                   interjectLoop source s'
                end)


      (* Calls mainLoop, handles exceptional conditions, then restarts the main loop.

         row is the current row.
         gapStart is the row of the beginning of the preceding gap (possibly empty).
      *)
      fun replLoop gapStart row =
         let
            val () = Memory.setLocation (gapStart, row)

            val () = Buffer.signal ()

            val strm = Buffer.new gapStart row
         in
            mainLoop (ShowContext.streamToSource row strm) (Incremental.lex strm (row, firstCol))
            handle
               Buffer.Interjection s =>
                  let
                     val (a, b) = Memory.rewindLast ()
                  in
                     UI.moveCursor b;
   
                     (interjectLoop 
                         (ShowContext.streamToSource interjectionRow s)
                         (Incremental.lex s (interjectionRow, firstCol))
                      handle Exception => ());
   
                     replLoop a b
                  end
   
             | Buffer.Rewind n =>
                  let
                     val (a, b) = Memory.rewind n
                     val line = Int.min (b, n)
                  in
                     UI.moveCursor line;
                     onRewind ();
                     replLoop a line
                  end
   
             | Exception =>
                  let
                     val (a, b) = Memory.rewindLast ()
                  in
                     UI.moveCursor b;
                     UI.beep ();
                     replLoop a b
                  end

             | SilentException =>
                  (* same as Exception but no beep *)
                  let
                     val (a, b) = Memory.rewindLast ()
                  in
                     UI.moveCursor b;
                     replLoop a b
                  end
                  
         end
  


      (* Create the initial environment *)

      fun makeStruct l =
         foldl
            (fn (str, c) => 
                let
                   val sym = Symbol.fromValue str
                in
                   Context.forwardExp c sym ([sym], 0)
                end)
            Context.empty
            l

      val ctrlSig =
         makeStruct
            ["use", "exit", 
             "pwd", "cd",
             "printDepth", "printLength", "stringLength", "gcMessages", "allowBeep", "backtrace"]

      val recoverSig =
         makeStruct ["recover"]

      val initial =
         Context.forwardMod
            (Context.forwardMod
                (Context.forwardSig
                    (Initial.basis (Language.SML) false)
                    (Symbol.fromValue "CTRL")
                    (Symbol.fromValue "CTRL", ctrlSig))
                (Symbol.fromValue "Ctrl")
                ([Symbol.fromValue "Ctrl"], ctrlSig))
            (Symbol.fromValue "RecoverRepl")
            ([Symbol.fromValue "RecoverReplInside"], recoverSig)

      val () = Incremental.reset initial



      (* Start the REPL *)

      fun activate main =
         let
            val tempFilename = OS.FileSys.tmpName ()

            val () =
               (
               theTempFilename := tempFilename;
               Incremental.outputStream := (fn () => TextIO.openOut tempFilename);
               Platform.captureOutput SubRepl.process;
               commands := IQueue.iqueue ()
               )

            val x = main ()
         in
            Platform.resetOutput ();
            OS.FileSys.remove tempFilename handle OS.SysErr _ => ();
            x
         end

      fun startRepl gapStart row =
         activate
         (fn () => replLoop gapStart row handle Exit => ())

      fun run () =
         (
         print "[IML repl started]\n\n";
         startRepl firstRow firstRow
         )

      fun batch filename =
         let
            val result =
               activate
               (fn () =>
                   (
                   IQueue.insert (!commands) (USE filename);
   
                   (runCommands (); true)
                   handle
                      Exit => false
                    | Exception => false
                   ))
         in
            if result then
               ()
            else
               (
               print "[exiting ";
               print filename;
               print "]\n"
               );

            result
         end



      (* Exports *)

      structure Repl =
         struct

            val run = run
            val batch = batch

            structure Hooks = Hooks

         end


      structure Ctrl =
         struct

            fun use filename = IQueue.insert (!commands) (USE filename)

            fun exit () = 
               (
               Platform.resetOutput ();
               
               OS.Process.exit OS.Process.success
               )

            val pwd = OS.FileSys.getDir
            val cd = OS.FileSys.chDir

            val printDepth = Platform.printDepth
            val printLength = Platform.printLength
            val stringLength = Platform.stringLength
            val gcMessages = Platform.gcMessages
            val allowBeep = UI.allowBeep
            val backtrace = backtrace

         end

         
      (* After the UI interrupts, it sends "RecoverRepl.recover ();".

         We don't know whether an interrupt will come while running IML code, in which
         case we will stay in the IML repl, or while translating IML code, in which case
         the IML repl will be interrupted.  So we arrange the environment so that in the
         IML repl RecoverRepl points to RecoverReplInside, but outside the IML repl it
         points to RecoverRepl.
      *)

      structure RecoverRepl =
         struct

            fun recover () =
               (* In this scenario, the interrupt arrived while in the IML repl code,
                  so the IML interrupted, placing us at the SML/NJ repl prompt.  The UI then
                  sent "RecoverRepl.recover ();", which got us here.

                  Now we have to do all the usual exception recovery stuff before
                  restarting the repl.
               *)
               let
                  val (a, b) = Memory.rewindLast ()
               in
                  UI.moveCursor b;
                  UI.beep ();
                  UI.message "Interrupt";
                  startRepl a b
               end

         end


      structure RecoverReplInside =
         struct

            fun recover () =
               (* In this scenario, the interrupt arrived while in Platform.use, so we
                  handled it as an uncaught exception and rewound the state as usual.  
                  At that point everything was fine, but the UI didn't know that, so
                  it sent "RecoverRepl.recover ();" anyway, which got us here.

                  At this point we want to gracefully pretend that this was never called
                  at all, so we will raise the SilentException exception.  That will do the
                  usual exception stuff except that it won't ring the bell a second time.
               *)
               raise SilentException

         end

   end
