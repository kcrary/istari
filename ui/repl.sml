
signature CTRL =
   sig

      val load : string -> unit     (* load a compiled project *)
      val use : string -> unit      (* load a file *)
      val import : string -> unit   (* load a file, but only once *)
      val escape : unit -> unit
      val exit : unit -> 'a

      val pwd : unit -> string
      val cd : string -> unit

      val printDepth : int ref
      val printLength : int ref
      val stringDepth : int ref


      val allowBeep : bool ref
      val primaryPrompt : string ref
      val secondaryPrompt : string ref

   end


signature REPL =
   sig

      (* Start the REPL. *)
      val run : unit -> unit

      (* Reset the preprocessor state, effectively emptying the environment. *)
      val reset : unit -> unit

      (* load the indicated file, as it it were being used, true result indicates success *)
      val batch : string -> bool



      (* Hooks and such *)

      val uiOn : bool ref
      val proverShow : (unit -> unit) ref                (* display current goals *)
      val rewindHook : (unit -> unit -> bool) ref        (* obtain a checkpoint *)
      val resetHook : (unit -> unit) ref                 (* reset to initial state *)
      val persistentCheckpoint : (unit -> unit) -> unit  (* save a checkpoint *)
      val exceptionHandler : (exn -> bool) ref           (* call on uncaught exceptions *)

   end


signature RECOVER_REPL =
   sig

      (* Recover from an interruption. *)
      val recover : unit -> unit

   end


signature PLATFORM =
   sig

      (* load the code from the given file name *)
      val use : string -> unit

      (* load the compiled project with the given base name *)
      val load : string -> bool

      val captureOutput : (string -> unit) -> unit
      val resetOutput : unit -> unit

      structure Tools :
         sig

            val printDepth : int ref
            val printLength : int ref
            val stringDepth : int ref

         end

   end


functor ReplFun (structure Platform : PLATFORM
                 structure PostProcess : POSTPROCESS)
   :> 
   sig
      structure Repl : REPL
      structure Ctrl : CTRL
      structure RecoverRepl : RECOVER_REPL
      structure RecoverReplAlt : RECOVER_REPL
   end
   =
   struct

      (* Processing the ML REPL's output. *)
      structure SR = SubReplFun (structure PostProcess = PostProcess)
      
      exception Exit

      val exceptionHandler : (exn -> bool) ref = ref (fn _ => false)

      fun withHandler x f =
         f ()
         handle
            Exit => raise Exit

          | Error.Error (msg, _) =>
               (
               print "IPP error: ";
               print msg;
               print "\n\n";
               SR.errorDetected := true;
               x
               )

          | exn =>
               if !exceptionHandler exn then
                  (
                  print "\n";
                  SR.errorDetected := true;
                  x
                  )
               else
                  (
                  print "Uncaught exception ";
                  print (exnMessage exn);
                  print "\n\n";
                  SR.errorDetected := true;
                  x
                  )

      fun onException f g =
         f ()
         handle exn =>
            (
            g ();
            raise exn
            )


      structure Memory = MemoryFun (val withHandler = withHandler)
      

      structure Repl =
         struct

            structure S = Stream
            structure I = Incremental
      
            val proverShow = ref (fn () => ())
            val uiOn = UI.on
            val exceptionHandler = exceptionHandler
      
            val localTempFilename = "iml-temp-buffer.sml"
            val theTempFilename = ref ""
      
      
            (* Error handlers *)
      
            fun mainErrorHandler (_, span, msg) = 
               (
               print "\n";
               I.invert span msg
               )
               
            structure R =
               RegexpFun (structure Streamable =
                             MonomorphizeStreamable (structure Streamable = StreamStreamable
                                                     type elem = char))
      
            local
      
               open R
               fun filesep ch = ch = #"/" orelse ch = #"\\"
               fun notfilesep ch = not (filesep ch)
      
            in
      
               val reFilename = seq [plus' any, set filesep,
                                     capture (plus' (set notfilesep)),
                                     string ".iml.sml"]
            end
      
            fun loadErrorHandler projfilename (errfile, span, msg) =
               (case R.match reFilename (S.fromString errfile) of
                   NONE =>
                      (
                      print "<file not identified>";
                      print msg
                      )
      
                 | SOME [R.One goodname] =>
                      (
                      Main.invert projfilename goodname span msg;
                      ()
                      )
      
                 | SOME _ =>
                      raise (Fail "impossible"))
      

      
      
      
            (* Commands for Ctrl *)
      
            datatype command = 
               LOAD of string 
             | USE of string 
             | IMPORT of string 
             | ESCAPE
      
            (* a stack of queues *)
            val commandQueues : command IQueue.iqueue list ref = ref [IQueue.iqueue ()]

            fun enqueue command =
               (case !commandQueues of
                   [] => raise (Fail "invariant")

                 | q :: _ =>
                      IQueue.insert q command)

            structure StringSet = RedBlackSet (structure Elem = StringOrdered)
            
            val imported : StringSet.set ref = ref StringSet.empty


            exception LoadError

            fun load projfilename =
               if I.load projfilename then
                  let
                     val proj = Make.getProjectBase projfilename
                     
                     val () =
                        (
                        print "[loading ";
                        print proj;
                        print "]\n"
                        )
      
                     val () = SR.errorHandler := loadErrorHandler projfilename
                  in
                     if
                        onException
                           (fn () => Platform.load proj)
                           I.undo
                     then
                        ()
                     else
                        (
                        I.undo ();
                        raise LoadError
                        )
                  end
               else
                  ()
      

            exception UseError

            fun useLoop used =
               let
                  val status = I.inputUsed used
               in
                  (case status of
                      I.ERROR =>
                         (
                         I.closeUsed used;
                         commandQueues := [IQueue.iqueue ()];
                         raise UseError
                         )

                    | _ =>
                         (
                         SR.skipLine := true;
                         SR.errorDetected := false;
                         SR.errorHandler := mainErrorHandler;

                         onException
                            (fn () => Platform.use (!theTempFilename))
                            (fn () =>
                                (
                                I.closeUsed used;
                                I.undo ();
                                commandQueues := [IQueue.iqueue ()]
                                ));

                         if !SR.errorDetected then
                            (
                            I.closeUsed used;
                            I.undo ();
                            commandQueues := [IQueue.iqueue ()];
                            raise UseError
                            )
                         else
                            (
                            onException
                               runCommands
                               (fn () =>
                                   (
                                   I.closeUsed used;
                                   commandQueues := [IQueue.iqueue ()]
                                   ));

                            (case status of
                                I.COMPLETE =>
                                   I.closeUsed used

                              | I.MORE =>
                                   useLoop used

                              | _ =>
                                   (* file input cannot return WAITING or EMPTY status *)
                                   raise (Fail "impossible"))
                            )
                         ))
               end

            and ippuse filename =
               let
                  val filename =
                     Path.canonize filename
                     handle Path.Path =>
                        raise (Error.GeneralError ("bad path name " ^ filename))

                  val olddir = OS.FileSys.getDir ()

                  val (newdir, _) = Path.split filename
               in
                  OS.FileSys.chDir newdir;

                  onException
                     (fn () =>
                         (
                         useLoop (I.useFile (fn () => TextIO.openOut (!theTempFilename)) filename);
                         OS.FileSys.chDir olddir
                         ))
                     (fn () => OS.FileSys.chDir olddir)
               end


            and import filename =
               let
                  val filename =
                     Path.canonize filename
                     handle Path.Path =>
                        raise (Error.GeneralError ("bad path name " ^ filename))
               in
                  if StringSet.member (!imported) filename then
                     ()
                  else
                     (
                     imported := StringSet.insert (!imported) filename;

                     (* This will end of canonizing filename again, but it doesn't seem like
                        a big enough deal to do anything about it.
                     *)
                     ippuse filename
                     )
               end

      
            and runCommands () =
               (case !commandQueues of
                   [] => raise (Fail "invariant")

                 | commandQueue :: restQueues =>
                      if IQueue.isEmpty commandQueue then
                         (case restQueues of
                             [] =>
                                ()

                           | _ :: _ =>
                                (
                                commandQueues := restQueues;
                                runCommands ()
                                ))
                      else
                         (case IQueue.remove commandQueue of
                             LOAD filename =>
                                (
                                load filename;
                                runCommands ()
                                )
                
                           | USE filename =>
                                (
                                (* any commands here take precedence over those already in the queue *)
                                commandQueues := IQueue.iqueue () :: !commandQueues;

                                ippuse filename;
                                runCommands ()
                                )
                
                           | IMPORT filename =>
                                (
                                (* any commands here take precedence over those already in the queue *)
                                commandQueues := IQueue.iqueue () :: !commandQueues;

                                import filename;
                                runCommands ()
                                )
                
                           | ESCAPE => raise Exit))

      

            (* The IML REPL *)
               
            val primaryPrompt = ref "% "
            val secondaryPrompt = ref "= "
      
            fun stringAllLoop f str i j =
               if i >= j then
                  true
               else
                  f (String.sub (str, i))
                  andalso
                  stringAllLoop f str (i+1) j
      
            fun stringAll f str = stringAllLoop f str 0 (String.size str)      
      
      
            fun inputLoopMain input =
               (case input of
                   UI.ChannelClosed => raise Exit
      
                 | UI.Rewind n =>
                      (
                      I.discard ();
                      Memory.rewind n;
                      preInputLoop ()
                      )
      
                 | UI.ShowState =>
                      (* Ignore this if we're in the middle of something. *)
                      inputLoop ()

                 | UI.Interject line =>
                      (
                      (* First scrap any input. *)
                      I.discard ();
                      Memory.rewind 0;
                      
                      (case I.input (fn () => TextIO.openOut (!theTempFilename)) line of
                          I.WAITING =>
                             (* The interjection must be a complete interaction. Abort. *)
                             (
                             I.discard ();
                             UI.message "Incomplete interjection";
                             UI.beep ();
                             preInputLoop ()
                             )

                        | I.EMPTY => ()
      
                        | I.COMPLETE => ()
      
                        | I.ERROR =>
                             (
                             UI.beep ();
                             preInputLoop ()
                             )

                        | I.MORE =>
                             (* console input cannot return MORE status *)
                             raise (Fail "impossible"))
                      )
      
                 | UI.Line str =>
                      (
                      Memory.advanceLine ();
                      (case I.input (fn () => TextIO.openOut (!theTempFilename)) str of
                          I.WAITING =>
                             inputLoop ()
          
                        | I.COMPLETE => ()
          
                        | I.EMPTY =>
                             (* nothing here but comments after all *)
                             (
                             Memory.deadspace ();
                             preInputLoop ()
                             )

                        | I.ERROR =>
                             (
                             Memory.uncheckpoint ();
                             UI.beep ();
                             preInputLoop ()
                             )

                        | I.MORE =>
                             (* console input cannot return MORE status *)
                             raise (Fail "impossible"))
                      ))
      
            (* oldLine is the line where the input begin, for rewinding purposes *)
            and inputLoop () =
               (
               print (!secondaryPrompt);
      
               UI.readyPartial ();
               inputLoopMain (UI.input ())
               )
      
            (* skipping leading whitespace *)
            and preInputLoop () =
               (
               print (!primaryPrompt);
      
               UI.ready ();
               (case UI.input () of
                   UI.ChannelClosed => raise Exit
      
                 | UI.ShowState =>
                      (
                      !proverShow ();
                      preInputLoop ()
                      )

                 | input =>
                      if 
                         (case input of
                             UI.Line str => stringAll Char.isSpace str
                           | _ => false)
                      then
                         (* blank line *)
                         (
                         Memory.advanceLine ();
                         preInputLoop ()
                         )
                      else
                         (
                         Memory.checkpoint ();
                         inputLoopMain input
                         ))
               )
      
      
      
            fun mainLoop () =
               (
               Memory.deadspace ();
               preInputLoop ();
               SR.skipLine := true;
               SR.errorDetected := false;
               SR.errorHandler := mainErrorHandler;
      
               withHandler () (fn () => Platform.use (!theTempFilename));
               TextIO.flushOut TextIO.stdOut;
               (* reactivate output in case we muted the SML repl *)
               Platform.captureOutput SR.process;
      
               if
                  !SR.errorDetected
                  orelse
                  (withHandler () runCommands; !SR.errorDetected)
               then
                  (
                  I.undo ();
                  Memory.uncheckpoint ();
                  UI.beep ();
                  commandQueues := [IQueue.iqueue ()];
                  mainLoop ()
                  )
               else 
                  mainLoop ()
               )

      
      
            (* Ctrl and the initial environment *)
      
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
                  ["load", "use", "import", "escape", "exit", "pwd", "cd",
                   "printDepth", "printLength", "stringDepth",
                   "allowBeep", "primaryPrompt", "secondaryPrompt"]
      
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
                  ([Symbol.fromValue "RecoverReplAlt"], recoverSig)
      


            (* Startup *)
      
            (* Put Ctrl into the IPP environment. *)
            val () = I.reset initial
      
            fun reset () = I.reset initial
      
            val oldout = { say = print, flush = (fn () => ()) }
      
            fun runQuietly () =
               Finally.finally
                  (fn () =>
                      (
                      (* When the UI starts the repl, it starts it with the output functions
                         empty, to make the startup splash cleaner.  We'll just undo that now.  
                         (We don't know if this is the first time time the repl is being run, 
                         but it's not harmful to do it extra times.)
                      *)
                      Platform.resetOutput ();
      
                      theTempFilename := OS.FileSys.tmpName ();
                      Platform.captureOutput SR.process;
                      commandQueues := [IQueue.iqueue ()];
             
                      mainLoop () handle Exit => ();
             
                      OS.FileSys.remove (!theTempFilename) handle OS.SysErr _ => ()
                      ))
                  (fn () => Platform.resetOutput ())
      
            fun run () =
               (
               print "[IML repl started]\n\n";
               runQuietly ()
               )

            fun recover () =
               (
               UI.beep ();
               UI.message "Interrupt";
               runQuietly ()
               )

            fun batch filename =
               Finally.finally
                  (fn () =>
                      let
                         val q = IQueue.iqueue ()
                      in
                         (* As above. *)
                         Platform.resetOutput ();
         
                         theTempFilename := OS.FileSys.tmpName ();
                         Platform.captureOutput SR.process;
                         commandQueues := [q];

                         IQueue.insert q (USE filename);

                         let
                            val res =
                               withHandler false (fn () => (runCommands (); true))
                               handle Exit =>
                                  (
                                  print "[exiting]\n";
                                  false
                                  )
                         in
                            OS.FileSys.remove (!theTempFilename) handle OS.SysErr _ => ();

                            res
                         end
                      end)
                  (fn () => Platform.resetOutput ())


            val rewindHook = Memory.rewindHook
            val resetHook = Memory.resetHook
            val persistentCheckpoint = Memory.persistentCheckpoint

         end

      structure Ctrl =
         struct

            fun load str = Repl.enqueue (Repl.LOAD str)
            fun use str = Repl.enqueue (Repl.USE str)
            fun import str = Repl.enqueue (Repl.IMPORT str)
            fun escape () = Repl.enqueue Repl.ESCAPE
            fun exit () = OS.Process.exit OS.Process.success
      
            val pwd = OS.FileSys.getDir
            val cd = OS.FileSys.chDir
      
            open Platform.Tools

            val allowBeep = UI.allowBeep
            val primaryPrompt = Repl.primaryPrompt
            val secondaryPrompt = Repl.secondaryPrompt

         end

      (* After the UI interrupts, it sends RecoverRepl.recover ().

         We don't know whether an interrupt will come while running IML code, in which
         case we will stay in the IML REPL, or while translating IML code, in which case
         the IML REPL will be interrupted.  So we arrange the environment so that in the
         IML REPL RecoverRepl points to RecoverReplAlt, but outside the IML REPL it points
         to RecoverRepl.
      *)

      structure RecoverRepl =
         struct

            val recover = Repl.recover

         end


      structure RecoverReplAlt =
         struct

            fun recover () =
               (
               Memory.undo ();
               UI.message "Interrupt"
               )

         end

   end
