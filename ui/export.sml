CM.make "sources.cm";
use "platform-nj.sml";
CM.make "../ipp/basis/basis.cm";

structure ReplStuff = ReplFun (structure Platform = Platform
                               structure UI = UI
                               structure PostProcess = PostProcess
                               structure Memory = Memory
                               structure Buffer = Buffer)
structure Repl = ReplStuff.Repl;
structure Ctrl = ReplStuff.Ctrl;
structure RecoverRepl = ReplStuff.RecoverRepl;
structure RecoverReplInside = ReplStuff.RecoverReplInside;


Incremental.load "../prover/prover.proj";
CM.make "../prover/prover.cm";


(* Set hooks *)

Repl.Hooks.exceptionHandler := Handler.handler;

FileInternal.useHook := Ctrl.use;

(* The rest of these don't matter in batch mode because batch mode never calls them. *)

Repl.Hooks.checkpoint :=
   (fn () =>
       let
          val st = Checkpoint.checkpoint ()
       in
          (fn () => Checkpoint.restore st)
       end);

Repl.Hooks.onReady := Message.display;

Repl.Hooks.onRewind := Prover.show;

Repl.Hooks.reset :=
   let
      val st = Checkpoint.checkpoint ()
   in
      (fn () => (
                Checkpoint.restore st;
                (* Ignore failure here, as per checkpoint spec. *)
   
                ()
                ))
   end;


(* Begin *)

Incremental.consult "open Pervasive;\n";
open Pervasive;


fun splash () =
   let
      val {system, version_id, date} = Compiler.version
      val replDate = Date.toString (Date.fromTimeUniv (Time.now ()))
   in
      print "Istari proof assistant ";
      print Version.version;
      print " [";
      print replDate;
      print "]\nRunning on ";
      print system;
      print " v";
      print (Int.toString (hd version_id));
      app (fn i => (print "."; print (Int.toString i))) (tl version_id);
      print " [";
      print date;
      print "]\n";

      (* Make the startup splash cleaner. *)
      Control.Print.out := {say = (fn _ => ()), flush = (fn () => ())}
   end


fun server message =
   (
   (* only in server mode *)
   ProverInternal.beforeLemmaHook := Memory.saveLast;

   splash ();
   print message;
   
   Repl.run ()
   )


structure C = BatchCommandLine

fun batch message (_, args) =
   (
   C.process args;

   splash ();
   print message;

   if C.rapidFlag () then
      (
      Unsafe.allow ();
      Datatype.rapid := true
      )
   else
      ();

   if Repl.batch (C.inputFile ()) then
      if Prover.underway () then
         (
         print "Error: file ended with proof underway.\n";
         OS.Process.failure
         )
      else
         (
         (case C.outputFile () of
             NONE => ()
   
           | SOME name => FileInternal.save name);
   
         OS.Process.success
         )
   else
      OS.Process.failure
   )



fun import prelude =
   if Repl.batch prelude then
      ()
   else
      (
      print "Error loading prelude.";
      OS.Process.exit OS.Process.failure
      );


fun exportServer prelude message exportPath =
   (
   import prelude;

   if SMLofNJ.exportML exportPath then
      server message 
   else
      ()
   )


fun exportBatch prelude message exportPath =
   (
   import prelude;

   SMLofNJ.exportFn (exportPath, batch message)
   )
