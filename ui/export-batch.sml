CM.make "sources.cm";
use "platform-nj.sml";
CM.make "../ipp/basis/basis.cm";

local

   structure ReplStuff =
      ReplFun (structure Platform = PlatformNJ
               structure UI = NullUI
               structure PostProcess = PostProcessNJ
               structure Memory = NullMemory
               structure Buffer = SimpleBuffer)

in

   structure Repl = ReplStuff.Repl
   structure Ctrl = ReplStuff.Ctrl

end;


Incremental.load "../prover/prover.proj";
CM.make "../prover/prover.cm";


(* Set hooks *)

Repl.Hooks.exceptionHandler := Handler.handler;

FileInternal.useHook := Ctrl.use;


(* Begin *)

Incremental.consult "open Pervasive;\n";
open Pervasive;


structure C = BatchCommandLine


val exportPath = "bin/istari-heapimg"
val exportPathNolib = "bin/istari-nolib-heapimg"
val {system, version_id, date} = Compiler.version
val replDate = Date.toString (Date.fromTimeUniv (Time.now ()))

fun go prelude (_, args) =
   (
   C.process args;
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

   if prelude then
      print "Libraries loaded.\n"
   else
      ();

   (* Make the startup splash cleaner. *)
   Control.Print.out := {say = (fn _ => ()), flush = (fn () => ())};

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


(*

We create an export function and call it from user input, rather than
merely executing it directly.  The user input "export <true/false>;" 
is piped in by the makefile.

The reason is a peculiarity in the way that SML/NJ propagates
exceptions in nested "use" instances.  Uncaught exceptions raised by
the startup code get turned into ExnDuringExecution, while uncaught
exceptions raised by user code are treated properly.  This arranges
that everything is run as user code.

*)


fun export prelude =
   if prelude then
      (
      if Repl.batch "../library/prelude.iml" then
         ()
      else
         (
         print "Error loading prelude.";
         OS.Process.exit OS.Process.failure
         );

      SMLofNJ.exportFn (exportPath, go true)
      )
   else
      SMLofNJ.exportFn (exportPathNolib, go false)
