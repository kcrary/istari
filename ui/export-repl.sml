
use "use-repl.sml";
Incremental.load "../prover/prover.proj";
CM.make "../prover/prover.cm";

Ctrl.primaryPrompt := "";
Ctrl.secondaryPrompt := "";
Repl.uiOn := true;


(* Set the hooks between the UI and Prover. *)

Repl.proverShow := Message.display;

Repl.rewindHook :=
   (fn () =>
       let
          val st = Checkpoint.checkpoint ()
       in
          fn () => 
             if Checkpoint.restore st then 
                (Prover.show (); true)
             else
                false
       end);

(* Repl.resetHook is set below. *)

ProverInternal.beforeLemmaHook := 
   (fn () => 
       let
          val st = Checkpoint.checkpoint ()
       in
          Repl.persistentCheckpoint
             (fn () =>
                 (
                 Checkpoint.restore st;
                 (* Ignore failure here, as per checkpoint spec. *)

                 Prover.show ()
                 ))
       end);


(* Begin *)

Incremental.inputKnown "open Pervasive;";
open Pervasive;


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


val exportPath = "bin/istarisrv-heapimg"
val exportPathNolib = "bin/istarisrv-nolib-heapimg"

fun export prelude =
   let
      val exportPath =
         if prelude then
            if Repl.batch "../library/prelude.iml" then
               exportPath
            else
               (
               print "Error loading prelude.";
               OS.Process.exit OS.Process.failure
               )
         else
            exportPathNolib

      val st = Checkpoint.checkpoint ()

      val () =
         Repl.resetHook :=
            (fn () => (
                      Checkpoint.restore st;
                      (* Ignore failure here, as per checkpoint spec. *)
         
                      Prover.show ()
                      ));


      val {system, version_id, date} = Compiler.version
      val replDate = Date.toString (Date.fromTimeUniv (Time.now ()))
   in
      if SMLofNJ.exportML exportPath then
         (
         print "Istari proof assistant [";
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
   
         Repl.run ()
         )
      else
         OS.Process.exit OS.Process.success
   end
