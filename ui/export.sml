CM.make "sources.cm";
use "platform-nj.sml";

structure ReplStuff = ReplFun (structure Platform = Platform
                               structure UI = UI
                               structure PostProcess = PostProcess
                               structure Memory = Memory
                               structure Buffer = Buffer);
structure Repl = ReplStuff.Repl;
structure Ctrl = ReplStuff.Ctrl;
structure RecoverRepl = ReplStuff.RecoverRepl;
structure RecoverReplInside = ReplStuff.RecoverReplInside;


Incremental.load "../prover/prover.proj";
CM.make "../prover/prover.cm";

(* We have access to both Path, and Basis.Path.  They are mostly
   the same code, but different instances.  Make sure we're using
   the latter.
*)
structure Path = Basis.Path;


(* Set hooks *)

Repl.Hooks.exceptionHandler := Handler.handler;

FileInternal.useHook := Ctrl.use;

(* Only set ProverInternal.beforeLemmaHook in server mode, because it would actually be called. *)

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

(* Set Repl.Hooks.reset after the prelude is loaded. *)


(* Begin *)

Incremental.consult "open Pervasive;\n";
open Pervasive;


val version =
   String.concat
      [
      Version.version,
      " [",
      Date.toString (Date.fromTimeUniv (Time.now ())),
      "]"
      ]

fun splash () =
   let
      val {system, version_id, ...} = Compiler.version
   in
      print "Istari proof assistant ";
      print version;
      print "\nRunning on ";
      print system;
      print " v";
      print (Int.toString (hd version_id));
      app (fn i => (print "."; print (Int.toString i))) (tl version_id);
      print "\n";

      (* Make the startup splash cleaner. *)
      Control.Print.out := {say = (fn _ => ()), flush = (fn () => ())}
   end


(* precondition: buildDir is a valid, absolute path *)
fun setLibraryPath buildDir l =
   let
      val execDir = Basis.FileSystem.getDir ()

      val envlib =
         (case OS.Process.getEnv "ISTARILIB" of
             NONE => NONE

           | SOME path =>
                (let
                    val path' = Path.fromHybridPath path
                 in
                    if Path.isAbsolute path' then
                       SOME path'
                    else
                       (
                       print "Error: ISTARILIB must be an absolute path.\n";
                       NONE
                       )
                 end
                 handle Path.Path =>
                    (
                    print "Error: ISTARILIB must be a valid path.\n";
                    NONE
                    )))

      val lib =
         (case envlib of
             SOME path => path

           | NONE =>
                Path.canonize (Path.join buildDir "../library"))
   in
      FileInternal.libraryPath :=
         map (Path.makeAbsolute execDir) l 
         @ [lib]
   end


fun server buildDir message =
   (
   (* only in server mode *)
   ProverInternal.beforeLemmaHook := Memory.saveLast;

   (* only in server mode, prelude is loaded now *)
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

   splash ();

   setLibraryPath buildDir [];

   print message;
   if message = "" then () else print "\n";
   
   Repl.run ()
   )


structure C = BatchCommandLine (val version = version)

fun batch buildDir message (_, args) =
   (
   C.process args;

   splash ();

   setLibraryPath buildDir (C.libPath ());

   print message;
   if message = "" then () else print "\n";

   if C.rapidFlag () then
      (
      Unsafe.allow ();
      Datatype.rapid := true;
      print "Rapid datatype elaboration activated.\n"
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
   let
      val buildDir = Basis.FileSystem.getDir ()
   in
      import prelude;
   
      if SMLofNJ.exportML exportPath then
         server buildDir message 
      else
         ()
   end


fun exportBatch prelude message exportPath =
   let
      val buildDir = Basis.FileSystem.getDir ()
   in
      import prelude;

      SMLofNJ.exportFn (exportPath, batch buildDir message)
   end
