CM.make "sources.cm";
use "platform-nj.sml";

structure ReplStuff =
   ReplFun (structure Platform = Platform
            structure UI = NullUI
            structure PostProcess = PostProcess
            structure Memory = NullMemory
            structure Buffer = SimpleBuffer);
structure Repl = ReplStuff.Repl;
structure Ctrl = ReplStuff.Ctrl;


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


(* Begin *)

Incremental.consult "open Pervasive;\n";
open Pervasive;


if Repl.batch "../core/prelude.iml" then
   ()
else
   (
   print "Error loading prelude.";
   OS.Process.exit OS.Process.failure
   );

Repl.batch "procdoc.iml";

fun go (_, args) =
   (case args of
       [infile, outfile] =>
          ((
           Procdoc.go (Basis.Path.fromHybridPath infile) (Basis.Path.fromHybridPath outfile);
           OS.Process.success
           )
           handle _ => OS.Process.failure)

     | _ =>
          (
          print "usage\n  procdoc <input-file> <output-file>\n";
          OS.Process.failure
          ))

fun export () = SMLofNJ.exportFn ("bin/procdoc-heapimg", go)
