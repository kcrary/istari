
use "../ui/use-repl.sml";
Incremental.load "../prover/prover.proj";
CM.make "../prover/prover.cm";

FileInternal.useHook := Ctrl.use;

Incremental.inputKnown "open Pervasive;";
open Pervasive;

if Repl.batch "../library/prelude.iml" then
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
           Procdoc.go infile outfile;
           OS.Process.success
           )
           handle _ => OS.Process.failure)

     | _ =>
          (
          print "usage\n  procdoc <input-file> <output-file>\n";
          OS.Process.failure
          ))

fun export () = SMLofNJ.exportFn ("bin/procdoc-heapimg", go)
