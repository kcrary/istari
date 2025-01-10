
signature BATCH_COMMAND_LINE =
   sig

      (* Call to process command-line arguments *)
      val process : string list -> unit


      (* After arguments have been processed, call these to obtain the results. *)
      val inputFile : unit -> string
      val outputFile : unit -> string option
      val rapidFlag : unit -> bool

   end



structure BatchCommandLine :> BATCH_COMMAND_LINE =
   struct

      structure C = ParseCommandLine


      fun exit () = OS.Process.exit OS.Process.success
      fun exitfail () = OS.Process.exit OS.Process.failure


      fun usage () =
         (
         print "istari usage:\n";
         print "  istari [options] <istari-file>\n\
               \  -no             do not write output\n\
               \  -o <filename>   set output file name\n\
               \  -rapid          activate unsafe mode and rapid datatype elaboration\n";
         exit ()
         )

   
      val infileKey : string C.id_key =
         C.key (C.default'
                   (fn _ => (print "istari: no input file\n"; exitfail ())))

      val outfileKey : string option C.id_key =
         C.key 
            (C.once "multiple output options specified"
                (C.default'
                    (fn log =>
                        let
                           val infile = C.read infileKey log
 
                           val base =
                              (case Path.splitExt infile of
                                  SOME (base, _) => base
                                | NONE => infile)
                        in
                           SOME (Path.joinExt base "isto")
                        end)))

      val rapidKey : bool C.id_key = C.key (C.default false)


      val parser =
         C.or
         [
         C.map usage C.eof,

         C.foldCompose
            (C.or
                [
                C.map usage (C.exactly "--help"),
                
                C.unitOpt "-no" outfileKey NONE,
                C.stringOpt "-o" (C.mapKeyIn SOME outfileKey),
                C.unitOpt "-rapid" rapidKey true,

                C.map (fn name => C.write infileKey name) C.nohyph
                ])
         ]

      
      val theLog = ref C.blank

      fun process args =
         theLog := C.parse parser args C.blank
         handle C.Error msg =>
            (
            print "istari: ";
            print msg;
            print "\n\n";
            usage ()
            )


      fun inputFile () = C.read infileKey (!theLog)

      fun outputFile () = C.read outfileKey (!theLog)

      fun rapidFlag () = C.read rapidKey (!theLog)

   end
