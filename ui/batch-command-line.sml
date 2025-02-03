
signature BATCH_COMMAND_LINE =
   sig

      (* Call to process command-line arguments *)
      val process : string list -> unit


      (* After arguments have been processed, call these to obtain the results. *)
      val inputFile : unit -> string
      val outputFile : unit -> string option
      val libPath : unit -> string list
      val rapidFlag : unit -> bool

   end



functor BatchCommandLine (val version : string) :> BATCH_COMMAND_LINE =
   struct

      structure C = ParseCommandLine


      fun exit () = OS.Process.exit OS.Process.success
      fun exitfail () = OS.Process.exit OS.Process.failure

      fun fromHybridPath filename =
         Basis.Path.fromHybridPath filename
         handle Basis.Path.Path =>
            (
            print "Error: bad path ";
            print filename;
            print "\n";
            exitfail ()
            )


      fun usage () =
         (
         print "istari usage:\n";
         print "  istari [options] <istari-file>\n\
               \  -no             do not write output\n\
               \  -o <filename>   set output file name\n\
               \  -L <directory>  add directory to library path\n\
               \  -rapid          activate unsafe mode and rapid datatype elaboration\n\
               \  -version        display version information\n";
         exit ()
         )

      fun showVersion () =
         (
         print "Istari proof assistant ";
         print version;
         print "\n";
         exit ()
         )
   
      val infileKey : string C.id_key =
         C.mapKeyIn fromHybridPath
            (C.key (C.default'
                       (fn _ => (print "istari: no input file\n"; exitfail ()))))

      val outfileKey : string option C.id_key =
         C.mapKeyIn (Option.map fromHybridPath)
            (C.key 
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
                            end))))

      val libKey : string C.list_key = C.mapKeyIn fromHybridPath (C.key C.list)

      val rapidKey : bool C.id_key = C.key (C.default false)


      val parser =
         C.or
         [
         C.map usage C.eof,

         C.foldCompose
            (C.or
                [
                C.map usage (C.exactly "--help"),
                C.map showVersion (C.exactly "-version"),
                
                C.unitOpt "-no" outfileKey NONE,
                C.stringOpt "-o" (C.mapKeyIn SOME outfileKey),
                C.stringOpt "-L" libKey,
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

      fun libPath () = C.read libKey (!theLog)

      fun rapidFlag () = C.read rapidKey (!theLog)

   end
