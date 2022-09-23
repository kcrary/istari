
structure Main =
   struct

      structure L = Language

      exception Exit


      structure C = ParseCommandLine

      fun usage () =
         (
         print "ipp usage:\n\
               \  ipp [options] <project-file> \n\
               \  ipp [options] <project-file> --invert <component-name> <start> <end>\n\
               \  -ac <number>     adjust columns to invert\n\
               \  -B <directory>   set the basis directory\n\
               \  -build           write build information\n\
               \  -m <number>      maximum lines of context to show\n\
               \  -t <lang>        set target language (sml/ocaml)\n\
               \\n\
               \  --invert takes locations as row and column (r.c)\n\
               \  The component name is the basename of its output file.\n\
               \";
         raise Exit
         )


      val infileKey : string C.id_key =
         C.key (C.default'
                   (fn _ => (print "ipp: no input files\n"; raise Exit)))

      type rc = int * int
      val invertKey : (string * (rc * rc)) C.option_key = C.key C.option

      val adjustKey : int C.id_key = C.key (C.default 0)
      
      val basisKey : string C.id_key = C.key (C.default ".")

      val buildKey : bool C.id_key = C.key (C.default false)
         
      val maxContextKey : int C.id_key = C.key (C.default 8)

      val targetKey : (string, L.language) C.key =
         C.key (C.mapIn
                   (fn "sml" => L.SML
                     | "ocaml" => L.OCAML
                     | _  => (print "ipp: unsupported target language\n"; raise Exit))
                   (C.default L.SML))


      fun makeCmd log =
         let
            val projfile = C.read infileKey log
            val basisdir = C.read basisKey log
            val writebuild = C.read buildKey log
         in
            Make.make projfile basisdir writebuild;
            OS.Process.success
         end


      fun invert projfile goodname toInvert msg =
         let

            val (fullname, ctx, deps, smlCompat) =
               Make.inversionInfo projfile goodname
               handle Error.Error (msg', _) =>
                  (
                  print msg';
                  print "<location not found1>";
                  print msg;
                  print "\n";
                  raise Exit
                  )

            val () = Language.smlCompatibility := smlCompat

            val (left, right) =
               Make.withInstream fullname
                  (fn ins =>
                      let
                         val (program, _, _) =
                            Traverse.traverse ctx (Parser.parseFull (Stream.fromTextInstream ins))
                      in
                         InvertRC.invert deps program toInvert
                      end)
               handle _ =>
                  (
                  print "<location not found2>";
                  print msg;
                  print "\n";
                  raise Exit
                  )

            val source = RowCol.filenameToSource fullname

            (* We could suspend this, in case we don't need it, but it doesn't seem worth the trouble. *)
            val (rcs as ((row1, col1), (row2, col2))) =
               RowCol.fromSpan source (left, right)
               handle Error.NotFound =>
                  (* This shouldn't happen, unless someone is mucking with the file while
                     we're trying to use it. *)
                  ((1, left), (1, right))
         in
            print (String.concat [Int.toString row1, ".", Int.toString col1,
                                  "-",
                                  Int.toString row2, ".", Int.toString col2,
                                  " (",
                                  !Make.currentFilename,
                                  ")"]);
            print msg;
            print "\n";

            RowCol.display source rcs;
            true
         end handle Exit => false


      fun invertCmd log =
         let
            val projfile = C.read infileKey log
            val adjust = C.read adjustKey log
            val (goodname, ((r1, c1), (r2, c2))) = Option.valOf (C.read invertKey log)
         in
            if
               invert projfile goodname ((r1, c1 + adjust), (r2, c2 + adjust)) ""
            then
               OS.Process.success
            else
               OS.Process.failure
         end


      val modeKey : (C.log -> OS.Process.status) C.id_key = 
         C.key (C.once "multiple modes specified" (C.default makeCmd))

      val rcParser =
         C.map
            (fn str =>
                (case String.fields (fn ch => ch = #".") str of
                    [r, c] =>
                       (C.stringToNonneg r, C.stringToNonneg c)
                    
                  | _ => C.backtrack ()))
            C.string
   
      val parser =
         C.or
         [
         C.map usage C.eof,

         C.foldCompose
            (C.or
                [
                C.map usage (C.exactly "--help"),

                C.intOpt "-ac" adjustKey,
                C.stringOpt "-B" basisKey,
                C.unitOpt "-build" buildKey true,
                C.nonnegOpt "-m" maxContextKey,
                C.stringOpt "-t" targetKey,

                C.seqf (C.exactly "--invert") 
                   (C.mapCompose (C.write modeKey invertCmd)
                       (C.trap (C.expects "a span" "--invert")
                           (C.map (C.write invertKey)
                               (C.seq
                                   C.string
                                   (C.seq rcParser rcParser))))),

                C.map (fn name => C.write infileKey name) C.nohyph
                ])
         ]

      fun runCmdMain args =
         let
            val log =
               C.parse parser args C.blank
               handle C.Error msg =>
                  (
                  print "ipp: ";
                  print msg;
                  print "\n\n";
                  usage ()
                  )
         in
            L.target := C.read targetKey log;
            RowCol.maxContext := C.read maxContextKey log;

            (C.read modeKey log log)
            handle
               Error.Error (str, place) =>
                  (
                  print "Error: ";
                  print str;
                  
                  (case place of
                      Error.POS pos =>
                         let
                            val source = RowCol.filenameToSource (!Make.currentFilename)

                            val ((row, col), _) =
                               RowCol.fromSpan source (pos, pos)
                         in
                            print " at ";
                            print (Int.toString row);
                            print ".";
                            print (Int.toString col);

                            if !Make.currentFilename = "" then
                               ()
                            else
                               (
                               print " (";
                               print (!Make.currentFilename);
                               print ")"
                               );

                            print "\n";
                            RowCol.display source ((row, col), (row, col+1))
                         end

                    | Error.SPAN span =>
                         let
                            val source = RowCol.filenameToSource (!Make.currentFilename)

                            val (rcs as ((row1, col1), (row2, col2))) =
                               RowCol.fromSpan source span
                         in
                            print " at ";
                            print (Int.toString row1);
                            print ".";
                            print (Int.toString col1);
                            print "-";
                            print (Int.toString row2);
                            print ".";
                            print (Int.toString col2);

                            if !Make.currentFilename = "" then
                               ()
                            else
                               (
                               print " (";
                               print (!Make.currentFilename);
                               print ")"
                               );

                            print "\n";
                            RowCol.display source rcs
                         end

                    | Error.UNKNOWN =>
                         print "\n");

                  raise Exit
                  )
         end

      
      fun runCmd (_, args) =
         runCmdMain args
         handle 
            Exit => OS.Process.failure
          | exn => (
                   print "General error ";
                   print (exnName exn);
                   print "\n";
                   OS.Process.failure
                   )

      fun run args =
         runCmd ((), String.tokens (fn ch => ch = #" ") args)
       
   end
