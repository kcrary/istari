
signature INCREMENTAL =
   sig

      val reset : Context.context -> unit

      datatype status = WAITING | COMPLETE | MORE | EMPTY | ERROR

      (* Input from console (status is never MORE) *)

      val input : (unit -> TextIO.outstream) -> string -> status
      val discard : unit -> unit

      (* Input from file (status is never WAITING or EMPTY) *)

      type used
      (* stream to use, input filename *)
      val useFile : (unit -> TextIO.outstream) -> string -> used
      val inputUsed : used -> status
      val closeUsed : used -> unit

      (* undo last interaction *)
      val undo : unit -> unit

      (* project filename -> did it load successully? *)
      val load : string -> bool

      (* preprocess but do not generate code, no errors tolerated *)
      val inputKnown : string -> unit

      val invert : ((int * int) * (int * int)) -> string -> unit

   end


structure Incremental :> INCREMENTAL =
   struct

      structure S = Stream
      type token = Token.token

      exception Block = Lexer.Block
      exception BlockModal = Lexer.BlockModal

      (* If the parser gets to block, it will raise the Block exception rather than
         signalling a syntax error.  This is how we distinguish between an incomplete
         input and a syntax error.
      *)
      
      fun parseLoop s acc =
         let
            val (p, s') = Parser.parseIncremental s

            (* We accept this parse if it is a complete interaction, meaning that
               s' is block or nil.  If there is anything before that, it is an
               incomplete interaction.
            *)

            val done =
               (case S.front s' of
                   S.Nil => true
                 | _ => false)
               handle Block => true
         in
            if done then
               foldl
                  (fn ((d1, sp1), (d2, sp2)) => (d1 @ d2, Span.join sp1 sp2))
                  p acc
            else
               parseLoop s' (p :: acc)
         end

      datatype parse_result = EMPTYPARSE | NOPARSE | SOMEPARSE of Syntax.program

      fun tryParse strs =
         let
            val s =
               foldl 
                  (fn (str, s) => S.@ (S.fromString str, s))
                  (S.eager S.Nil) strs

            val strm = Lexer.lexRepl s
         in
            if
               (S.front strm; false)
               handle Block => true
                    | BlockModal => false
            then
               (* no lexemes found, and did not end in another mode *)
               EMPTYPARSE
            else
               SOMEPARSE (parseLoop strm [])
               handle Block => NOPARSE
                    | BlockModal => NOPARSE
         end

      val initial = Initial.basis (!Language.target) (!Language.smlCompatibility)

      val theInput : string list ref = ref []
      val theContext = ref initial
      val oldInput : RowCol.source ref = ref RowCol.empty
      val oldContext = ref initial
      val oldProg : Syntax.program ref = ref ([], (0,0))

      fun reset ctx =
         (
         theContext := ctx;
         oldContext := ctx;
         theInput := [];
         oldInput := RowCol.empty;
         oldProg := ([], (0,0))
         )

      fun withErrorHandling src x f =
         f ()
         handle Error.Error (errstr, place) =>
            (
            theInput := [];
            print "Error: ";
            print errstr;

            (case place of
                Error.POS pos =>
                   let
                      val ((row, col), _) =
                         RowCol.fromSpan src (pos, pos)
                   in
                      print " at ";
                      print (Int.toString row);
                      print ".";
                      print (Int.toString col);

                      print "\n";
                      RowCol.display src ((row, col), (row, col+1))
                   end

              | Error.SPAN span =>
                   let
                      val (rcs as ((row1, col1), (row2, col2))) =
                         RowCol.fromSpan src span
                   in
                      print " at ";
                      print (Int.toString row1);
                      print ".";
                      print (Int.toString col1);
                      print "-";
                      print (Int.toString row2);
                      print ".";
                      print (Int.toString col2);

                      print "\n";
                      RowCol.display src rcs
                   end

              | Error.UNKNOWN =>
                   print "\n");
            
            x
            )

      datatype status = WAITING | COMPLETE | MORE | ERROR | EMPTY

      fun input outsfn str =
         let
            val strs = str :: !theInput
            val () = theInput := strs
            val src = RowCol.stringsToSource (rev strs)
         in
            withErrorHandling src ERROR
            (fn () =>
                (case tryParse strs of
                    NOPARSE =>
                       WAITING
    
                  | EMPTYPARSE =>
                       EMPTY

                  | SOMEPARSE p =>
                       let
                          val ctx = !theContext
                          val (p', ctx', _) = Traverse.traverse ctx p
                          val outs = outsfn ()
                       in
                           theInput := [];
                           theContext := ctx';
                           oldInput := src;
                           oldContext := ctx;
                           oldProg := p';
                           Render.render outs [] p';
                           TextIO.closeOut outs;
                           COMPLETE
                        end))
         end

      fun discard () =
         theInput := []

      type used =
         string *
         TextIO.instream * 
         (unit -> TextIO.outstream) * 
         RowCol.source * 
         Token.token Stream.stream ref

      fun useFile outsfn filename =
         let
            val ins =
               TextIO.openIn filename
               handle IO.Io _ =>
                  raise (Error.GeneralError ("unable to open file " ^ filename))

            val src = RowCol.filenameToSource filename

            val s = Lexer.lexUse (S.fromTextInstream ins)
         in
            print "[reading ";
            print filename;
            print "]\n";

            (filename, ins, outsfn, src, ref s)
         end

      fun inputUsed (_, ins, outsfn, src, sr) =
         withErrorHandling src ERROR
         (fn () =>
             let
                val (p, s') = Parser.parseIncremental (!sr)
                val ctx = !theContext
                val (p', ctx', _) = Traverse.traverse ctx p
                val outs = outsfn ()
             in
                theContext := ctx';
                oldContext := ctx;
                oldInput := src;
                oldProg := p';
                Render.render outs [] p';
                TextIO.closeOut outs;

                sr := s';

                (case S.front s' of
                    S.Nil => COMPLETE

                  | S.Cons _ => MORE)
             end)

      fun closeUsed (filename, ins, _, _, sr) =
         (
         TextIO.closeIn ins;
         sr := S.eager S.Nil;
         print "[closing ";
         print filename;
         print "]\n"
         )


      
      fun inputKnown str =
         let
            val ctx = !theContext
            val (p, _) = Parser.parseIncremental (Lexer.lexUse (S.fromString str))
            val (_, ctx', _) = Traverse.traverse ctx p
         in
            theContext := ctx';
            oldContext := ctx
         end



      fun undo () =
         (
         theInput := [];
         theContext := !oldContext
         )


      fun load projname =
         let
            val ctx = !theContext
            val ctx' = Context.union ctx (Make.load projname)
         in
            theContext := ctx';
            oldContext := ctx;
            true
         end handle Error.Error (errstr, _) =>
            (
            print "Error: ";
            print errstr;
            print "\n";
            false
            )


      fun invert inspan msg =
         let
            val span =
               InvertRC.invert [] (!oldProg) inspan

            val src = !oldInput

            val (rcs as ((row1, col1), (row2, col2))) =
               RowCol.fromSpan src span
               handle Error.NotFound =>
                  (* This really shouldn't happen, since we just found it. *)
                  ((1, #1 span), (1, #2 span))
         in
            print (String.concat [Int.toString row1, ".", Int.toString col1,
                                  "-",
                                  Int.toString row2, ".", Int.toString col2]);
            print msg;

            RowCol.display src rcs
         end
         handle NotFound =>
            (* Hopefully this never happens, but if it does, we'd like to print *something*. *)
            (
            print "<location not found>";
            print msg
            )

   end
