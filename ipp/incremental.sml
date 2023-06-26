
signature INCREMENTAL =
   sig

      type token
      type program
      type receipt

      val lex : char Stream.stream -> Span.pos -> token Stream.stream
      val parse : token Stream.stream -> program * token Stream.stream
      val span : program -> Span.span

      (* compile a program, update context *)
      val compile : program -> receipt

      (* update context according to the provided code without generating output code *)
      val consult : string -> receipt

      (* update context for compiled project files *)
      val load : string -> unit

      (* undo the last interaction *)
      val undo : unit -> unit

      (* set IPP context as indicated *)
      val reset : Context.context -> unit

      (* showErrorMesasage p span source name msg

         Inverts the span for p.
         Takes the resulting (original) span and displays context for the
         error context drawn from source.  Uses name (if SOME) for the file name.
      *)
      val showErrorMessage : receipt -> Span.span -> ShowContext.source -> string option -> string -> unit

      (* where to put compiled code *)
      val outputStream : (unit -> TextIO.outstream) ref

   end


structure Incremental :> INCREMENTAL =
   struct

      structure S = Stream

      type token = Token.token
      type program = Syntax.program
      type receipt = Syntax.program

      
      val lex = Lexer.lexRepl
      val parse = Parser.parseIncremental

      fun span (_, sp) = sp

      
      val outputStream : (unit -> TextIO.outstream) ref = ref (fn () => raise (Fail "unimplemented"))


      val initial = Initial.basis (!Language.target) (!Language.smlCompatibility)

      val nullspan = (Span.origin, Span.origin)

      val theContext = ref initial
      val oldContext = ref initial
      val lastProgram : Syntax.program ref = ref ([], (Span.origin, Span.origin))


      fun compile p =
         let
            val ctx = !theContext
            val (p', ctx', _) = Traverse.traverse ctx p
            val outs = !outputStream ()
         in
            theContext := ctx';
            oldContext := ctx;
            Render.render outs [] p';
            TextIO.closeOut outs;
            p'
         end
      

      fun consult code =
         let
            val (p, _) = parse (lex (Stream.fromString code) Span.origin)

            val ctx = !theContext
            val (p', ctx', _) = Traverse.traverse ctx p
         in
            theContext := ctx';
            oldContext := ctx;
            p'
         end
      

      fun load projname =
         let
            val ctx = !theContext
            val ctx' = Context.union ctx (Make.load projname)
         in
            theContext := ctx';
            oldContext := ctx
         end


      fun undo () =
         theContext := !oldContext


      fun reset ctx =
         (
         theContext := ctx;
         oldContext := ctx
         )


      fun showErrorMessage p inspan source sourcename msg =
         let
            val span as ((row1, col1), (row2, col2)) =
               InvertRC.invert [] p inspan
         in
            (case sourcename of
                NONE => ()
              | SOME name =>
                   (
                   print name;
                   print ":"
                   ));

            print (Int.toString row1);
            print ".";
            print (Int.toString col1);
            print "-";
            print (Int.toString row2);
            print ".";
            print (Int.toString col2);
            print msg;
            print "\n";

            ShowContext.display source span
         end

   end
