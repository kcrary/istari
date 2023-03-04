
signature MAIN =
   sig

      val parse : unit -> Syntax.clause list
      val elaborate : unit -> Rule.clause list
      val rulegen : unit -> unit
      val lemmagen : unit -> unit
      val docgen : unit -> unit
      val docgendb : unit -> unit
      val webgen : unit -> unit
      val webgendb : unit -> unit
      val gen : unit -> unit

   end


structure Main :> MAIN =
   struct

      fun parse () =
         let
            val ins = TextIO.openIn "../prover/trusted/RULES"
         in
            Finally.finally
               (fn () => Parser.parse (Stream.fromTextInstream ins))
               (fn () => TextIO.closeIn ins)
            handle
            exn as (Parser.SyntaxError pos) =>
               (
               print "Syntax error at ";
               print (Int.toString pos);
               print "\n";
               raise exn
               )

         end

      fun elaborate () =
         map Elaborate.elaborate (parse ())

      fun rulegen () =
         let
            val rules = elaborate ()
            val outs = TextIO.openOut "../prover/trusted/the-rules.iml"
         in
            Finally.finally
               (fn () => Rulegen.gen outs rules)
               (fn () => TextIO.closeOut outs)
         end

      fun lemmagen () =
         let
            val rules = elaborate ()
            val outs = TextIO.openOut "../coq/Obligations.v"
         in
            Finally.finally
               (fn () => Lemmagen.gen outs rules)
               (fn () => TextIO.closeOut outs)
         end

      fun docgen () =
         let
            val rules = parse ()
            val outs = TextIO.openOut "../rules/the-rules.tex"
         in
            Finally.finally
               (fn () => Docgen.gen outs rules)
               (fn () => TextIO.closeOut outs)
         end

      fun docgendb () =
         let
            val rules = elaborate ()
            val outs = TextIO.openOut "../rules/the-rules-db.tex"
         in
            Finally.finally
               (fn () => DocgenDB.gen outs rules)
               (fn () => TextIO.closeOut outs)
         end

      fun webgen () =
         let
            val rules = parse ()
            val outs = TextIO.openOut "../rules/rules.md"
         in
            Finally.finally
               (fn () => Webgen.gen outs rules)
               (fn () => TextIO.closeOut outs)
         end

      fun webgendb () =
         let
            val rules = elaborate ()
            val outs = TextIO.openOut "../rules/rules-db.md"
         in
            Finally.finally
               (fn () => WebgenDB.gen outs rules)
               (fn () => TextIO.closeOut outs)
         end

      fun gen () =
         let
            val rules = parse ()
            val rules' = map Elaborate.elaborate rules
         in
            let
               val outs = TextIO.openOut "../prover/trusted/the-rules.iml"
            in
               Finally.finally
                  (fn () => Rulegen.gen outs rules')
                  (fn () => TextIO.closeOut outs)
            end;

            let
               val outs = TextIO.openOut "../coq/Obligations.v"
            in
               Finally.finally
                  (fn () => Lemmagen.gen outs rules')
                  (fn () => TextIO.closeOut outs)
            end;

            let
               val outs = TextIO.openOut "../rules/the-rules.tex"
            in
               Finally.finally
                  (fn () => Docgen.gen outs rules)
                  (fn () => TextIO.closeOut outs)
            end;

            let
               val outs = TextIO.openOut "../rules/the-rules-db.tex"
            in
               Finally.finally
                  (fn () => DocgenDB.gen outs rules')
                  (fn () => TextIO.closeOut outs)
            end;

            let
               val outs = TextIO.openOut "../rules/rules.md"
            in
               Finally.finally
                  (fn () => Webgen.gen outs rules)
                  (fn () => TextIO.closeOut outs)
            end;

            let
               val outs = TextIO.openOut "../rules/rules-db.md"
            in
               Finally.finally
                  (fn () => WebgenDB.gen outs rules')
                  (fn () => TextIO.closeOut outs)
            end
         end

   end
