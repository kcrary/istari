
structure Tags :>
   sig 
      val tag : string -> TextIO.outstream -> unit 
   end
   =
   struct

      structure S = Syntax

      val dummy = ((0, 0), (0, 0))


      val andSym = Symbol.fromValue "and"

      val barSym = Symbol.fromValue "|"

      val defineIndSym = Symbol.fromValue "defineInd"

      val lemmaSym = Symbol.fromValue "lemma"

      val ofSym = Symbol.fromValue "of"

      val typedefSym = Symbol.fromValue "typedef"

      val defineSyms = 
         map Symbol.fromValue ["define", "defineRaw", "definerec", "definerecRaw"]



      fun member sym l =
         List.exists (fn sym' => Symbol.eq (sym, sym')) l


      fun find trigger elements acc =
         (case elements of
             [] => acc

           | [_] => acc

           | elem :: (rest as (S.Lident (name, span) :: rest')) =>
                if trigger elem then
                   find trigger rest' ((Symbol.toValue name, span) :: acc)

                else
                   find trigger rest acc

           | _ :: rest =>
                find trigger rest acc)


      fun drop trigger elements =
         (case elements of
             [] => []

           | elem :: rest =>
                if trigger elem then
                   rest
                else
                   drop trigger rest)


      fun proc (exp_, _) =
         (case exp_ of
             S.Ejuxta ((S.Jident ((sym, _), _), _) :: args) =>
                if member sym defineSyms then
                   (case args of
                       (S.Jatom (S.Eterm (S.Lident (name, span) :: _), _), _) :: _ =>
                          [(Symbol.toValue name, span)]

                     | _ => [])

                else if Symbol.eq (sym, lemmaSym) then
                   (case args of
                       (S.Jatom (S.Estring name, span), _) :: _ =>
                          [(name, span)]

                     | _ => [])

                else if Symbol.eq (sym, defineIndSym) then
                   (case args of
                       _ :: (S.Jatom (S.Eterm elems, _), _) :: _ =>
                          find
                             (fn (S.Lident (sym, _)) => Symbol.eq (sym, andSym)
                               | _ => false)
                             (S.Lident (andSym, dummy) :: elems) []

                     | _ => [])

                else if Symbol.eq (sym, typedefSym) then
                   (case args of
                       (S.Jatom (S.Eterm elems, _), _) :: _ =>
                          find
                             (fn (S.Lident (sym, _)) => Symbol.eq (sym, andSym)
                               | (S.Llexeme (sym, _)) => Symbol.eq (sym, barSym)
                               | _ => false)
                             (S.Lident (andSym, dummy) ::
                              drop 
                                 (fn (S.Lident (sym, _)) => Symbol.eq (sym, ofSym)
                                   | _ => false)
                                 elems)
                             []

                     | _ => [])

                else
                   []

           | _ => [])
                

      fun innerLoop directives acc =
         (case directives of
             [] => acc

           | (S.Vexp exp, _) :: rest =>
                innerLoop rest (proc exp @ acc)

           | _ :: rest =>
                innerLoop rest acc)


      fun outerLoop filename s acc =
         (case Stream.front s of
             Stream.Nil =>
                List.rev acc

           | _ =>
                let
                   val ((directives, _), s') = 
                      Parser.parseIncremental s
                      handle Error.Error _ =>
                         (
                         print filename;
                         print " contains syntax errors, aborted\n";
                         (([], dummy), Stream.eager Stream.Nil)
                         )

                   val acc' = innerLoop directives acc
                in
                   outerLoop filename s' acc'
                end)


      fun readLine ins acc =
         (case TextIO.input1 ins of
             NONE =>
                String.implode (List.rev acc)

           | SOME ch =>
                if ch = #"\n" then
                   String.implode (List.rev (ch :: acc))
                else
                   readLine ins (ch :: acc))


      fun lineStream pos ins =
         Stream.lazy
         (fn () =>
             let
                val str = readLine ins []
             in
                if String.size str = 0 then
                   Stream.Nil
                else
                   Stream.Cons ((pos, str),
                                lineStream (pos + String.size str) ins)
             end)


      val ch1 = String.str (Char.chr 1)
      val ch12 = String.str (Char.chr 12)
      val ch127 = String.str (Char.chr 127)


      fun outputLoop defs lineno s outsize acc =
         (case defs of
             [] =>
                (outsize, List.rev acc)

           | (name, ((r1, _), (r2, c2))) :: rest =>
                if r1 = r2 andalso lineno <= r1 then
                   let
                      val s' = Stream.drop (s, r1 - lineno)

                      val (sol, line) =
                         (case Stream.front s' of
                             Stream.Cons ((pos, str), _) => (pos, str)

                           | Stream.Nil => raise (Fail "impossible"))

                      (* add an extra character so we don't get prefixes of the target *)
                      val col =
                         if c2 + 1 = String.size line then
                            c2
                         else
                            c2 + 1

                      val str =
                         String.concat
                            [
                            String.substring (line, 0, col),
                            ch127,
                            name,
                            ch1,
                            Int.toString r1,
                            ",",
                            Int.toString (sol+1),
                            "\n"
                            ]
                   in
                      outputLoop rest r1 s' (outsize + String.size str) (str :: acc)
                   end
                else
                   (* We shouldn't see an identifier that crosses a newline
                      or a definition out of order, but if we do, discard.
                   *)
                   outputLoop rest lineno s outsize acc)


      fun tag infile outs =
         let
            val ins =
               TextIO.openIn infile
               handle
                  IO.Io _ =>
                     (
                     print "Unable to open file ";
                     print infile;
                     print "\n";
                     OS.Process.exit OS.Process.failure
                     )

            val s = Lexer.lexUse (Stream.fromTextInstream ins)
            val defs = outerLoop infile s []
            val () = TextIO.closeIn ins

            val ins = TextIO.openIn infile
            val lines = lineStream 0 ins
            val (outsize, output) = outputLoop defs 1 lines 0 []
            val () = TextIO.closeIn ins

            fun write str = TextIO.output (outs, str)

            val (_, basename) = Path.split infile
         in
            write ch12;
            write "\n";
            write basename;
            write ",";
            write (Int.toString outsize);
            write "\n";
            List.app write output
         end

   end


structure TagsCommandLine :>
   sig
      val main : string list -> OS.Process.status
   end
   =
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
         print "istaritags usage:\n\
               \  istaritags [options] <istari-file> ...\n\
               \  -o <filename>  set output file name (otherwise TAGS)\n\
               \  -a             append to existing tag file\n";

         exit ()
         )

      val infileKey : string C.list_key = 
         C.mapKeyIn fromHybridPath (C.key C.list)

      val outfileKey : string C.id_key = 
         C.mapKeyIn fromHybridPath (C.key (C.default "TAGS"))

      val appendKey : bool C.id_key = C.key (C.default false)

      val parser =
         C.or
         [
         C.map usage C.eof,

         C.foldCompose
            (C.or
                [
                C.map usage (C.exactly "--help"),

                C.stringOpt "-o" outfileKey,
                C.unitOpt "-a" appendKey true,

                C.map (fn name => C.write infileKey name) C.nohyph
                ])
         ]


      fun main args =
         let
            val log = C.parse parser args C.blank
         in
            (case C.read infileKey log of
                nil =>
                   usage ()

              | infiles =>
                   let
                      val outfile = C.read outfileKey log
          
                      val outs =
                         if C.read appendKey log then
                            TextIO.openAppend outfile
                         else
                            TextIO.openOut outfile
                   in
                      List.app (fn infile => Tags.tag infile outs) infiles;

                      TextIO.closeOut outs;
                      OS.Process.success
                   end)
         end

   end
