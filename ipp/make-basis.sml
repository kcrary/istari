
CM.make "sources.cm";

structure MakeBasis =
   struct

      structure PC = PreContext
      structure PP = PrettyPrint

      structure P = ParsingFun (type token = string
                                structure Streamable =
                                   MonomorphizeStreamable (structure Streamable = StreamStreamable
                                                           type elem = string))
      

      val s2v = Symbol.toValue
      val indent = 3
      val initialIndent = 3 + indent
      val width = 60


      fun mkstream ins =
         Stream.lazy
         (fn () =>
             (case TextIO.input1 ins of
                 NONE => Stream.Nil

               | SOME #"\^@" =>
                    Stream.Nil

               | SOME ch =>
                    Stream.Cons (ch, mkstream ins)))


      (* quick-and-dirty lexer *)
      fun qad ins =
         Stream.lazy
         (fn () => qadSpace ins)

      and qadSpace ins =
         (case TextIO.input1 ins of
             NONE => 
                Stream.Nil

           | SOME #"\^@" =>
                Stream.Nil

           | SOME ch =>
                if Char.isSpace ch then
                   qadSpace ins
                else
                   qadChars ins [ch])

      and qadChars ins acc =
         (case TextIO.input1 ins of
             NONE =>
                Stream.Cons (String.implode (rev acc), Stream.eager Stream.Nil)

           | SOME #"\^@" =>
                Stream.Cons (String.implode (rev acc), Stream.eager Stream.Nil)

           | SOME ch =>
                if Char.isSpace ch then
                   Stream.Cons (String.implode (rev acc), qad ins)
                else
                   qadChars ins (ch :: acc))


      val parser =
         P.many
            (P.andthen2
                (P.wrap (String.fields (fn ch => ch = #".")) P.accept,
                 P.wrap (String.fields (fn ch => ch = #".")) P.accept))


      fun writeItem pp sprefix item =
         (case item of
             PC.VAL ((sym, _), n) =>
                (
                PP.print pp "(\"";
                PP.print pp (s2v sym);
                PP.print pp "\", E ";
                PP.print pp (Int.toString n);
                PP.print pp ")"
                )
             
           | PC.TYPE (sym, _) =>
                (
                PP.print pp "(\"";
                PP.print pp (s2v sym);
                PP.print pp "\", T)"
                )

           (* Since all signatures must appear at the top-level, we may rely on them being
              bound to names.
           *)
           | PC.SIG ((sym, _), _) =>
                (
                PP.print pp "(\"";
                PP.print pp (s2v sym);
                PP.print pp "\", S ";
                PP.print pp sprefix;
                PP.print pp (s2v sym);
                PP.print pp ")"
                )

           | PC.MOD ((sym, _), class) =>
                (
                PP.print pp "(\"";
                PP.print pp (s2v sym);
                PP.print pp "\", M ";
                writeClass pp sprefix class;
                PP.print pp ")"
                )

           | PC.FUN _ =>
                raise (Fail "basis functors unsupported"))

      and writeContext pp sprefix items =
         (case items of
             [] =>
                PP.print pp "C.empty"

           | item :: rest =>
                (
                PP.openBox pp PP.Consistent 0;
                PP.print pp "[";
                PP.openBox pp PP.Consistent 0;
                writeItem pp sprefix item;
                app (fn item' =>
                        (
                        PP.print pp ",";
                        PP.break pp 1;
                        writeItem pp sprefix item'
                        ))
                   rest;
                PP.closeBox pp;
                PP.print pp "]";
                PP.closeBox pp
                ))

      and writeClass pp sprefix class =
         (case class of
             PC.LIST items => writeContext pp sprefix items

           | PC.NAME (sym, _) =>
                (
                PP.print pp sprefix;
                PP.print pp (s2v sym)
                ))


      fun appWith f g l =
         (case l of
             nil => ()

           | h :: t =>
                (
                f h;
                app (fn x => (g (); f x)) t
                ))


      fun printStrings pp l =
         (
         PP.print pp "[";
         appWith
            (fn str =>
                (
                PP.print pp "\"";
                PP.print pp (String.toString str);
                PP.print pp "\""
                ))
            (fn () => PP.print pp ", ")
            l;
         PP.print pp "]"
         )


      fun render outs ctx1 ctx2 =
         let
            val pp = PP.makeStreamIndent outs width initialIndent
         in
            TextIO.output (outs,
               "\n\
               \(* This file is generated by make-basis.sml. *)\n\
               \\n\
               \functor TheBasis (datatype data = \n\
               \                     E of int\n\
               \                   | EQ of string list * int\n\
               \                   | T\n\
               \                   | TQ of string list\n\
               \                   | S of (string * data) list\n\
               \                   | M of (string * data) list)\n\
               \   :>\n\
               \   sig\n\
               \      val basis1 : (string * data) list\n\
               \      val basis2 : (string * data) list\n\
               \   end\n\
               \   =\n\
               \   struct\n");
            PP.openBox pp PP.Vertical 0;
            PP.newline pp;
      
            app
               (fn PC.SIG ((sym, _), class) =>
                      (
                      PP.openBox pp PP.Consistent indent;
                      PP.print pp "val sig1_";
                      PP.print pp (s2v sym);
                      PP.print pp " =";
                      PP.break pp 1;
                      writeClass pp "sig1_" class;
                      PP.closeBox pp;
                      PP.newline pp;
                      PP.newline pp
                      )
                 | _ => ())
               ctx1;
      
            PP.openBox pp PP.Consistent indent;
            PP.print pp "val basis1 =";
            PP.break pp 1;
            writeContext pp "sig1_" ctx1;
            PP.closeBox pp;
            PP.newline pp;
            PP.newline pp;
      
            app
               (fn PC.SIG ((sym, _), class) =>
                      (
                      PP.openBox pp PP.Consistent indent;
                      PP.print pp "val sig2_";
                      PP.print pp (s2v sym);
                      PP.print pp " =";
                      PP.break pp 1;
                      writeClass pp "sig2_" class;
                      PP.closeBox pp;
                      PP.newline pp;
                      PP.newline pp
                      )
                 | _ => ())
               ctx2;
      
            PP.openBox pp PP.Consistent indent;
            PP.print pp "val basis2 =";
            PP.break pp 1;
            writeContext pp "sig2_" ctx2;
            PP.closeBox pp;
            PP.newline pp;

            PP.closeBox pp;
            TextIO.output (outs, "\n   end\n")
         end
      

      fun go () =
         let
            val ins = TextIO.openIn "basis/BASIS"
         in
            Finally.finally
            (fn () =>
                let
                   (* After each, the lexer will read up through the closing null then stop. *)

                   val ctx1 = Parser.parseIpc (mkstream ins)
                   val ctx2 = Parser.parseIpc (mkstream ins)

                   val outs = TextIO.openOut "the-basis.sml"
                in
                   Finally.finally
                   (fn () => render outs ctx1 ctx2)
                   (fn () => TextIO.closeOut outs)
                 end)
            (fn () => TextIO.closeIn ins);

            print "the-basis.sml written\n"
         end

   end

val () = MakeBasis.go ();

OS.Process.exit OS.Process.success : unit;
