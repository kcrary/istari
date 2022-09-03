
signature DOCGEN =
   sig

      val gen : TextIO.outstream -> Syntax.clause list -> unit

   end


structure Docgen :> DOCGEN =
   struct

      open Syntax

      fun appsep f g l =
         (case l of
             [] => ()

           | [x] => f x

           | x :: rest =>
                (
                f x;
                app (fn y => (g (); f y)) rest
                ))

      val precMin = 0
      val precLam = 2
      val precEq = 140
      val precApp = 180
      val precMax = 200

      fun lparen write prec prec' =
         if prec' < prec then
            write "("
         else
            ()

      fun rparen write prec prec' =
         if prec' < prec then
            write ")"
         else
            ()

      
      fun toSpine m acc =
         (case m of
             App (m1, m2) =>
                toSpine m1 (m2 :: acc)

           | _ => (m, acc))


      fun writeTerm write prec m =
         (case m of
             Var sym =>
                write (Symbol.toValue sym)

           | Const sym =>
                (
                write "{\\sf ";
                write (Symbol.toValue sym);
                write "}"
                )

           | Metavar (sym, []) =>
                write (Symbol.toValue sym)

           | Metavar (sym, sub) =>
                (
                writeSub write sub;
                write (Symbol.toValue sym)
                )
                
           | Lam (x, m1) =>
                (
                lparen write prec precLam;
                write "\\lambda ";
                write (Symbol.toValue x);
                write ".\\,";
                writeTerm write precLam m1;
                rparen write prec precLam
                )

           | App _ =>
                (case toSpine m [] of
                    (Const "of", [m1, m2]) =>
                       (
                       lparen write prec precEq;
                       writeTerm write (precEq+1) m2;
                       write ": ";
                       writeTerm write (precEq+1) m1;
                       rparen write prec precEq
                       )
                          
                  | (Const "istp", [m1]) =>
                       (
                       lparen write prec precEq;
                       writeTerm write (precEq+1) m1;
                       write ": {\\sf type}";
                       rparen write prec precEq
                       )

                  | (Const "eq", [m1, m2, m3]) =>
                       (
                       lparen write prec precEq;
                       writeTerm write (precEq+1) m2;
                       write "= ";
                       writeTerm write (precEq+1) m3;
                       write ": ";
                       writeTerm write (precEq+1) m1;
                       rparen write prec precEq
                       )
                          
                  | (Const "eqtp", [m1, m2]) =>
                       (
                       lparen write prec precEq;
                       writeTerm write (precEq+1) m1;
                       write "= ";
                       writeTerm write (precEq+1) m2;
                       write ": {\\sf type}";
                       rparen write prec precEq
                       )

                  | (Const "univ", [m]) =>
                       (
                       write "{\\Bbb U}_{";
                       writeTerm write precMin m;
                       write "}"
                       )

                  | (Const "kind", [m]) =>
                       (
                       write "{\\Bbb K}_{";
                       writeTerm write precMin m;
                       write "}"
                       )

                  | (Const sym, [m1, Lam (x, m2)]) =>
                       (
                       lparen write prec precApp;
                       write "{\\sf ";
                       write (Symbol.toValue sym);
                       write "}\\,\\{";
                       write (Symbol.toValue x);
                       write " : ";
                       writeTerm write precMin m1;
                       write "\\}\\,";
                       writeTerm write (precApp+1) m2;
                       rparen write prec precApp
                       )

                  | (n, spine) =>
                       (
                       lparen write prec precApp;
                       writeTerm write precApp n;
              
                       List.app
                          (fn n =>
                              (
                              write "\\,";
                              writeTerm write (precApp+1) n
                              ))
                          spine;
                              
                       rparen write prec precApp
                       ))

           | Pair (m1, m2) =>
                (
                write "\\langle ";
                writeTerm write precMin m1;
                write ",";
                writeTerm write precMin m2;
                write "\\rangle "
                )

           | Pi1 m1 =>
                (
                lparen write prec precApp;
                writeTerm write precApp m1;
                write "\\, \\pi_1";
                rparen write prec precApp
                )

           | Pi2 m1 =>
                (
                lparen write prec precApp;
                writeTerm write precApp m1;
                write "\\, \\pi_2";
                rparen write prec precApp
                )

           | Next m1 =>
                (
                lparen write prec precApp;
                write "{\\sf next}\\,";
                writeTerm write (precApp+1) m1;
                rparen write prec precApp
                )

           | Prev m1 =>
                (
                lparen write prec precApp;
                writeTerm write precApp m1;
                write "\\, {\\sf prev}";
                rparen write prec precApp
                )

           | Triv =>
                write "\\star ")

      and writeSub write sub =
         (
         write "[";

         appsep
            (fn (n, _) => writeTerm write precMin n)
            (fn () => write ", ")
            sub;

         write "/";

         appsep
            (fn (_, x) => write x)
            (fn () => write ", ")
            sub;

         write "]"
         )



      fun writeClass write h =
         (case h of
             Tm a =>
                writeTerm write precMax a

           | Tml a => 
                (
                write "\\underline{";
                writeTerm write precMax a;
                write "}"
                )

           | Tmh a => 
                (
                write "[";
                writeTerm write precMax a;
                write "]"
                )

           | Tp =>
                write "{\\sf type}"

           | Tpl =>
                write "\\underline{\\sf type}"

           | Tph =>
                write "[{\\sf type}]")
                

      fun writeHyp write (sym, class) =
         (
         write (Symbol.toValue sym);
         write "\\mathord{:}";
         writeClass write class
         )

      fun writeRule write name (premises, concl, ext) =
         (
         write "\\[\n\\infer[{\\tt ";
         write (Symbol.toValue name);      
         write "}]{";

         write "\\Gamma \\vdash ";
         writeTerm write precMin concl;

         (case ext of
             Triv => ()

           | _ =>
                (
                write "\\:{\\sf ext}\\:";
                writeTerm write precMin ext
                ));

         write "}{";

         if null premises then
            ()
         else
            (
            write "\n\\begin{stack}\n";
            
            appsep
               (fn (promote, hyps, rhs, extv) =>
                   (
                   if promote then
                      write "\\overline{\\Gamma}"
                   else
                      write "\\Gamma ";
   
                   List.app (fn hyp => (write ","; writeHyp write hyp)) (rev hyps);
   
                   write "\\vdash ";
                   writeTerm write precMin rhs;
   
                   (case extv of
                       NONE => ()
   
                     | SOME ext =>
                          (
                          write "\\:{\\sf ext}\\:";
                          write (Symbol.toValue ext)
                          ));
   
                   write "\n"
                   ))
               (fn () => write "\\\\\n")
               premises;
   
            write "\\end{stack}"
            );

         write "}\n\\]\n\n"
         )

      fun writeLRule write name (premises, hyps, concl, ext) =
         (
         write "\\[\n\\infer[{\\tt ";
         write (Symbol.toValue name);      
         write "}]{";

         write "\\Gamma_1 ";
         
         List.app (fn hyp => (write ","; writeHyp write hyp)) (rev hyps);

         write ", \\Gamma_2 \\vdash ";
         writeTerm write precMin concl;

         (case ext of
             Triv => ()

           | _ =>
                (
                write "\\:{\\sf ext}\\:";
                writeTerm write precMin ext
                ));

         write "}{";

         if null premises then
            ()
         else
            (
            write "\n\\begin{stack}\n";
            
            appsep
               (fn (promote, hyps, subo, rhs, extv) =>
                   (
                   if promote then
                      write "\\overline{\\Gamma_1}"
                   else
                      write "\\Gamma_1 ";
   
                   List.app (fn hyp => (write ","; writeHyp write hyp)) (rev hyps);

                   (case subo of
                       NONE => ()

                     | SOME [] =>
                          write ", \\Gamma_2"

                     | SOME sub =>
                          (
                          write ", ";
                          writeSub write sub;
                          write "\\Gamma_2"
                          ));
   
                   write "\\vdash ";
                   writeTerm write precMin rhs;
   
                   (case extv of
                       NONE => ()
   
                     | SOME ext =>
                          (
                          write "\\:{\\sf ext}\\:";
                          write (Symbol.toValue ext)
                          ));
   
                   write "\n"
                   ))
               (fn () => write "\\\\\n")
               premises;
   
            write "\\end{stack}"
            );

         write "}\n\\]\n\n"
         )

      fun gen outs rules =
         let
            fun write str = TextIO.output (outs, str)
         in
            write "% This file is generated by Rulegen.\n\n";

            List.app
               (fn Rule (name, rule) => writeRule write name rule
                 | LRule (name, rule) => writeLRule write name rule)
               rules
         end

   end
