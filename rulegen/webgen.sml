
signature WEBGEN =
   sig

      val gen : TextIO.outstream -> Syntax.clause list -> unit

   end


structure Webgen :> WEBGEN =
   struct

      structure S = RedBlackSet (structure Elem = SymbolOrdered)

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
      val precLam = 0
      val precOf = 0
      val precEq = 30
      val precApp = 90
      val precMax = 100



      fun metavars m =
         (case m of
             Var _ => S.empty

           | Const _ => S.empty

           | Metavar (sym, s) => S.insert (metavarsSub s) sym

           | Lam (_, m) => metavars m

           | App (m1, m2) => S.union (metavars m1) (metavars m2)

           | Pair (m1, m2) => S.union (metavars m1) (metavars m2)

           | Pi1 m1 => metavars m1

           | Pi2 m1 => metavars m1

           | Next m1 => metavars m1

           | Prev m1 => metavars m1

           | Triv => S.empty)

      and metavarsSub s =
         List.foldl
            (fn ((m, _), set) =>
                S.union (metavars m) set)
            S.empty
            s

      and metavarsHyp (_, h) =
         (case h of
             Tm m => metavars m
           | Tml m => metavars m
           | Tmh m => metavars m
           | Tp => S.empty
           | Tpl => S.empty
           | Tph => S.empty)




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


      fun writeVar write v = write v



      fun writeTerm write prec m =
         (case m of
             Var sym =>
                writeVar write (Symbol.toValue sym)

           | Const sym =>
                write (Symbol.toValue sym)

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
                write "fn ";
                writeVar write (Symbol.toValue x);
                write " . ";
                writeTerm write precLam m1;
                rparen write prec precLam
                )

           | App _ =>
                (case toSpine m [] of
                    (Const head, spine) =>
                       (case head of
                           "of" => writeOf
                         | "istp" => writeIstp
                         | "eq" => writeEq
                         | "eqtp" => writeEqtp
                         | "forall" => writeBinder "forall"
                         | "exists" => writeBinder "exists"
                         | "intersect" => writeBinder "intersect"
                         | "wtype" => writeBinder "wtype"
                         | "iforall" => writeIBinder "iforall"
                         | "iexists" => writeIBinder "iexists"
                         | "foralltp" => writeBinderBare "foralltp"
                         | "rec" => writeBinderBare "rec"
                         | "mu" => writeBinderBare "mu"
                         | "arrow" => writeInfixR 0 "->"
                         | "tarrow" => writeInfixR 0 "-t>"
                         | "karrow" => writeInfixR 0 "-k>"
                         | "guard" => writeInfixR 0 "-g>"
                         | "sum" => writeInfixR 15 "%"
                         | "prod" => writeInfixR 20 "&"
                         | "subtype" => writeInfixN 30 "<:"
                         | "lleq" => writeInfixN 30 "<l="
                         | "set" => writeSet
                         | "quotient" => writeQuotient
                         | "squash" => writeSquash
                         | _ => writePath)
                       head write prec spine

                  | (n, spine) =>
                       (
                       lparen write prec precApp;
                       writeTerm write precApp n;
              
                       List.app
                          (fn n =>
                              (
                              write " ";
                              writeTerm write (precApp+1) n
                              ))
                          spine;
                              
                       rparen write prec precApp
                       ))

           | Pair (m1, m2) =>
                (
                write "(";
                writeTerm write precMin m1;
                write " , ";
                writeTerm write precMin m2;
                write ")"
                )

           | Pi1 m1 =>
                (
                lparen write prec precApp;
                writeTerm write precApp m1;
                write " #1";
                rparen write prec precApp
                )

           | Pi2 m1 =>
                (
                lparen write prec precApp;
                writeTerm write precApp m1;
                write " #2";
                rparen write prec precApp
                )

           | Next m1 =>
                (
                lparen write prec precApp;
                write "next ";
                writeTerm write (precApp+1) m1;
                rparen write prec precApp
                )

           | Prev m1 =>
                (
                lparen write prec precApp;
                writeTerm write precApp m1;
                write " #prev";
                rparen write prec precApp
                )

           | Triv =>
                write "()")

         
      and writePath head write prec spine =
         (
         lparen write prec precApp;
         write head;

         List.app
            (fn n =>
                (
                write " ";
                writeTerm write (precApp+1) n
                ))
            spine;
                
         rparen write prec precApp
         )

         
      and writeOf _ write prec spine =
         (case spine of
             [m1, m2] =>
                (
                lparen write prec precOf;
                writeTerm write (precOf+1) m2;
                write " : ";
                writeTerm write precOf m1;
                rparen write prec precOf
                )

           | _ => writePath "of" write prec spine)


      and writeIstp _ write prec spine =
         (case spine of
             [m1] =>
                (
                lparen write prec precOf;
                writeTerm write (precOf+1) m1;
                write " : type";
                rparen write prec precOf
                )

           | _ => writePath "istp" write prec spine)


      and writeEq _ write prec spine =
         (case spine of
             [m1, m2, m3] =>
                (
                lparen write prec precEq;
                writeTerm write (precEq+1) m2;
                write " = ";
                writeTerm write (precEq+1) m3;
                write " : ";
                writeTerm write (precEq+1) m1;
                rparen write prec precEq
                )

           | _ => writePath "eq" write prec spine)


      and writeEqtp _ write prec spine =
         (case spine of
             [m1, m2] =>
                (
                lparen write prec precEq;
                writeTerm write (precEq+1) m1;
                write " = ";
                writeTerm write (precEq+1) m2;
                write " : type";
                rparen write prec precEq
                )

           | _ => writePath "eqtp" write prec spine)


      and writeInfix precOper precL precR oper head write prec spine =
         (case spine of
             [m1, m2] =>
                (
                lparen write prec precOper;
                writeTerm write precL m1;
                write " ";
                write oper;
                write " ";
                writeTerm write precR m2;
                rparen write prec precOper
                )

           | _ => writePath head write prec spine)


      and writeInfixL precOper oper head write prec spine =
         writeInfix precOper precOper (precOper+1) oper head write prec spine


      and writeInfixR precOper oper head write prec spine =
         writeInfix precOper (precOper+1) precOper oper head write prec spine


      and writeInfixN precOper oper head write prec spine =
         writeInfix precOper (precOper+1) (precOper+1) oper head write prec spine


      and writeBinder oper head write prec spine =
         (case spine of
             [m1, Lam (x, m2)] =>
                (
                lparen write prec precMin;
                write oper;
                write " (";
                writeVar write x;
                write " : ";
                writeTerm write precMin m1;
                write ") . ";
                writeTerm write precMin m2;
                rparen write prec precMin
                )

           | _ => writePath head write prec spine)


      and writeIBinder oper head write prec spine =
         (case spine of
             [m1, m2, Lam (x, m3)] =>
                (
                lparen write prec precMin;
                write oper;
                write " ";
                writeTerm write (precApp+1) m1;
                write " (";
                writeVar write x;
                write " : ";
                writeTerm write precMin m2;
                write ") . ";
                writeTerm write precMin m3;
                rparen write prec precMin
                )

           | _ => writePath head write prec spine)


      and writeBinderBare oper head write prec spine =
         (case spine of
             [Lam (x, m1)] =>
                (
                lparen write prec precMin;
                write oper;
                write " ";
                writeVar write x;
                write " . ";
                writeTerm write precMin m1;
                rparen write prec precMin
                )

           | _ => writePath head write prec spine)


      and writeSet _ write prec spine =
         (case spine of
             [m1, Lam (x, m2)] =>
                (
                write "{";
                writeVar write x;
                write " : ";
                writeTerm write precMin m1;
                write " | ";
                writeTerm write precMin m2;
                write "}"
                )

           | _ => writePath "set" write prec spine)


      and writeQuotient _ write prec spine =
         (case spine of
             [m1, Lam (x, Lam (y, m2))] =>
                (
                lparen write prec precMin;
                write "quotient (";
                writeVar write x;
                write " ";
                writeVar write y;
                write " : ";
                writeTerm write precMin m1;
                write ") . ";
                writeTerm write precMin m2;
                rparen write prec precMin
                )

           | _ => writePath "quotient" write prec spine)


      and writeSquash _ write prec spine =
         (case spine of
             [m1] =>
                (
                write "{";
                writeTerm write precMin m1;
                write "}"
                )

           | _ => writePath "set" write prec spine)


      and writeSub write sub =
         (
         write "[";

         appsep
            (fn (n, _) => writeTerm write precMin n)
            (fn () => write ", ")
            sub;

         write " / ";

         appsep
            (fn (_, x) => writeVar write x)
            (fn () => write ", ")
            sub;

         write "]"
         )



      fun writeClass write h =
         (case h of
             Tm a =>
                (
                write " : ";
                writeTerm write precMax a
                )

           | Tml a => 
                (
                write " (later) : ";
                writeTerm write precMax a
                )

           | Tmh a => 
                (
                write " (hidden) : ";
                writeTerm write precMax a
                )

           | Tp =>
                write " : type"

           | Tpl =>
                write " (later) : type"

           | Tph =>
                write " (hidden) : type")
                

      fun writeHyp write (sym, class) =
         (
         writeVar write (Symbol.toValue sym);
         writeClass write class
         )


      fun writeRule write name (premises, concl, ext) =
         (
         write "- `";
         write (Symbol.toValue name);      

         List.app
            (fn v =>
                (
                write " ";
                write v
                ))
            (Juliasort.sort 
                String.compare
                (List.map Symbol.toValue
                    (S.toList
                        (List.foldl
                            (fn ((_, hs, m, vopt), set) =>
                                List.foldl
                                   (fn (h, set) =>
                                       S.union (metavarsHyp h) set)
                                   (S.union 
                                       (metavars m) 
                                       (case vopt of
                                           SOME v => S.remove set v
                                         | NONE => set))
                                   hs)
                            (S.union (metavars concl) (metavars ext))
                            premises))));

         write "`\n\n";

         write "      G |- ";
         writeTerm write precMin concl;

         (case ext of
             Triv => ()

           | _ =>
                (
                write " ext ";
                writeTerm write precMin ext
                ));

         if null premises then
            write "\n\n"
         else
            (
            write "\n      >>\n";

            List.app
               (fn (promote, hyps, rhs, extv) =>
                   (
                   if promote then
                      write "      promote(G)"
                   else
                      write "      G";
   
                   List.app (fn hyp => (write ", "; writeHyp write hyp)) (rev hyps);
   
                   write " |- ";
                   writeTerm write precMin rhs;
   
                   (case extv of
                       NONE => ()
   
                     | SOME ext =>
                          (
                          write " ext ";
                          write (Symbol.toValue ext)
                          ));
   
                   write "\n"
                   ))
               premises;
   
            write "\n"
            )
         )


      fun writeLRule write name (premises, hyps, concl, ext) =
         (
         write "- `";
         write (Symbol.toValue name);      
         write " n";

         List.app
            (fn v =>
                (
                write " ";
                write v
                ))
            (Juliasort.sort 
                String.compare
                (List.map Symbol.toValue
                    (S.toList
                        (List.foldl
                            (fn ((_, hs, sopt, m, vopt), set) =>
                                List.foldl
                                   (fn (h, set) =>
                                       S.union (metavarsHyp h) set)
                                   (S.union 
                                       (case sopt of
                                           NONE => metavars m
                                         | SOME s => S.union (metavars m) (metavarsSub s))
                                       (case vopt of
                                           SOME v => S.remove set v
                                         | NONE => set))
                                   hs)
                            (List.foldl
                                (fn (h, set) =>
                                    S.union (metavarsHyp h) set)
                                (S.union (metavars concl) (metavars ext))
                                hyps)
                            premises))));

         write "`\n\n";

         write "      G1";
         
         List.app (fn hyp => (write ", "; writeHyp write hyp)) (rev hyps);

         write ", G2 |- ";
         writeTerm write precMin concl;

         (case ext of
             Triv => ()

           | _ =>
                (
                write " ext ";
                writeTerm write precMin ext
                ));

         if null premises then
            write "\n\n"
         else
            (
            write "\n      >>\n";

            List.app
               (fn (promote, hyps, subo, rhs, extv) =>
                   (
                   if promote then
                      write "      promote(G1)"
                   else
                      write "      G1";
   
                   List.app (fn hyp => (write ", "; writeHyp write hyp)) (rev hyps);

                   (case subo of
                       NONE => ()

                     | SOME [] =>
                          write ", G2"

                     | SOME sub =>
                          (
                          write ", ";
                          writeSub write sub;
                          write "G2"
                          ));

                   write " |- ";
                   writeTerm write precMin rhs;
   
                   (case extv of
                       NONE => ()
   
                     | SOME ext =>
                          (
                          write " ext ";
                          write (Symbol.toValue ext)
                          ));
   
                   write "\n"
                   ))
               premises;
   
            write "\n"
            )
         )


      fun gen outs rules =
         let
            fun write str = TextIO.output (outs, str)
         in
            List.app
               (fn Rule (name, rule, _) => writeRule write name rule
                 | LRule (name, rule) => writeLRule write name rule)
               rules
         end

   end
