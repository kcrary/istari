
signature WEBGENDB =
   sig

      val gen : TextIO.outstream -> Rule.clause list -> unit

   end


structure WebgenDB :> WEBGENDB =
   struct

      open Rule

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
      val precApp = 90
      val precMax = 100

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
             Var i =>
                write (Int.toString i)

           | Varfar i =>
                (
                write (Int.toString i);
                write "+n"
                )

           | Const sym =>
                write (Symbol.toValue sym)

           | Metavar (sym, sub) =>
                (
                write (Symbol.toValue sym);
                writeSub write sub
                )
                
           | Lam m1 =>
                (
                lparen write prec precLam;
                write "fn . ";
                writeTerm write precLam m1;
                rparen write prec precLam
                )

           | App (m1, m2) =>
                (
                lparen write prec precApp;
                writeTerm write precApp m1;
                write " ";
                writeTerm write (precApp+1) m2;
                rparen write prec precApp
                )

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

      and writeSub write sub =
         (case sub of
             Shift 0 => ()

           | _ =>
                (
                write "[";
                writeSubMain write sub;
                write "]"
                ))

      and writeSubMain write sub =
         (case sub of
             Shift 0 =>
                write "id"

           | Shift i =>
                (
                write "^";
                write (Int.toString i)
                )

           | Dot (m, s) =>
                (
                writeTerm write precMin m;
                write " . ";
                writeSubMain write s
                )

           | ComposeShiftFar s =>
                (
                write "(";
                writeSubMain write s;
                write ") o ^n"
                )

           | Under s =>
                (
                write "under_n (";
                writeSubMain write s;
                write ")"
                ))


      fun writeHyp write h =
         (case h of
             Tm a =>
                (
                writeTerm write precMax a
                )

           | Tml a => 
                (
                write "(later) ";
                writeTerm write precMax a
                )

           | Tmh a => 
                (
                write "(hidden) ";
                writeTerm write precMax a
                )

           | Tp =>
                write "type"

           | Tpl =>
                write "(later) type"

           | Tph =>
                write "(hidden) type")


      fun writeRule write name (premises, concl, ext) oset =
         (
         write "- `";
         write (Symbol.toValue name);

         List.app
            (fn v =>
                (
                write " ";
                write v
                ))
            oset;

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

      fun writeLRule write name (premises, hyps, concl, ext) oset =
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
            oset;

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

                     | SOME (Shift 0) =>
                          write ", G2"

                     | SOME sub =>
                          (
                          write ", G2";
                          writeSub write sub
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
               (fn rule =>
                   let
                      val (oset, _) = Check.check rule
                   in
                      (case rule of
                          Rule (name, rule, _) => writeRule write name rule oset
                        | LRule (name, rule) => writeLRule write name rule oset)
                   end)
               rules
         end

   end
