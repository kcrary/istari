
signature LEMMAGEN =
   sig

      val gen : TextIO.outstream -> Rule.clause list -> unit

   end


structure Lemmagen :> LEMMAGEN =
   struct

      open Rule

      structure D = SplayDict (structure Key = SymbolOrdered)

      val renamed =
         List.foldl
         (fn ((from, to), d) =>
             D.insert d (Symbol.fromValue from) to)
         D.empty
         [("forall", "pi"), ("exists", "sigma"), ("fix", "theta"), ("let", "lett")]

      fun writeTerm write m =
         (case m of
             Var i => 
                (
                write "(var ";
                write (Int.toString i);
                write ")"
                )

           | Varfar 0 =>
                write "(var (length G2))"

           | Varfar i =>
                (
                write "(var (";
                write (Int.toString i);
                write " + length G2))"
                )

           | Const k =>
                (case D.find renamed k of
                    SOME str =>
                       write str

                  | NONE =>
                       write (Symbol.toValue k))

           | Lam m1 =>
                (
                write "(lam ";
                writeTerm write m1;
                write ")"
                )

           | App (m1, m2) =>
                (
                write "(app ";
                writeTerm write m1;
                write " ";
                writeTerm write m2;
                write ")"
                )

           | Pair (m1, m2) =>
                (
                write "(ppair ";
                writeTerm write m1;
                write " ";
                writeTerm write m2;
                write ")"
                )
                
           | Pi1 m1 =>
                (
                write "(ppi1 ";
                writeTerm write m1;
                write ")"
                )
                
           | Pi2 m1 =>
                (
                write "(ppi2 ";
                writeTerm write m1;
                write ")"
                )
                
           | Next m1 =>
                (
                write "(next ";
                writeTerm write m1;
                write ")"
                )
                
           | Prev m1 =>
                (
                write "(prev ";
                writeTerm write m1;
                write ")"
                )

           | Triv =>
                write "triv"

           | Metavar (sym, Shift 0) =>
                write (Symbol.toValue sym)

           | Metavar (sym, s) =>
                (
                write "(subst ";
                writeSub write s;
                write " ";
                write (Symbol.toValue sym);
                write ")"
                ))

      and writeSub write s =
         (case s of
             Shift i =>
                (
                write "(sh ";
                write (Int.toString i);
                write ")"
                )

           | Dot (m, s') =>
                (
                write "(dot ";
                writeTerm write m;
                write " ";
                writeSub write s';
                write ")"
                )

           | ComposeShiftFar (Shift i) =>
                (
                write "(sh (";
                write (Int.toString i);
                write " + length G2))"
                )

           | ComposeShiftFar s' =>
                (
                write "(compose ";
                writeSub write s';
                write " (sh (length G2)))"
                )

           | Under s' =>
                (
                write "(under (length G2) ";
                writeSub write s';
                write ")"
                ))
                

      fun writeHyp write h =
         (case h of
             Tm a =>
                (
                write "(hyp_tm ";
                writeTerm write a;
                write ")"
                )

           | Tml a =>
                (
                write "(hyp_tml ";
                writeTerm write a;
                write ")"
                )

           | Tmh a =>
                (
                write "(hyp_tm ";
                writeTerm write a;
                write ")"
                )

           | Tp => write "hyp_tp"
           | Tpl => write "hyp_tpl"
           | Tph => write "hyp_tp")


      fun writeHyps write first hyps =
         (case hyps of
             [] =>
                write first

           | hyp :: rest =>
                (
                write "(cons ";
                writeHyp write hyp;
                write " ";
                writeHyps write first rest;
                write ")"
                ))
                   

      fun isHidden h =
         (case h of
             Tmh _ => true
           | Tph => true
           | _ => false)


      fun gen outs rules =
         let
            fun write str = TextIO.output (outs, str)

            val rules' =
               map
               (fn rule => (rule, Check.check rule))
               rules
         in
            write "(* This file is generated by Rulegen. *)\n\nRequire Import Defs.\n\n";

            app
               (fn (Rule (name, (premises, concl, ext)), (oset, _)) =>
                      let
                         val (premises', eset, _) =
                            List.foldr
                               (fn ((promote, hyps, rhs, extv), (l, eset, i)) =>
                                   (case extv of
                                       NONE =>
                                          let
                                             val ext = "ext" ^ Int.toString i
                                          in
                                             ((promote, hyps, rhs, ext) :: l,
                                              ext :: eset,
                                              i+1)
                                          end
   
                                     | SOME ext =>
                                          ((promote, hyps, rhs, ext) :: l,
                                           ext :: eset,
                                           i)))
                               ([], [], 0)
                               premises
   
                         val set = oset @ eset
                      in
                         write "Definition ";
                         write (Symbol.toValue name);
                         write "_obligation : Type := forall G";
                         
                         List.app (fn var => (write " "; write var)) set;
                         write ", ";
   
                         List.app
                            (fn (_, hyps, _, ext) =>
                                (
                                List.foldl
                                   (fn (h, i) =>
                                       (
                                       if isHidden h then
                                          (
                                          write "hygiene (fun i => i <> ";
                                          write (Int.toString i);
                                          write ") ";
                                          write ext;
                                          write " -> "
                                          )
                                       else
                                          ();

                                       i+1
                                       ))
                                   0
                                   hyps;
                                ()
                                ))
                            premises';
       
                         List.app
                            (fn (promote, hyps, rhs, ext) =>
                                (
                                write "tr ";
                                writeHyps write (if promote then "(promote G)" else "G") hyps;
                                write " (dof ";
                                write ext;
                                write " ";
                                writeTerm write rhs;
                                write ") -> "
                                ))
                            premises';
                         
                         write "tr G (dof ";
                         writeTerm write ext;
                         write " ";
                         writeTerm write concl;
                         write ").\n"
                      end

                 | (LRule (name, (premises, hyps, concl, ext)), (oset, _)) =>
                      let
                         val (premises', eset, _) =
                            List.foldr
                               (fn ((promote, hyps, subo, rhs, extv), (l, eset, i)) =>
                                   (case extv of
                                       NONE =>
                                          let
                                             val ext = "ext" ^ Int.toString i
                                          in
                                             ((promote, hyps, subo, rhs, ext) :: l,
                                              ext :: eset,
                                              i+1)
                                          end
   
                                     | SOME ext =>
                                          ((promote, hyps, subo, rhs, ext) :: l,
                                           ext :: eset,
                                           i)))
                               ([], [], 0)
                               premises
   
                         val set = oset @ eset
                      in
                         write "Definition ";
                         write (Symbol.toValue name);
                         write "_obligation : Type := forall G1 G2";
                         
                         List.app (fn var => (write " "; write var)) set;
                         write ", ";
   
                         List.app
                            (fn (_, hyps, subo, _, ext) =>
                                (
                                List.foldl
                                   (fn (h, i) =>
                                       (
                                       if isHidden h then
                                          (
                                          write "hygiene (fun i => i <> ";
                                          write (Int.toString i);
                                          (case subo of
                                              NONE => ()
                                            | SOME _ =>
                                                 write " + length G2");
                                          write ") ";
                                          write ext;
                                          write " -> "
                                          )
                                       else
                                          ();

                                       i+1
                                       ))
                                   0
                                   hyps;
                                ()
                                ))
                            premises';
       
                         List.app
                            (fn (promote, hyps, subo, rhs, ext) =>
                                (
                                write "tr (";

                                (case subo of
                                    NONE => ()

                                  | SOME sub =>
                                       (
                                       write "List.app (substctx ";
                                       writeSub write sub;
                                       write " G2) "
                                       ));
                                
                                writeHyps write (if promote then "(promote G1)" else "G1") hyps;
                                write ") (dof ";
                                write ext;
                                write " ";
                                writeTerm write rhs;
                                write ") -> "
                                ))
                            premises';
                         
                         write "tr (List.app G2 ";
                         writeHyps write "G1" hyps;
                         write ") (dof ";
                         writeTerm write ext;
                         write " ";
                         writeTerm write concl;
                         write ").\n"
                      end)
               rules';

            write "\n\nDefinition all_obligations : list Type := ";

            List.app
               (fn clause =>
                   let 
                      val name =
                         (case clause of
                             Rule (name, _) => name
                           | LRule (name, _) => name)
                   in
                      write (Symbol.toValue name);
                      write "_obligation :: "
                   end)
               rules;
            write "nil.\n"

         end

   end
