
signature RULEGEN =
   sig

      val gen : TextIO.outstream -> Rule.clause list -> unit

   end


structure Rulegen :> RULEGEN =
   struct

      open Rule

      structure S = SplaySet (structure Elem = SymbolOrdered)

      fun constantsTerm set m =
         (case m of
             Var _ => set

           | Varfar _ => set

           | Const k => S.insert set k

           | Lam m1 => constantsTerm set m1

           | App (m1, m2) =>
                constantsTerm (constantsTerm set m1) m2

           | Pair (m1, m2) =>
                constantsTerm (constantsTerm set m1) m2

           | Pi1 m1 =>
                constantsTerm set m1

           | Pi2 m1 =>
                constantsTerm set m1

           | Next m1 =>
                constantsTerm set m1

           | Prev m1 =>
                constantsTerm set m1

           | Triv => set

           | Metavar (_, s) => constantsSub set s)

      and constantsSub set s =
         (case s of
             Shift _ => set

           | Dot (m, s') =>
                constantsSub (constantsTerm set m) s'

           | ComposeShiftFar s' =>
                constantsSub set s'

           | Under s' =>
                constantsSub set s')

      fun constantsHyp set h =
         (case h of
             Tm a => constantsTerm set a

           | Tml a => constantsTerm set a

           | Tmh a => constantsTerm set a

           | Tp => set

           | Tpl => set

           | Tph => set)

      fun constantsHyps set hs =
         List.foldl (fn (h, set) => constantsHyp set h) set hs

      val renamed =
         List.foldl
         (fn (str, s) =>
             S.insert s (Symbol.fromValue str))
         S.empty
         ["of", "true", "false"]

      fun lower str = String.map Char.toLower str

      datatype elim = Eapp of term | Epi1 | Epi2 | Eprev

      fun writeTerm write m = writeTermLoop write m []

      and writeTermLoop write m spine =
         (case m of
             App (m1, m2) =>
                writeTermLoop write m1 (Eapp m2 :: spine)

           | Pi1 m1 =>
                writeTermLoop write m1 (Epi1 :: spine)

           | Pi2 m1 =>
                writeTermLoop write m1 (Epi2 :: spine)

           | Prev m1 =>
                writeTermLoop write m1 (Eprev :: spine)

           | _ =>
                (case spine of
                    [] =>
                       writeHead write m

                  | _ :: _ =>
                       (
                       write "Elim (";
                       writeHead write m;
                       write ", [";

                       List.app
                          (fn Eapp n =>
                                 (
                                 write "App (";
                                 writeTerm write n;
                                 write "), "
                                 )
                            | Epi1 => write "Pi1, "
                            | Epi2 => write "Pi2, "
                            | Eprev => write "Prev, ")
                          spine;

                       write "])"
                       )))

      and writeHead write m =
         (case m of
             Var i => 
                (
                write "Var ";
                write (Int.toString i)
                )

           | Varfar 0 =>
                write "Var gsize "

           | Varfar i =>
                (
                write "Var (gsize + ";
                write (Int.toString i);
                write ")"
                )

           | Const k =>
                (
                write "const_";
                write (Symbol.toValue k)
                )

           | Lam m1 =>
                (
                write "Lam (NONE, ";
                writeTerm write m1;
                write ")"
                )

           | Pair (m1, m2) =>
                (
                write "Pair (";
                writeTerm write m1;
                write ", ";
                writeTerm write m2;
                write ")"
                )
                
           | Next m1 =>
                (
                write "Next (";
                writeTerm write m1;
                write ")"
                )
                
           | Triv =>
                write "Triv"

           | Metavar (sym, Shift 0) =>
                write (lower (Symbol.toValue sym))

           | Metavar (sym, s) =>
                (
                write "Sub (";
                write (lower (Symbol.toValue sym));
                write ", ";
                writeSub write s;
                write ")"
                )

           | App _ => raise (Fail "impossible")
           | Pi1 _ => raise (Fail "impossible")
           | Pi2 _ => raise (Fail "impossible")
           | Prev _ => raise (Fail "impossible"))

      and writeSub write s =
         (case s of
             Shift i =>
                (
                write "Shift ";
                write (Int.toString i)
                )

           | Dot (Var i, s') =>
                (
                write "Idot (";
                write (Int.toString i);
                write ", ";
                writeSub write s';
                write ")"
                )

           | Dot (m, s') =>
                (
                write "Dot (";
                writeTerm write m;
                write ", ";
                writeSub write s';
                write ")"
                )

           | ComposeShiftFar (Shift 0) =>
                (
                write "Shift gsize "
                )

           | ComposeShiftFar (Shift i) =>
                (
                write "Shift (gsize + ";
                write (Int.toString i);
                write ")"
                )

           | ComposeShiftFar s' =>
                (
                write "compose (";
                writeSub write s';
                write ") (Shift gsize)"
                )

           | Under (Shift 0) =>
                write "Shift 0"

           | Under s' =>
                (
                write "under gsize (";
                writeSub write s';
                write ")"
                ))
                

      fun writeHyp write h =
         (case h of
             Tm a =>
                (
                write "J.Tm (";
                writeTerm write a;
                write ")"
                )

           | Tml a =>
                (
                write "J.Tml (";
                writeTerm write a;
                write ")"
                )

           | Tmh a =>
                (
                write "J.Tmh (";
                writeTerm write a;
                write ")"
                )

           | Tp =>
                write "J.Tp"

           | Tpl =>
                write "J.Tpl"

           | Tph =>
                write "J.Tph")

      fun gen outs rules =
         let
            fun write str = TextIO.output (outs, str)

            val rules' =
               map
               (fn rule => (rule, Check.check rule))
               rules

            val constants =
               S.difference
                  (List.foldl
                      (fn (Rule (_, (premises, concl, ext)), set) =>
                             List.foldl
                                (fn ((_, hyps, rhs, _), set) =>
                                    constantsHyps (constantsTerm set rhs) hyps)
                                (constantsTerm (constantsTerm set concl) ext)
                                premises

                        | (LRule (_, (premises, hyps, concl, ext)), set) =>
                             List.foldl
                                (fn ((_, hyps, subo, rhs, _), set) =>
                                    let
                                       val set =
                                          (case subo of
                                              NONE => set

                                            | SOME sub => constantsSub set sub)
                                    in
                                       constantsHyps (constantsTerm set rhs) hyps
                                    end)
                                (constantsHyps (constantsTerm (constantsTerm set concl) ext) hyps)
                                premises)
                      S.empty
                      rules)
                  renamed
         in
            write "(* This file is generated by Rulegen. *)\n\n\
\signature RULE_ARG =\n\
\   sig\n\
\\n\
\      type result\n\
\      type rule\n\
\\n\
\      exception ExtractFailure\n\
\\n\
\      datatype context_action =\n\
\         Nothing\n\
\       | Promote\n\
\       | Unhide\n\
\       | PromoteUnhide\n\
\\n\
\      val make :\n\
\         string                                                      (* name *)\n\
\         -> Term.term list                                           (* hidden variables *)\n\
\         -> Term.term                                                (* conclusion *)\n\
\         -> (context_action * Judgement.hyp list * Term.term) list   (* premises *)\n\
\         -> (Term.term list -> Term.term)                            (* extract *)\n\
\         -> rule\n\
\\n\
\      val lmake :\n\
\         string                             (* name *)\n\
\         -> Term.term list                  (* hidden variables *)\n\
\         -> int                             (* size of trailing context *)\n\
\         -> Judgement.hyp list              (* conclusion floating context *)\n\
\         -> Term.term                       (* conclusion rhs *)\n\
\         -> (context_action * Judgement.hyp list * Term.sub option * Term.term) list  (* premises *)\n\
\         -> (Term.term list -> Term.term)   (* extract *)\n\
\         -> rule\n\
\\n\
\   end\n\n\n\
\signature THE_RULES =\n\
\   sig\n\n\
\      type term = Term.term\n\
\      type rule\n\n";

            List.app
               (fn (Rule (name, _), (oset, _)) =>
                      (
                      write "      val ";
                      write (Symbol.toValue name);
                      write " : ";
                      List.app (fn _ => write "term -> ") oset;
                      write "rule\n"
                      )
                 | (LRule (name, _), (oset, _)) =>
                      (
                      write "      val ";
                      write (Symbol.toValue name);
                      write " : int -> ";
                      List.app (fn _ => write "term -> ") oset;
                      write "rule\n"
                      ))
               rules';

            write "\n\
\   end\n\n\n\
\functor RuleFun (structure Arg : RULE_ARG)\n\
\   :> THE_RULES where type rule = Arg.rule\n\
\=\n\
\struct\n\n\
\type rule = Arg.rule\n\
\open Term\n\
\structure J = Judgement\n\n\
\val const_of = Const Prim.ov\n\
\val const_true = Const Prim.tru\n\
\val const_false = Const Prim.fals\n";

            S.app
               (fn k =>
                   (
                   write "val const_";
                   write (Symbol.toValue k);
                   write " = Const Prim.";
                   write (Symbol.toValue k);
                   write "\n"
                   ))
               constants;

            write "\n";

            List.app
               (fn (Rule (name, (premises, concl, ext)), (oset, easet)) =>
                      (
                      (case oset of
                          [] => write "val "
                        | _ :: _ => write "fun ");
   
                      write (Symbol.toValue name);
                      write " ";
   
                      List.app 
                         (fn str =>
                             (
                             write (lower str);
                             write " "
                             ))
                         oset;
   
                      write "= Arg.make \"";
                      write (Symbol.toValue name);
                      write "\" [";

                      List.app
                         (fn str =>
                             (
                             write (lower str);
                             write ", "
                             ))
                         easet;
                                 
                      write "] (";
                      writeTerm write concl;
                      write ") [";
                      
                      List.app
                         (fn (promote, hyps, rhs, extv) =>
                             (
                             write "(";
                             write (case (promote, extv) of
                                       (false, SOME _) => "Arg.Nothing"
                                     | (false, NONE) => "Arg.Unhide"
                                     | (true, SOME _) => "Arg.Promote"
                                     | (true, NONE) => "Arg.PromoteUnhide");
                             write ", [";
                             
                             List.app
                                (fn hyp =>
                                    (
                                    writeHyp write hyp;
                                    write ", "
                                    ))
                                hyps;
   
                             write "], ";
                             writeTerm write rhs;
                             write "), "
                             ))
                         premises;
   
                      write "] (fn [";
                      
                      List.app
                         (fn (_, _, _, SOME str) =>
                                (
                                write (lower str);
                                write ", "
                                )
                           | (_, _, _, NONE) =>
                                write "_, ")
                         premises;
   
                      write "] => ";
                      writeTerm write ext;
                      write " | _ => raise Arg.ExtractFailure)\n"
                      )

                 | (LRule (name, (premises, hyps, concl, ext)), (oset, easet)) =>
                      (
                      write "fun ";
                      write (Symbol.toValue name);
                      write " gsize ";
   
                      List.app 
                         (fn str =>
                             (
                             write (lower str);
                             write " "
                             ))
                         oset;
   
                      write "= Arg.lmake \"";
                      write (Symbol.toValue name);
                      write "\" [";

                      List.app
                         (fn str =>
                             (
                             write (lower str);
                             write ", "
                             ))
                         easet;
                                 
                      write "] gsize [";

                      List.app
                         (fn hyp =>
                             (
                             writeHyp write hyp;
                             write ", "
                             ))
                         hyps;

                      write "] (";
                      writeTerm write concl;
                      write ") [";
                      
                      List.app
                         (fn (promote, hyps, subo, rhs, extv) =>
                             (
                             write "(";
                             write (case (promote, extv) of
                                       (false, SOME _) => "Arg.Nothing"
                                     | (false, NONE) => "Arg.Unhide"
                                     | (true, SOME _) => "Arg.Promote"
                                     | (true, NONE) => "Arg.PromoteUnhide");
                             write ", [";
                             
                             List.app
                                (fn hyp =>
                                    (
                                    writeHyp write hyp;
                                    write ", "
                                    ))
                                hyps;
   
                             write "], ";

                             (case subo of
                                 NONE => write "NONE"

                               | SOME sub =>
                                    (
                                    write "SOME (";
                                    writeSub write sub;
                                    write ")"
                                    ));

                             write ", ";
                             writeTerm write rhs;
                             write "), "
                             ))
                         premises;
   
                      write "] (fn [";
                      
                      List.app
                         (fn (_, _, _, _, SOME str) =>
                                (
                                write (lower str);
                                write ", "
                                )
                           | (_, _, _, _, NONE) =>
                                write "_, ")
                         premises;
   
                      write "] => ";
                      writeTerm write ext;
                      write " | _ => raise Arg.ExtractFailure)";

                      if List.null easet then
                         ()
                      else
                         write " jud)";
                      write "\n"
                      ))
               rules';

            write "\nend\n"

         end

   end
