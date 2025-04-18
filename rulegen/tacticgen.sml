
signature TACTICGEN =
   sig

      val gen : TextIO.outstream -> Rule.clause list -> unit

   end


structure Tacticgen :> TACTICGEN =
   struct

      open Rule

      structure S = RedBlackSet (structure Elem = SymbolOrdered)

      fun defined m spine set =
         (case m of
             Var _ =>
                List.foldl
                   (fn (n, set) => defined n [] set)
                   set
                   spine

           | Varfar _ =>
                List.foldl
                   (fn (n, set) => defined n [] set)
                   set
                   spine

           | Const _ =>
                List.foldl
                   (fn (n, set) => defined n [] set)
                   set
                   spine

           | Metavar (sym, s) =>
                (case (spine, s) of
                    ([], Shift 0) =>
                       S.insert set sym

                  | _ => set)

           | Lam m' => defined m' [] set

           | App (m1, m2) => defined m1 (m2 :: spine) set

           | Pair (m1, m2) => defined m2 [] (defined m1 [] set)

           | Pi1 m' => defined m' spine set

           | Pi2 m' => defined m' spine set

           | Next m' => defined m' [] set

           | Prev m' => defined m' spine set

           | Triv => set)


      fun spaces outs n =
         if n = 0 then
            ()
         else
            (
            TextIO.output (outs, " ");
            spaces outs (n-1)
            )


      exception Found of int list

      fun findbindLoop sym m spine path =
         (case m of
             Const _ =>
                findbindSpine 1 sym spine path

           | App (m1, m2) =>
                findbindLoop sym m1 (SOME m2 :: spine) path

           | Pi1 m' =>
                findbindLoop sym m' (NONE :: spine) path

           | Pi2 m' =>
                findbindLoop sym m' (NONE :: spine) path

           | Prev m' =>
                findbindLoop sym m' (NONE :: spine) path

           | Lam m' =>
                findbindLoop sym m' [] (0 :: path)

           | Pair (m1, m2) =>
                (
                findbindLoop sym m1 [] (0 :: path);
                findbindLoop sym m2 [] (1 :: path)
                )

           | Next m' =>
                findbindLoop sym m' [] (0 :: path)

           | _ => ())

      and findbindSpine i sym spine path =
         (case spine of
             [] =>
                ()

           | SOME (Metavar (sym', _)) :: (rest as (SOME (Lam _) :: _)) =>
                if Symbol.eq (sym, sym') then
                   raise (Found (i+1 :: path))
                else
                   findbindSpine (i+1) sym rest path

           | SOME m :: rest =>
                (
                findbindSpine (i+1) sym rest path;
                findbindLoop sym m [] (i :: path)
                )

           | _ :: rest =>
                findbindSpine (i+1) sym rest path)

      (* Look for sym in m; return the path to a Lam appearing immediately after it. *)

      fun findbind sym m =
         ((findbindLoop sym m [] []; NONE)
          handle Found l => SOME (List.rev l))


      fun writeHyp outs hyp concl =
         let
            fun write str = TextIO.output (outs, str)

            val symopt =
               (case hyp of
                   Tm (Metavar (sym, _)) => SOME sym
                 | Tml (Metavar (sym, _)) => SOME sym
                 | Tmh (Metavar (sym, _)) => SOME sym
                 | Tmlh (Metavar (sym, _)) => SOME sym
                 | _ => NONE)
         in
            (case symopt of
                NONE => write "NONE, "

              | SOME sym =>
                   (case findbind sym concl of
                       NONE => write "NONE, "

                     | SOME path =>
                          (
                          write "binder [";

                          List.app
                             (fn i =>
                                 (
                                 write (Int.toString i);
                                 write ", "
                                 ))
                             path;
                          
                          write "] (J.concl jud), "
                          )))
         end

      fun gen outs rules =
         let
            fun write str = TextIO.output (outs, str)

            val rules' =
               map
                  (fn rule =>
                      let
                         val (used, _) = Check.check rule

                         val defed =
                            (case rule of
                                Rule (_, (_, m, _), _) =>
                                   defined m [] S.empty

                              | LRule (_, (_, hyps, m, _)) =>
                                   defined m []
                                      (List.foldl
                                          (fn (Tm n, set) =>
                                                 defined n [] set

                                            | (Tml n, set) =>
                                                 defined n [] set

                                            | (Tmh n , set) =>
                                                 defined n [] set

                                            | (Tmlh n , set) =>
                                                 defined n [] set

                                            | (_, set) => set)
                                          S.empty
                                          hyps))
                      in
                         (rule, used, defed)
                      end)
                  rules
         in
            write "\
\(* Tactics corresponding to primitive rules.\n\
\\n\
\   - Parameters that cannot be inferred from the conclusion are taken as arguments.\n\
\     The comment indicates those arguments and their order.\n\
\\n\
\   - Unlike the primitive rules, these manage the directory properly.\n\
\\n\
\\n\
\   This file is generated by Rulegen.\n\
\*)\n\
\\n\
\signature RULE_TACTIC =\n\
\   sig\n\
\\n\
\      type tactic = Tactic.tactic\n\
\      type term = Term.term\n\
\\n\
\      type tactic1 = term -> tactic\n\
\      type tactic2 = term -> tactic1\n\
\      type tactic3 = term -> tactic2\n\
\      type tactic4 = term -> tactic3\n\
\      type tactic5 = term -> tactic4\n\
\      type tactic6 = term -> tactic5\n\
\      type tactic7 = term -> tactic6\n\
\      type tactic8 = term -> tactic7\n\
\\n\
\      val binder : int list -> Term.term -> Term.binder\n\
\\n";

            List.app
               (fn (Rule (name, _, _), used, defed) =>
                      let
                         val usedset =
                            List.foldl
                               (fn (sym, set) => S.insert set sym)
                               S.empty
                               used
    
                         val undefed = S.difference usedset defed
                         val n = S.size undefed
                         val nstr = Int.toString n
                         val namestr = Symbol.toValue name
                      in
                         write "      val ";
                         write namestr;
                         write " : tactic";
                         
                         if n = 0 then
                            write "\n"
                         else
                            (
                            write nstr;
                            spaces outs (50 - 19 - String.size namestr - String.size nstr);
                            write "(* ";
    
                            List.app
                               (fn str =>
                                   (
                                   write str;
                                   write " "
                                   ))
                               (Juliasort.sort
                                   String.compare
                                   (List.map Symbol.toValue (S.toList undefed)));
    
                            write "*)\n"
                            )
                      end

                 | (LRule (name, _), used, defed) =>
                      let
                         val usedset =
                            List.foldl
                               (fn (sym, set) => S.insert set sym)
                               S.empty
                               used
    
                         val undefed = S.difference usedset defed
                         val n = S.size undefed
                         val nstr = Int.toString n
                         val namestr = Symbol.toValue name
                      in
                         write "      val ";
                         write namestr;
                         write " : int -> tactic";
                         
                         if n = 0 then
                            write "\n"
                         else
                            (
                            write nstr;
                            spaces outs (50 - 26 - String.size namestr - String.size nstr);
                            write "(* ";
    
                            List.app
                               (fn str =>
                                   (
                                   write str;
                                   write " "
                                   ))
                               (Juliasort.sort
                                   String.compare
                                   (List.map Symbol.toValue (S.toList undefed)));
    
                            write "*)\n"
                            )
                      end)
             rules';

            write "\n\
\      val sumLeft : int -> tactic\n\
\      val insert : int -> tactic\n\
\      val forallLeft : tactic1\n\
\      val arrowLeft : tactic\n\
\      val haltsValue : tactic\n\
\      val checkPositive : tactic\n\
\      val checkNegative : tactic\n\
\      val integerIntroOf : tactic\n\
\      val integerIntroEq : tactic\n\
\      val symbolIntroOf : tactic\n\
\      val symbolIntroEq : tactic\n\
\\n\
\   end\n\
\\n\
\\n\
\structure RuleTactic :> RULE_TACTIC =\n\
\   struct\n\
\\n\
\      structure J = Judgement\n\
\      structure T = Term\n\
\      structure D = Directory\n\
\\n\
\      type rule = Rule.rule\n\
\      type term = Term.term\n\
\\n\
\      open Tactic\n\
\      open RefineTactic\n\
\\n\
\      type tactic1 = term -> tactic\n\
\      type tactic2 = term -> tactic1\n\
\      type tactic3 = term -> tactic2\n\
\      type tactic4 = term -> tactic3\n\
\      type tactic5 = term -> tactic4\n\
\      type tactic6 = term -> tactic5\n\
\      type tactic7 = term -> tactic6\n\
\      type tactic8 = term -> tactic7\n\
\\n\
\      exception Subterm\n\
\\n\
\      fun subtermSpine i elims =\n\
\         (case elims of\n\
\             [] =>\n\
\                raise Subterm\n\
\\n\
\           | T.App m :: rest =>\n\
\                if i = 0 then\n\
\                   m\n\
\                else\n\
\                   subtermSpine (i-1) rest\n\
\\n\
\           | _ :: rest =>\n\
\                if i = 0 then\n\
\                   raise Subterm\n\
\                else\n\
\                   subtermSpine (i-1) rest)\n\
\\n\
\      fun subterm l m =\n\
\         (case l of\n\
\             [] => m\n\
\\n\
\           | i :: rest =>\n\
\                (case Normalize.whnf m of\n\
\                    T.Elim (m0, spine) =>\n\
\                       (case Int.compare i 0 of\n\
\                           LESS => raise Subterm\n\
\\n\
\                         | EQUAL => subterm rest m0\n\
\\n\
\                         | GREATER => subterm rest (subtermSpine (i-1) spine))\n\
\\n\
\                  | T.Lam (_, m1) =>\n\
\                       if i = 0 then\n\
\                          subterm rest m1\n\
\                       else\n\
\                          raise Subterm\n\
\\n\
\                  | T.Pair (m1, m2) =>\n\
\                       if i = 0 then\n\
\                          subterm rest m1\n\
\                       else if i = 1 then\n\
\                          subterm rest m2\n\
\                       else\n\
\                          raise Subterm\n\
\\n\
\                  | T.Next m1 =>\n\
\                       if i = 0 then\n\
\                          subterm rest m1\n\
\                       else\n\
\                          raise Subterm\n\
\\n\
\                  | _ =>\n\
\                       raise Subterm))\n\
\\n\
\      fun binder l m =\n\
\         try\n\
\            (case Normalize.whnf (subterm l m) of\n\
\                T.Lam (b, _) => b\n\
\\n\
\              | _ => NONE)\n\
\         with\n\
\            Subterm => NONE\n\
\\n\
\      fun rebind left n right set =\n\
\         let\n\
\            val (l, _) =\n\
\               Int.natrecUp\n\
\                  (fns _ (l, set) =>\n\
\                      let\n\
\                         val (sym, set') = D.freshAndBindSet set\n\
\                      in\n\
\                         (sym :: l, set')\n\
\                      end)\n\
\                  ([], set)\n\
\                  n\n\
\         in\n\
\            D.binds (D.binds left (List.rev l)) right\n\
\         end\n\
\\n";

             List.app
                (fn (Rule (name, (premises, concl, _), _), used, defed) =>
                       let
                          val usedset =
                             List.foldl
                                (fn (sym, set) => S.insert set sym)
                                S.empty
                                used
     
                          val undefed = S.difference usedset defed

                          val usedList =
                             Juliasort.sort
                                String.compare
                                (List.map Symbol.toValue used)

                          val undefedList = 
                             Juliasort.sort
                                String.compare
                                (List.map Symbol.toValue (S.toList undefed))

                          val needToBind = List.exists (fn (_, nil, _, _) => false | _ => true) premises
                       in
                          write "      ";
                          
                          (case undefedList of
                              [] => write "val "

                            | _ => write "fun ");

                          write (Symbol.toValue name);
                             
                          List.app
                             (fn str => (write " x"; write str))
                             undefedList;

                          write " =\n";

                          write "         let\n";

                          (case (undefedList, usedList) of
                              ([], _ :: _) =>
                                 write "            do () = lift\n"

                            | _ => ());

                          if needToBind then
                             write "            do (jud, dir) = withgoal\n"
                          else
                             ();

                          write "         in\n";

                          write "            refine (Rule.";
                          write (Symbol.toValue name);

                          List.app
                             (fn sym =>
                                 if S.member defed sym then
                                    write " (T.evar ())"
                                 else
                                    (
                                    write " x";
                                    write (Symbol.toValue sym)
                                    ))
                             usedList;

                          write ")\n";

                          if needToBind then
                             (
                             write "            >>> [\n";

                             List.app
                                (fn (_, hyps, _, _) =>
                                    (case hyps of
                                        [] => write "                idtac,\n"

                                      | _ =>  
                                           (
                                           write "                chdir (D.bindsVary dir [";

                                           List.app (fn hyp => writeHyp outs hyp concl) hyps;

                                           write "]),\n"
                                           )))
                                premises;

                             write "                ]\n"
                             )
                          else
                             ();

                          write "         end\n\n"
                       end

                  | (LRule (name, (premises, lhyps, concl, _)), used, defed) =>
                       let
                          val usedset =
                             List.foldl
                                (fn (sym, set) => S.insert set sym)
                                S.empty
                                used
     
                          val undefed = S.difference usedset defed

                          val usedList =
                             Juliasort.sort
                                String.compare
                                (List.map Symbol.toValue used)

                          val undefedList = 
                             Juliasort.sort
                                String.compare
                                (List.map Symbol.toValue (S.toList undefed))
                       in
                          write "      fun ";
                          
                          write (Symbol.toValue name);
                             
                          write " i";

                          List.app
                             (fn str => (write " x"; write str))
                             undefedList;

                          write " =\n";

                          write "         let\n";

                          (case (undefedList, usedList) of
                              ([], _ :: _) =>
                                 write "            do () = lift\n"

                            | _ => ());

                          write "            do (jud, dir) = withgoal\n";
                          write "            val (right, dir') = D.split dir i\n";
                          write "            val left = D.shift dir' ";
                          write (Int.toString (List.length lhyps));
                          write "\n";
                          write "            val set = D.set dir\n";

                          write "         in\n";

                          write "            refine (Rule.";
                          write (Symbol.toValue name);
                          write " i";

                          List.app
                             (fn sym =>
                                 if S.member defed sym then
                                    write " (T.evar ())"
                                 else
                                    (
                                    write " x";
                                    write (Symbol.toValue sym)
                                    ))
                             usedList;

                          write ")\n";

                          write "            >>> [\n";

                          List.app
                             (fn (_, hyps, subopt, _, _) =>
                                 (case (hyps, subopt) of
                                     ([], NONE) =>
                                        write "                chdir left,\n"

                                   | (_, NONE) =>
                                        (
                                        write "                chdir (D.bindsVary left [";

                                        List.app (fn hyp => writeHyp outs hyp concl) hyps;

                                        write "]),\n"
                                        )
                                     
                                   | (_, SOME _) =>
                                        (
                                        write "                chdir (rebind left ";
                                        write (Int.toString (List.length hyps));
                                        write " right set),\n"
                                        )))
                             premises;

                          write "                ]\n";

                          write "         end\n\n"
                       end)
                rules';

            write "\n\
\      fun sumLeft i = refine (Rule.sumLeft i (T.evar ()) (T.evar ()) (T.evar ()))\n\
\\n\
\      fun insert i =\n\
\         let\n\
\            do (jud, dir) = withgoal\n\
\            val sym = D.fresh dir\n\
\            val (dir2, dir1) = D.split dir i\n\
\            val dir' = D.binds (D.bind dir1 sym) dir2\n\
\         in\n\
\            refine (Rule.insert i)\n\
\            >>> [\n\
\                chdir dir'\n\
\                ]\n\
\         end\n\
\\n\
\      fun forallLeft m =\n\
\         let\n\
\            do (jud, dir) = withgoal\n\
\            val dir' = D.tl dir\n\
\         in\n\
\            refine (Rule.forallLeft m)\n\
\            >>> [\n\
\                chdir dir',\n\
\                idtac\n\
\                ]\n\
\         end\n\
\\n\
\      val arrowLeft =\n\
\         let\n\
\            do (jud, dir) = withgoal\n\
\            val dir' = D.tl dir\n\
\         in\n\
\            refine Rule.arrowLeft\n\
\            >>> [\n\
\                chdir dir',\n\
\                idtac\n\
\                ]\n\
\         end\n\
\\n\
\      val haltsValue = refine Rule.haltsValue\n\
\      val checkPositive = refine Rule.checkPositive\n\
\      val checkNegative = refine Rule.checkNegative\n\
\      val integerIntroOf = refine Rule.integerIntroOf\n\
\      val integerIntroEq = refine Rule.integerIntroEq\n\
\      val symbolIntroOf = refine Rule.symbolIntroOf\n\
\      val symbolIntroEq = refine Rule.symbolIntroEq\n\
\\n\
\   end\n"
         end

   end