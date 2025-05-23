
(* We could easily have done this during elaboration, but then we would have
   to trust the elaborator.
*)

signature CHECK =
   sig

      type symbol = Symbol.symbol

      exception MetavariableCollision

      (* Returns the rule's ordinary metavariables, and the subset of
         ordinary variables that appear in extracts.
         Also checks that they are disjoint from the extract metavariables.
      *)
      val check : Rule.clause -> string list * string list

   end


structure Check :> CHECK =
   struct

      type symbol = Symbol.symbol

      open Rule

      exception MetavariableCollision

      structure S = ListSet (structure Elem = SymbolOrdered)

      fun checkTerm set m =
         (case m of
             Var _ => set

           | Varfar _ => set

           | Const _ => set

           | Lam m1 => checkTerm set m1

           | App (m1, m2) =>
                checkTerm (checkTerm set m1) m2

           | Pair (m1, m2) =>
                checkTerm (checkTerm set m1) m2

           | Pi1 m1 =>
                checkTerm set m1

           | Pi2 m1 =>
                checkTerm set m1

           | Next m1 =>
                checkTerm set m1

           | Prev m1 =>
                checkTerm set m1

           | Triv => set

           | Metavar (sym, s) =>
                checkSub (S.insert set sym) s)

      and checkSub set s =
         (case s of
             Shift _ => set

           | Dot (m, s') =>
                checkSub (checkTerm set m) s'

           | ComposeShiftFar s' =>
                checkSub set s'

           | Under s' =>
                checkSub set s')

      fun checkHyp set h =
         (case h of
             Tm a => checkTerm set a

           | Tml a => checkTerm set a

           | Tmh a => checkTerm set a

           | Tmlh a => checkTerm set a

           | Tp => set

           | Tpl => set

           | Tph => set)

      val sort = Juliasort.sort String.compare


      (* Checks that any occurrences of metavars in set are not under a binder
         or a nontrivial substitution.  The set is intended to be the set of
         metavariable used in the extract that are not bound by an extract.
         There's nothing inherently wrong with such a metavariable being modified,
         but we would need to make the checker for hidden variable occurrences
         more sophisticated if any such metavariables were modified.
      *)
      exception ModifiedExtractMetavariable

      fun unmodifiedTerm set under m =
         (case m of
             Var _ => ()

           | Varfar _ => ()

           | Const _ => ()

           | Lam m' => 
                unmodifiedTerm set true m'

           | App (m1, m2) =>
                (
                unmodifiedTerm set under m1;
                unmodifiedTerm set under m2
                )

           | Pair (m1, m2) =>
                (
                unmodifiedTerm set under m1;
                unmodifiedTerm set under m2
                )

           | Pi1 m' =>
                unmodifiedTerm set under m'

           | Pi2 m' =>
                unmodifiedTerm set under m'

           | Next m' =>
                unmodifiedTerm set under m'

           | Prev m' =>
                unmodifiedTerm set under m'

           | Triv => ()

           | Metavar (sym, s) =>
                if S.member set sym then
                   if under then
                      raise ModifiedExtractMetavariable
                   else
                      (case s of
                          Shift 0 => ()

                        | _ => raise ModifiedExtractMetavariable)
                else
                   unmodifiedSub set under s)

      and unmodifiedSub set under s =
         (case s of
             Shift _ => ()

           | Dot (m, s') =>
                (
                unmodifiedTerm set under m;
                unmodifiedSub set under s'
                )

           | ComposeShiftFar s' =>
                unmodifiedSub set true s'

           | Under s' =>
                unmodifiedSub set true s')


      fun check rule =
         (case rule of
             Rule (_, (premises, concl, ext), _) =>
                let
                   (* Set of variables occuring outside extracts *)
                   val oset =
                      List.foldl
                         (fn ((_, hyps, rhs, _), set) =>
                             List.foldl
                                (fn (hyp, set) => checkHyp set hyp)
                                (checkTerm set rhs)
                                hyps)
                         (checkTerm S.empty concl)
                         premises
       
                   (* Set of variables bound by extracts *)
                   val bset =
                      List.foldl
                         (fn ((_, _, _, SOME extv), bset) =>
                             if S.member bset extv orelse S.member oset extv then
                                (* an extract metavariable is bound multiple times, or is used outside the extracts *)
                                raise MetavariableCollision
                             else
                                S.insert bset extv
       
                           | ((_, _, _, NONE), bset) => bset)
                         S.empty
                         premises
       
                   (* Set of variables used in the extract *)
                   val eset = checkTerm S.empty ext
       
                   val eargset = S.difference eset bset
                   val argset = S.union oset eargset

                   val () = unmodifiedTerm eargset false ext
                in
                   (sort (List.map Symbol.toValue (S.toList argset)),
                    sort (List.map Symbol.toValue (S.toList eargset)))
                end

           | LRule (_, (premises, hyps, concl, ext)) =>
                let
                   (* Set of variables occuring outside extracts *)
                   val oset =
                      List.foldl
                         (fn ((_, hyps, subo, rhs, _), set) =>
                             let
                                val set =
                                   (case subo of
                                       NONE => set
                                     | SOME s => checkSub set s)
                             in
                                List.foldl
                                   (fn (hyp, set) => checkHyp set hyp)
                                   (checkTerm set rhs)
                                   hyps
                             end)
                         (List.foldl
                             (fn (hyp, set) => checkHyp set hyp)
                             (checkTerm S.empty concl)
                             hyps)
                         premises
       
                   (* Set of variables bound by extracts *)
                   val bset =
                      List.foldl
                         (fn ((_, _, _, _, SOME extv), bset) =>
                             if S.member bset extv orelse S.member oset extv then
                                (* an extract metavariable is bound multiple times, or is used outside the extracts *)
                                raise MetavariableCollision
                             else
                                S.insert bset extv
       
                           | ((_, _, _, _, NONE), bset) => bset)
                         S.empty
                         premises
       
                   (* Set of variables used in the extract *)
                   val eset = checkTerm S.empty ext
       
                   val eargset = S.difference eset bset
                   val argset = S.union oset eargset

                   val () = unmodifiedTerm eargset false ext
                in
                   (sort (List.map Symbol.toValue (S.toList argset)),
                    sort (List.map Symbol.toValue (S.toList eargset)))
                end)

   end