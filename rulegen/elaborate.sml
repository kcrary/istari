
signature ELABORATE =
   sig

      exception Incorrect of string

      val elaborate : Syntax.clause -> Rule.clause

   end


structure Elaborate :> ELABORATE =
   struct

      exception Incorrect of string

      structure S = Syntax
      open Rule

      structure Dict =
         ListDict (structure Key = SymbolOrdered)

      structure Set =
         ListSet (structure Elem = SymbolOrdered)


      (* Explicit variables are near or far.  Far means they are on the far side
         of the second context in an lrule.  Otherwise they are near, which means
         they are on the near side of a second context, or from where they stand
         there is no second context (ie, in an ordinary rule, or when already
         standing on the far side).

         An elaboration scope is not permitted to contain both near and far variables.
         (This simplifies things.)  The scope is marked far if it consists of far
         variables.

         A metavariable cannot depend on both near and far variables.  (Again, this
         simplifies things.)  In an lrule, all a metavariable's explicit dependencies
         are on the variables before the second context.

         A metavariable is marked as to whether it can depend on the second context
         (if any).  It can only depend on it if all its appearances can.
      *)

      fun traverseMetavar d far scope X =
         let
            val set = List.foldl (fn (y, set) => Set.insert set y) Set.empty scope
         in
            Dict.insertMerge d X
               (far, set)
               (fn (far', set') => 
                   (far andalso far', Set.intersection set set'))
         end

      fun bind x scope =
         if List.exists (fn y => Symbol.eq (x, y)) scope then
            raise (Incorrect ("rebind " ^ Symbol.toValue x))
         else
            x :: scope

      fun traverseTerm d far scope m =
         (case m of
             S.Var _ => d
           | S.Const _ => d

           | S.Lam (x, m1) => 
                if far then
                   (* Adding x would put both near and far variables into scope simultaneously. *)
                   raise (Incorrect "near and far")
                else
                   traverseTerm d far (bind x scope) m1

           | S.App (m1, m2) => traverseTerm (traverseTerm d far scope m1) far scope m2
           | S.Pair (m1, m2) => traverseTerm (traverseTerm d far scope m1) far scope m2
           | S.Pi1 m1 => traverseTerm d far scope m1
           | S.Pi2 m1 => traverseTerm d far scope m1
           | S.Next m1 => traverseTerm d far scope m1
           | S.Prev m1 => traverseTerm d far scope m1
           | S.Triv => d

           | S.Metavar (X, sub) =>
                let
                   val (d', scope') =
                      List.foldl
                         (fn ((m, y), (d', scope')) =>
                             (traverseTerm d' false scope m,
                              bind y scope'))
                         (d, scope)
                         sub
                in
                   traverseMetavar d' far scope' X
                end)

      fun traverseClass d scope h =
         (case h of
             S.Tm a => traverseTerm d false scope a

           | S.Tml a => traverseTerm d false scope a

           | S.Tmh a => traverseTerm d false scope a

           | S.Tp => d

           | S.Tpl => d

           | S.Tph => d)

      fun traverseHyps d scope hyps =
         (case hyps of
             [] =>
                (d, scope)

           | (x, class) :: rest =>
                let
                   val (d', scope') = traverseHyps d scope rest
                in
                   (traverseClass d' scope' class,
                    x :: scope')
                end)

      fun traverseRule (premises, concl, ext) =
         List.foldl
            (fn ((_, hyps, rhs, extv), d) =>
                let
                   val (d, scope) = traverseHyps d [] hyps
                   val d = traverseTerm d false scope rhs
                in
                   (case extv of
                       NONE => d

                     | SOME X =>
                          traverseMetavar d false scope X)
                end)
            (traverseTerm (traverseTerm Dict.empty false [] concl) false [] ext)
            premises

      fun traverseLRule (premises, hyps, concl, ext) =
         let
            val (d, scope) = traverseHyps Dict.empty [] hyps
            val d = traverseTerm d true scope concl
            val d = traverseTerm d true scope ext
         in
            List.foldl
               (fn ((_, hyps, subo, rhs, extv), d) =>
                   let
                      val (d, scope) = traverseHyps d [] hyps
                   
                      val (far, d) =
                         (case subo of
                             NONE => (false, d)

                           | SOME sub =>
                                (true,
                                 List.foldl
                                    (fn ((m, _), d) => traverseTerm d false scope m)
                                    d
                                    sub))

                      val d = traverseTerm d far scope rhs
                   in
                      (case extv of
                          NONE => d

                        | SOME X =>
                             traverseMetavar d far scope X)
                   end)
               d
               premises
         end


      fun lookup l x i =
         (case l of
             [] => raise (Incorrect "unbound")

           | y :: rest =>
                if Symbol.eq (x, y) then
                   i
                else
                   lookup rest x (i+1))


      fun dot m s =
         (case (m, s) of
             (Var i, Shift j) =>
                if i+1 = j then
                   Shift i
                else
                   Dot (m, s)

           | _ => Dot (m, s))

      fun under s =
         (case s of
             Shift 0 => s
           | _ => Under s)


      fun coerce deps scope =
         (case deps of
             [] =>
                Shift (List.length scope)

           | x :: rest =>
                dot (Var (lookup scope x 0)) (coerce rest scope))


      (* precondition: no ComposeShiftFar or Under *)
      fun lookupSub i s =
         (case s of
             Shift j => Var (i + j)

           | Dot (m, s') =>
                if i = 0 then
                   m
                else
                   lookupSub (i-1) s'

           | ComposeShiftFar _ => raise (Fail "precondition")

           | Under _ => raise (Fail "precondition"))



      (* precondition: every dot in s1 is a variable, no ComposeShiftFar or Under *)
      fun compose s1 s2 =
         (case (s1, s2) of
             (Shift 0, _) => s2

           | (_, Shift 0) => s1

           | (Shift i, Dot (_, s)) =>
                compose (Shift (i-1)) s

           | (Shift i, Shift j) =>
                Shift (i+j)

           | (Dot (Var i, s), _) =>
                dot (lookupSub i s2) (compose s s2)

           | _ => raise (Fail "precondition"))


      fun elabTerm d far scope m =
         (case m of
             S.Var x =>
                if far then
                   Varfar (lookup scope x 0)
                else
                   Var (lookup scope x 0)

           | S.Const k =>
                Const k

           | S.Metavar (X, sub) =>
                let
                   val (far', predeps) = Dict.lookup d X

                   val deps =
                      Juliasort.sort
                         (fn (x, y) => String.compare (Symbol.toValue y, Symbol.toValue x))
                         (Set.toList predeps)

                   (* Note that a far metavariable depends on far variables,
                      so any substitutends must live in the far context, which
                      makes the dependencies *near* to them.

                      Thus, subsitutends are always near, regardless of whether
                      the metavariable is far or not.
                   *)

                   val (s, scope') = elabSub d scope sub
                   val s' = compose (coerce deps scope') s
                in
                   Metavar (X, 
                            (case (far', far) of
                                (true, true) => under s'

                              | (false, true) => ComposeShiftFar s'

                              | (false, false) => s'

                              | (true, false) => 
                                   (* A metavariable is only marked far if every appearance
                                      has a second context, so this can't happen.
                                   *)
                                   raise (Fail "impossible")))
                end

           | S.Lam (x, m) =>
                if far then
                   raise (Incorrect "near bind in far")
                else
                   Lam (elabTerm d far (x :: scope) m)

           | S.App (m1, m2) =>
                App (elabTerm d far scope m1, elabTerm d far scope m2)

           | S.Pair (m1, m2) =>
                Pair (elabTerm d far scope m1, elabTerm d far scope m2)

           | S.Pi1 m1 =>
                Pi1 (elabTerm d far scope m1)

           | S.Pi2 m1 =>
                Pi2 (elabTerm d far scope m1)

           | S.Next m1 =>
                Next (elabTerm d far scope m1)

           | S.Prev m1 =>
                Prev (elabTerm d far scope m1)

           | S.Triv =>
                Triv)

      and elabSub d scope sub =
         List.foldl
            (fn ((m, y), (s, scope')) =>
                (dot (elabTerm d false scope m) s,
                 y :: scope'))
            (Shift 0, scope)
            sub
         

      fun elabHyp d scope h =
         (case h of
             S.Tm a => Tm (elabTerm d false scope a)

           | S.Tml a => Tml (elabTerm d false scope a)

           | S.Tmh a => Tmh (elabTerm d false scope a)

           | S.Tp => Tp

           | S.Tpl => Tpl

           | S.Tph => Tph)



      fun elabHyps d hyps =
         (case hyps of
             [] =>
                ([], [])
                
           | (x, class) :: rest =>
                let
                   val (rest', scope) = elabHyps d rest
                in
                   (elabHyp d scope class :: rest',
                    x :: scope)
                end)


      fun elabRule (rule as (premises, concl, ext)) =
         let
            val d = traverseRule rule
         in
            (map
                (fn (promote, hyps, a, extv) =>
                    let
                       val (hyps', scope) = elabHyps d hyps
                    in
                       (case extv of
                           NONE => ()

                         | SOME X =>
                              let
                                 val (_, predeps) = Dict.lookup d X

                                 val deps =
                                    Juliasort.sort
                                       (fn (x, y) => String.compare (Symbol.toValue y, Symbol.toValue x))
                                       (Set.toList predeps)
                              in
                                 (case coerce deps scope of
                                     Shift 0 => ()

                                   | _ => raise (Incorrect "inexhaustive extract"))
                              end);

                       (promote, hyps', elabTerm d false scope a, extv)
                    end)
                premises,
             elabTerm d false [] concl,
             elabTerm d false [] ext)
         end


      fun elabLRule (rule as (premises, hyps, concl, ext)) =
         let
            val d = traverseLRule rule

            val (hyps', conclscope) = elabHyps d hyps
         in
            (map
                (fn (promote, hyps, subo, a, extv) =>
                    let
                       val (hyps', scope) = elabHyps d hyps

                       val (far, subo') =
                          (case subo of
                              NONE => (false, NONE)

                            | SOME sub =>
                                 let
                                    val (s, scope') = elabSub d scope sub
                                    val s' = compose (coerce conclscope scope') s
                                 in
                                    (true, SOME s')
                                 end)
                    in
                       (case extv of
                           NONE => ()

                         | SOME X =>
                              let
                                 val (_, predeps) = Dict.lookup d X

                                 val deps =
                                    Juliasort.sort
                                       (fn (x, y) => String.compare (Symbol.toValue y, Symbol.toValue x))
                                       (Set.toList predeps)
                              in
                                 (case coerce deps scope of
                                     Shift 0 => ()

                                   | _ => raise (Incorrect "inexhaustive extract"))
                              end);

                       (promote, hyps', subo', elabTerm d far scope a, extv)
                    end)
                premises,
             hyps',
             elabTerm d true conclscope concl,
             elabTerm d true conclscope ext)
         end


      fun elaborate clause =
         (case clause of
             S.Rule (name, rule, axiom) => 
                (Rule (name, elabRule rule, axiom)
                 handle (Incorrect msg) =>
                    (
                    print "Incorrect rule ";
                    print name;
                    print ": ";
                    print msg;
                    print "\n";
                    raise (Incorrect msg)
                    ))

           | S.LRule (name, rule) => 
                (LRule (name, elabLRule rule))
                 handle (Incorrect msg) =>
                    (
                    print "Incorrect rule ";
                    print name;
                    print ": ";
                    print msg;
                    print "\n";
                    raise (Incorrect msg)
                    ))

   end
