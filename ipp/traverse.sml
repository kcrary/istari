
signature TRAVERSE =
   sig

      val traverse : Context.context -> Syntax.program -> Syntax.program * Context.context * Context.context

   end


structure Traverse :> TRAVERSE =
   struct

      open Syntax

      structure E = Error
      structure C = Context
      datatype result = datatype C.result

      (* topological sort of type declarations *)

      structure Dict = SymbolDict
      structure Set = SymbolSet

      datatype color = WHITE | GRAY | BLACK

      fun identifiers (t, _) =
         (case t of
             Tident (longid, _) =>
                (case longid of
                    [] => raise (Fail "invariant")

                  | [id] => Set.singleton id

                  | (_ :: _ :: _) => Set.empty)

           | Ttyvar _ => Set.empty

           | Tapp (ts, (longid, _)) =>
                (case longid of
                    [] => raise (Fail "invariant")

                  | [id] => Set.insert (identifiersFromList ts) id

                  | (_ :: _ :: _) => identifiersFromList ts)

           | Tprod ts =>
                identifiersFromList ts

           | Tarrow (t1, t2) =>
                Set.union (identifiers t1) (identifiers t2))

      and identifiersFromList l =
         List.foldl (fn (t, s) => Set.union (identifiers t) s) Set.empty l


      (* Puts type declarations into standard form: datatypes first, then withtypes in dependency order. *)
      fun standardizeTypeDec binds span =
         let
            fun loop1 binds dts wd =
               (case binds of
                   nil => 
                      (rev dts, wd)

                 | (b as Data _) :: rest =>
                      loop1 rest (b :: dts) wd

                 | (b as With (_, (id, _), t, _)) :: rest =>
                      let
                         (* We can ignore the bound variables because they are syntactically distinguished
                            from the variables we're interested in.
                         *)
                         val edges = Set.toList (identifiers t)

                         val (wd', dup) =
                            Dict.insert' wd id (ref WHITE, edges, b)
                      in
                         if dup then
                            raise (E.SemanticError ("duplicate identifier " ^ Symbol.toValue id ^ " in type declaration", span))
                         else
                            loop1 rest dts wd'
                      end)

            val (dts, wd) = loop1 binds nil Dict.empty

            (* depth-first search *)
            fun search (id, acc) =
               (case Dict.find wd id of
                   NONE => acc

                 | SOME (color, edges, bind) =>
                      (case !color of
                          BLACK => acc

                        | GRAY => 
                            raise (E.SemanticError ("cycle in type declaration", span))

                        | WHITE =>
                             let
                                val () = color := GRAY
                                val acc' = List.foldl search acc edges
                                val () = color := BLACK
                             in
                                bind :: acc'
                             end))

            val withs =
               Dict.foldl (fn (id, _, acc) => search (id, acc)) nil wd
         in
            dts @ rev withs
         end
         

      fun idToString (id, _) = Symbol.toValue id

      fun longidToString (longid, _) =
         let
            fun loop acc longid =
               (case longid of
                   nil => raise (Fail "precondition")

                 | [id] =>
                      String.concat (rev (Symbol.toValue id :: acc))

                 | id :: rest =>
                      loop ("." :: Symbol.toValue id :: acc) rest)
         in
            loop [] longid
         end


      fun bindTyvars ctx tyvars =
         List.foldl (fn (id, c) => C.bindTyvar c id) ctx tyvars


      fun traverseTyGen aftv ctx (ty as (ty_, span)) =
         (case ty_ of
             Tident longid =>
                (case C.lookupType ctx longid of
                    Absent longid' =>
                       raise (E.SemanticError ("unbound identifier " ^ longidToString longid', span))

                  | Present longid' => (Tident longid', span))

           | Ttyvar id =>
                (case C.lookupTyvar ctx id of
                    SOME id' => (Ttyvar id', span)
                  | NONE =>
                       (* free type variable, pass it along unchanged if allowed here *)
                       if aftv then
                          ty
                       else
                          raise (E.SemanticError ("unbound type variable " ^ idToString id, span)))

           | Tapp (ts, longid) =>
                (case C.lookupType ctx longid of
                    Absent longid' =>
                       raise (E.SemanticError ("unbound identifier " ^ longidToString longid', span))
                  | Present longid' => 
                       (Tapp (map (traverseTyGen aftv ctx) ts, longid'), span))

           | Tprod ts =>
                (Tprod (map (traverseTyGen aftv ctx) ts), span)

           | Tarrow (t1, t2) =>
                (Tarrow (traverseTyGen aftv ctx t1, traverseTyGen aftv ctx t2), span))


      val traverseTy = traverseTyGen false


      fun traverseTybinds ctx binds span =
         let
            val ctx' =
               foldl
               (fn (Data (_, id, _, _), c) => C.bindType c id
                 | (With (_, id, _, _), c) => C.bindType c id)
               ctx
               binds

            val binds' =
               map
               (fn Data (args, id, dcons, span) =>
                      let
                         val ctx'' = bindTyvars ctx' args
                      in
                         Data (args, id,
                               map (fn Dcon (id, tyo, span) =>
                                          Dcon (id, Option.map (traverseTy ctx'') tyo, span)
   
                                     | Record (id, fields, span) => 
                                          Record (id,
                                                  map (fn (lab, t) => (lab, traverseTy ctx'' t)) fields,
                                                  span)) dcons,
                               span)
                      end

                 | With (args, id, t, span) =>
                      With (args, id, traverseTy (bindTyvars ctx' args) t, span))
               binds

            val binds'' = standardizeTypeDec binds' span

            val bctx =
               foldl
               (fn (Data (_, id, dcons, _), c) =>
                      foldl
                      (fn (Dcon (id, tyo, _), c) =>
                             (case tyo of
                                 NONE => C.bindConstr c id 0

                               | SOME (Tprod l, _) => C.bindConstr c id (length l)

                               | SOME _ => C.bindConstr c id 1)

                        | (Record (id, _, _), c) => C.bindConstr c id 1)
                      (C.bindType c id)
                      dcons

                 | (With (_, id, _, _), c) => C.bindType c id)
               C.empty
               binds''
         in
            (binds'', bctx)
         end


      fun traverseSpec ctx (spec_, span) =
         (case spec_ of
             Sval (id, ty) =>
                ((Sval (id, traverseTyGen true ctx ty), span),
                 C.bindExp C.empty id)

           | Sabstype (args, id) =>
                ((spec_, span),
                 C.bindType C.empty id)

           | Stype (args, id, t) =>
                ((Stype (args, id, traverseTy (bindTyvars ctx args) t), span),
                 C.bindType C.empty id)

           | Sdatatype binds =>
                let
                   val (binds', bctx) = traverseTybinds ctx binds span
                in
                   ((Sdatatype binds', span), bctx)
                end

           | Smod (id, s) =>
                let
                   val (s', sctx) = traverseSig ctx s
                in
                   ((Smod (id, s'), span),
                    C.bindMod C.empty id sctx)
                end

           | Sextension (id, tyo) =>
                let
                   val arity =
                      (case tyo of
                          NONE => 0
                        | SOME _ => 1)
                in
                   ((Sextension (id, Option.map (traverseTy ctx) tyo), span),
                    C.bindConstr C.empty id arity)
                end

           | Sinclude id =>
                (case C.lookupSig ctx id of
                    SOME (id', sctx) =>
                       ((Sinclude id', span), sctx)

                  | NONE =>
                       raise (E.SemanticError ("unbound signature identifier " ^ idToString id, span))))


      and traverseSpecs ctx specs =
         let
            val (specs', ctx', sctx) =
               foldl
               (fn (s, (l, ctx', lctx)) =>
                   let
                      val (s', sctx) = traverseSpec ctx' s
                   in
                      (s' :: l, C.union ctx' sctx, C.union lctx sctx)
                   end)
               ([], ctx, C.empty)
               specs
         in
            (rev specs', ctx', sctx)
         end

         
      and traverseSig ctx (sg_, span) =
         (case sg_ of
             Sident id =>
                (case C.lookupSig ctx id of
                    SOME (id', sctx) =>
                       ((Sident id', span), sctx)

                  | NONE =>
                       raise (E.SemanticError ("unbound signature identifier " ^ idToString id, span)))

           | Ssig specs =>
                let
                   val (specs', _, sctx) = traverseSpecs ctx specs
                in
                   ((Ssig specs', span), sctx)
                end

           | Swhere (s, longid, args, t) =>
                let
                   val (s', sctx) = traverseSig ctx s
                   val t' = traverseTy (bindTyvars ctx args) t
                in
                   (case C.lookupType sctx longid of
                       Present longid' =>
                          (* probably the same as longid, but we won't rely on that *)
                          ((Swhere (s', longid', args, t'), span),
                           sctx)

                     | Absent longid' =>
                          raise (E.SemanticError (String.concat ["where clause identifier ", longidToString longid', " not present in signature"], span)))
                end)
                          

      fun traversePatGen aftv ctx (pat as (pat_, span)) =
         (case pat_ of
             Pwild => (pat, C.empty)

           | Punit => (pat, C.empty)

           | Pident id => (pat, C.bindExp C.empty id)

           | Pnumber _ => (pat, C.empty)

           | Pstring _ => (pat, C.empty)

           | Pchar _ => (pat, C.empty)

           | Pword _ => (pat, C.empty)

           | Pconstr longid =>
                (case C.lookupExp ctx longid of
                    Present (longid', 0) =>
                       ((Pconstr longid', span), C.empty)

                  | Present (_, arity) =>
                       (* This would actually take care of itself, but let's generate consistent
                          error messages.
                       *)
                       raise (E.SemanticError (String.concat ["constructor ", longidToString longid, " takes ", Int.toString arity, " arguments but is given 0"], span))

                  | Absent longid' =>
                       raise (E.SemanticError ("unbound identifier " ^ longidToString longid', span)))

           | Ptuple l =>
                let val (l', lctx) = traversePatsGen aftv ctx l
                in
                   ((Ptuple l', span), lctx)
                end

           | Plist l =>
                let val (l', lctx) = traversePatsGen aftv ctx l
                in
                   ((Plist l', span), lctx)
                end

           (* We won't enforce the arity rule here since we can simulate the desired behavior. *)
           | Papp (longid, (Pwild, sp)) =>
                let
                   val (longid', arity) =
                      (case C.lookupExp ctx longid of
                          Present (_, 0) =>
                             raise (E.SemanticError (String.concat ["constructor ", longidToString longid, " takes 0 arguments but is given 1"], span))

                        | Present x => x

                        | Absent longid' =>
                             raise (E.SemanticError ("unbound identifier " ^ longidToString longid', span)))

                   val ps = List.tabulate (arity, (fn _ => (Pwild, sp)))
                in
                   ((Papp (longid', (Ptuple ps, sp)), span), C.empty)
                end

           | Papp (longid, p) =>
                let
                   val (longid', arity) =
                      (case C.lookupExp ctx longid of
                          Present x => x
                        | Absent longid' =>
                             raise (E.SemanticError ("unbound identifier " ^ longidToString longid', span)))

                   val (p', pctx) = traversePatGen aftv ctx p

                   val actualArity =
                      (case p' of
                          (Ptuple l, _) => length l
                        | _ => 1)
                in
                   if arity = 1 orelse arity = actualArity then
                      ((Papp (longid', p'), span), pctx)
                   else
                      (* We cannot easily simulate the desired behavior on OCaml, so we prohibit this. *)
                      raise (E.SemanticError (String.concat ["constructor ", longidToString longid, " takes ", Int.toString arity, " arguments but is given ", Int.toString actualArity], span))
                end

           | Papprecord (longid, fields) =>
                let
                   val longid' =
                      (case C.lookupExp ctx longid of
                          Present (longid', _) => longid'
                        | Absent longid' =>
                             raise (E.SemanticError ("unbound identifier " ^ longidToString longid', span)))

                   val (fields', fctx) =
                      foldr
                      (fn ((label, p), (l, c)) =>
                          let
                             val (p', c') = traversePatGen aftv ctx p
                          in
                             ((label, p') :: l, C.union c' c)
                          end)
                      (nil, C.empty)
                      fields
                in
                   ((Papprecord (longid', fields'), span), fctx)
                end

           | Pref p =>
                let
                   val (p', pctx) = traversePatGen aftv ctx p
                in
                   ((Pref p', span), pctx)
                end

           | Pas (id, p) =>
                let
                   val (p', pctx) = traversePatGen aftv ctx p
                in
                   ((Pas (id, p'), span), C.bindExp pctx id)
                end

           | Pannot (p, t) =>
                let
                   val (p', pctx) = traversePatGen aftv ctx p
                in
                   ((Pannot (p', traverseTyGen aftv ctx t), span), pctx)
                end

           | Pjuxta juxtas =>
                let
                   val p = PatPrecedence.parse (Context.infixes ctx) juxtas span
                in
                   traversePatGen aftv ctx p
                end)

      and traversePatsGen aftv ctx pats =
         foldr
         (fn (p, (l, c)) =>
             let
                val (p', c') = traversePatGen aftv ctx p
             in
                (p' :: l, C.union c' c)
             end)
         (nil, C.empty)
         pats

      val traversePat = traversePatGen false
      val traversePats = traversePatsGen false


      val nextsym = ref 0
      fun gensymMod () =
         let val n = !nextsym
         in
            nextsym := n+1;
            Symbol.fromValue ("A__" ^ Int.toString n)
         end


      val a0 = Symbol.fromValue "a0"
      val a1 = Symbol.fromValue "a1"
      val zilch = Symbol.fromValue ""


      fun procTyvars ctx tyvars =
         (case !Language.target of
             Language.SML => 
                (bindTyvars ctx tyvars, tyvars)

           | Language.OCAML =>
                (* Have to change these into type identifiers. *)
                List.foldr
                (fn ((var, varsp), (ctx, l)) =>
                    let
                       val var' = Symbol.fromValue ("t__" ^ Symbol.toValue var)
                    in
                       (C.forwardTyvar ctx var var',
                        (var', varsp) :: l)
                    end)
                (ctx, [])
                tyvars)
      

      (* n >= 1 *)
      fun etaExpand n (e as (_, span)) =
         let
            val p =
               if n = 1 then
                  (Pident (a0, span), span)
               else
                  (Ptuple (List.tabulate (n, (fn i => (Pident (Symbol.fromValue ("a" ^ Int.toString i), span), span)))),
                   span)
            
            val arg =
               if n = 1 then
                  (Eident ([a0], span), span)
               else
                  (Etuple (List.tabulate (n, (fn i => (Eident ([Symbol.fromValue ("a" ^ Int.toString i)], span), span)))),
                   span)
         in
            (Elam [(p, (Eapp (e, arg), span), span)], span)
         end


      fun traverseExp ctx (exp as (exp_, span)) =
         (case exp_ of
             Eunit => exp
           | Eident longid =>
                (case C.lookupExp ctx longid of
                    Present (longid', _) =>
                       (Eident longid', span)

                  | Absent longid' =>
                       raise (E.SemanticError ("unbound identifier " ^ longidToString longid', span)))

           | Econstr longid =>
                (case C.lookupExp ctx longid of
                    Present (longid', arity) =>
                       (case !Language.target of
                           Language.SML =>
                              (Econstr longid', span)

                         | Language.OCAML =>
                              if arity = 0 then
                                 (Econstr longid', span)
                              else
                                 etaExpand arity (Econstr longid', span))

                  | Absent longid' =>
                       raise (E.SemanticError ("unbound identifier " ^ longidToString longid', span)))

           | Enumber _ => exp

           | Eword _ => exp

           | Estring _ => exp

           | Echar _ => exp

           | Elet (decs, e) =>
                let val (lpos, rpos) = span
                in
                   traverseLetDecs ctx rpos e [] decs
                end

           | Etuple exps =>
                (Etuple (map (traverseExp ctx) exps), span)

           | Eapprecord (id, fields) =>
                (Eapprecord (id, map (fn (label, exp) => (label, traverseExp ctx exp)) fields),
                 span)

           | Elist exps =>
                (Elist (map (traverseExp ctx) exps), span)

           | Eapp ((e1 as (Econstr longid, sp1)), (e2 as (e2_, _))) =>
                (* Optimize this case not to eta-expand the constructor. *)
                (case C.lookupExp ctx longid of
                    Present (longid', arity) =>
                       if
                          (case !Language.target of Language.SML => true | Language.OCAML => false)
                          orelse
                          arity < 2
                          orelse
                          (case e2_ of
                              Etuple es => arity = length es
                            | _ => false)
                       then
                          (Eapp ((Econstr longid', sp1), traverseExp ctx e2), span)
                       else
                          (Eapp (traverseExp ctx e1, traverseExp ctx e2), span)

                  | Absent longid' =>
                       raise (E.SemanticError ("unbound identifier " ^ longidToString longid', sp1)))
                       
           | Eapp _ =>
                let
                   val (e', _) = traverseExpApp ctx exp
                in
                   e'
                end

           | Ecase (e1, arms) =>
                (Ecase (traverseExp ctx e1, 
                        map
                           (fn (pat, e, sp) => 
                               let 
                                  val (p, pctx) = traversePat ctx pat
                               in
                                  (p, traverseExp (C.union ctx pctx) e, sp)
                               end)
                           arms),
                 span)

           | Etry (e1, arms) =>
                (Etry (traverseExp ctx e1, 
                       map
                          (fn (pat, e, sp) => 
                              let 
                                 val (p, pctx) = traversePat ctx pat
                              in
                                 (p, traverseExp (C.union ctx pctx) e, sp)
                              end)
                          arms), 
                 span)

           | Elam arms =>
                (Elam (map
                          (fn (pat, e, sp) => 
                              let 
                                 val (p, pctx) = traversePat ctx pat
                              in
                                 (p, traverseExp (C.union ctx pctx) e, sp)
                              end) 
                          arms), 
                 span)

           | Elams (ps, t, e) =>
                let
                   val (ps', pctx) = traversePats ctx ps
                in
                   (Elams (ps', Option.map (traverseTy ctx) t, traverseExp (C.union ctx pctx) e), span)
                end

           | Eannot (e, t) => (Eannot (traverseExp ctx e, traverseTy ctx t), span)

           | Eif (e1, e2, e3) => 
                (Eif (traverseExp ctx e1, traverseExp ctx e2, traverseExp ctx e3), span)

           | Eseq es => (Eseq (map (traverseExp ctx) es), span)

           | Eandalso (e1, e2) =>
                (Eandalso (traverseExp ctx e1, traverseExp ctx e2), span)

           | Eorelse (e1, e2) =>
                (Eorelse (traverseExp ctx e1, traverseExp ctx e2), span)

           | Eraise e =>
                (Eraise (traverseExp ctx e), span)

           | Ejuxta juxtas =>
                let
                   val e = ExpPrecedence.parse (Context.infixes ctx) juxtas span
                in
                   traverseExp ctx e
                end

           | Eterm elems =>
                parse ctx NONE elems span)


      and traverseExpApp ctx (exp as (exp_, span)) =
         (case exp_ of
             Eident (longid as ([sym], _)) =>
                (case C.lookupExp ctx longid of
                    Present (longid', _) =>
                       let
                          val (table, _) = Context.starts ctx

                          val starts =
                             Option.getOpt (SymbolHashTable.find table sym, nil)
                       in
                          ((Eident longid', span), starts)
                       end

                  | Absent longid' =>
                       raise (E.SemanticError ("unbound identifier " ^ longidToString longid', span)))

           | Eapp (e1, (Eterm elems, span2)) =>
                let
                   val (e1', starts) = traverseExpApp ctx e1
                   
                   val (start, starts') =
                      (case starts of
                          nil => (NONE, nil)

                        | start :: starts' => (start, starts'))
                in
                   ((Eapp (e1', parse ctx start elems span2), span),
                    starts')
                end

           | Eapp (e1, e2) =>
                let
                   val (e1', starts) = traverseExpApp ctx e1
                
                   val starts' =
                      (case starts of
                          nil => nil

                        | _ :: starts' => starts')
                in
                   ((Eapp (e1', traverseExp ctx e2), span),
                    starts')
                end

           | _ =>
                (traverseExp ctx exp, nil))


      and parse ctx starto elems span =
         let
            val elems' =
               map
               (fn (Lembed e) => Lembed (traverseExp ctx e)
                 | elem => elem)
               elems

            val start =
               (case starto of
                   NONE =>
                      (case Context.starts ctx of
                          (_, NONE) =>
                             raise (E.SemanticError ("No default start symbol", span))

                        | (_, SOME start) => start)

                 | SOME start => start)

            val parser =
               (case SymbolDict.find (Context.parsers ctx) start of
                   SOME p => p

                 | NONE =>
                      raise (E.SemanticError ("Unknown start symbol " ^ Symbol.toValue start, span)))
         in
            (case Parse.parse parser elems' span of
                Sum.INL e => e

              | Sum.INR pos =>
                   raise (E.SyntaxError ("No valid parse for start symbol " ^ Symbol.toValue start, pos)))
         end


      and traverseDec ctx (dec as (dec_, span)) =
         (case dec_ of
             Dval (tyargs, pat, e) => 
                let
                   val (ctx', tyargs') = procTyvars ctx tyargs

                   val (pat', pctx) = traversePatGen true ctx' pat
                in
                   ((Dval (tyargs', pat', traverseExp ctx' e), span),
                    C.union ctx pctx,
                    pctx)
                end

           | Dfun (tyargs, funs) =>
                let
                   val (tctx, tyargs') = procTyvars ctx tyargs
                   val fctx = foldl (fn ((id, _, _), c) => C.bindExp c id) C.empty funs
                   val ctx' = C.union tctx fctx
                in
                   ((Dfun (tyargs',
                           map
                              (fn (id, arms, sp) =>
                                  let
                                     val n =
                                        (case arms of
                                            (ps, _, _, _) :: _ => List.length ps
                                          | [] =>
                                               (* the parser ensures that fun declarations are not empty *)
                                               raise (Fail "precondition"))
                                  in
                                     (id,
                                      map (fn (pats, tyo, e, sp') =>
                                              let
                                                 val () =
                                                    if List.length pats = n then
                                                       ()
                                                    else
                                                       raise (E.SemanticError ("fun clauses take varying number of arguments", sp))

                                                 val (pats', pctx) = traversePatsGen true ctx' pats
                                              in
                                                 (pats', 
                                                  Option.map (traverseTy ctx') tyo,
                                                  traverseExp (C.union ctx' pctx) e, 
                                                  sp')
                                              end) arms,
                                      sp)
                                  end)
                              funs),
                     span),
                    C.union ctx fctx,
                    fctx)
                end

           | Ddo (pat, e) => 
                (* In an expression let, this should be handled by traverseLetDecs, and
                   elsewhere the parser should not permit it to arise.
                *)
                raise (Fail "impossible")

           | Dtype (args, id, t) =>
                ((Dtype (args, id, traverseTy (bindTyvars ctx args) t), span),
                 C.bindType ctx id,
                 C.bindType C.empty id)

           | Ddatatype binds =>
                let
                   val (binds', bctx) = traverseTybinds ctx binds span
                in
                   ((Ddatatype binds', span), 
                    C.union ctx bctx,
                    bctx)
                end

           | Dextension (id, tyo) =>
                let
                   val arity =
                      (case tyo of
                          NONE => 0
                        | SOME (Tprod l, _) => length l
                        | SOME _ => 1)
                in
                   ((Dextension (id, Option.map (traverseTy ctx) tyo), span),
                    C.bindConstr ctx id arity,
                    C.bindConstr C.empty id arity)
                end

           | Dextcopy (id, longid) =>
                (case C.lookupExp ctx longid of
                    Present (longid', arity) =>
                      ((Dextcopy (id, longid'), span),
                       C.bindConstr ctx id arity,
                       C.bindConstr C.empty id arity)

                  | Absent longid' =>
                       raise (E.SemanticError ("unbound identifier " ^ longidToString longid', span)))

           | Dinclude longid =>
                (case C.lookupMod ctx longid of
                    Present (longid', ctx') =>
                       ((Dinclude longid', span), 
                        C.union ctx ctx',
                        ctx')

                  | Absent longid' =>
                       raise (E.SemanticError ("unbound identifier " ^ longidToString longid', span)))

           | Dmod (id, m, so) => 
                let
                   val (m', mctx) = traverseMod ctx m

                   val (so', sctx) =
                      (case so of
                          NONE => (NONE, mctx)

                        | SOME s =>
                             let val (s', sctx) = traverseSig ctx s
                             in
                                (SOME s', sctx)
                             end)
                in
                   ((Dmod (id, m', so'), span),
                    C.bindMod ctx id sctx,
                    C.bindMod C.empty id sctx)
                end

           | Dfunctor (id, arg, s1, m, s2o) => 
                let
                   val (s1', s1ctx) = traverseSig ctx s1
                   val ctx' = C.bindMod ctx arg s1ctx
                   val (m', mctx) = traverseMod ctx' m

                   val (s2o', bodyctx) =
                      (case s2o of
                          NONE => (NONE, mctx)

                        | SOME s2 =>
                             let val (s2', s2ctx) = traverseSig ctx' s2
                             in
                                (SOME s2', s2ctx)
                             end)
                in
                   ((Dfunctor (id, arg, s1', m', s2o'), span),
                    C.bindFun ctx id bodyctx,
                    C.bindFun C.empty id bodyctx)
                end

           | Dfunctoralt (id, ss, specspan, m, s2o) =>
                (case !Language.target of
                    Language.OCAML =>
                       (* Can't render this form in OCaml. *)
                       let
                          val arg = gensymMod ()

                          val (ss', _, s1ctx) = traverseSpecs ctx ss

                          val s1ctx' =
                             C.relocate
                                (fn longid => arg :: longid)
                                s1ctx

                          val ctx' = C.union ctx s1ctx'
                          val (m', mctx) = traverseMod ctx' m
       
                          val (s2o', bodyctx) =
                             (case s2o of
                                 NONE => (NONE, mctx)
       
                               | SOME s2 =>
                                    let val (s2', s2ctx) = traverseSig ctx' s2
                                    in
                                       (SOME s2', s2ctx)
                                    end)
                       in
                          ((Dfunctor (id, (arg, span),
                                      (Ssig ss', specspan),
                                      m', s2o'),
                            span),
                           C.bindFun ctx id bodyctx,
                           C.bindFun C.empty id bodyctx)
                       end

                  | _ =>
                       let
                          val (ss', _, s1ctx) = traverseSpecs ctx ss
                          val ctx' = C.union ctx s1ctx
                          val (m', mctx) = traverseMod ctx' m
       
                          val (s2o', bodyctx) =
                             (case s2o of
                                 NONE => (NONE, mctx)
       
                               | SOME s2 =>
                                    let val (s2', s2ctx) = traverseSig ctx' s2
                                    in
                                       (SOME s2', s2ctx)
                                    end)
                       in
                          ((Dfunctoralt (id, ss', specspan, m', s2o'), span),
                           C.bindFun ctx id bodyctx,
                           C.bindFun C.empty id bodyctx)
                       end)

           | Dsig (id, s) =>
                let
                   val (s', sctx) = traverseSig ctx s
                in
                   ((Dsig (id, s'), span),
                    C.bindSig ctx id sctx,
                    C.bindSig C.empty id sctx)
                end)


      (* All this business is to deal with "do" pseudo-declarations.

         ctx is the context (including acc's bindings)
         rpos is the right-location of the "end".
         exp is the body of the let
         acc is the accumulated traversed declarations (reversed)
         decs are the declarations left to traverse
      *)
      and traverseLetDecs ctx rpos exp acc decs =
         (case decs of
             nil => 
                traverseLetDecsBase rpos (traverseExp ctx exp) acc

           | (Ddo (pat, e), (lposDo, _)) :: rest =>
                let
                   val (pat', pctx) = traversePatGen true ctx pat
                   val exp' = traverseLetDecs (C.union ctx pctx) rpos exp [] rest

                   val spClause = Span.join (#2 pat) (#2 exp')
                   val sp = (lposDo, #2 (#2 exp'))
                   (* The span for the app is the same as for the lambda, because the
                      app's extra material is all in the middle. *)

                   val exp'' =
                      (Eapp (traverseExp ctx e, 
                             (Elam [(pat', exp', spClause)], sp)), sp)
                in
                   traverseLetDecsBase rpos exp'' acc
                end

           | dec :: rest =>
                let
                   val (dec', ctx', dctx) = traverseDec ctx dec
                in
                   traverseLetDecs ctx' rpos exp (dec' :: acc) rest
                end)
         

      and traverseLetDecsBase rpos exp acc =
         (case rev acc of
             nil => exp

           | l as ((_, (lpos, _)) :: _) =>
                (Elet (l, exp), (lpos, rpos)))


      and traverseDecs ctx decs =
         let
            val (decs', ctx', dctx) =
               foldl
               (fn (d, (l, ctx, lctx)) =>
                   let
                      val (d', ctx', dctx) = traverseDec ctx d
                   in
                      (d' :: l, ctx', C.union lctx dctx)
                   end)
               ([], ctx, C.empty)
               decs
         in
            (rev decs', ctx', dctx)
         end


      and traverseMod ctx (md as (mod_, span)) =
         (case mod_ of
             Mident longid =>
                (case C.lookupMod ctx longid of
                    Present (longid', ctx') =>
                       ((Mident longid', span), ctx')

                  | Absent longid' =>
                       raise (E.SemanticError ("unbound identifier " ^ longidToString longid', span)))

           | Mstruct decs =>
                let
                   val (decs', _, dctx) = traverseDecs ctx decs
                in
                   ((Mstruct decs', span), dctx)
                end

           | Mapp (id, m) =>
                (case C.lookupFun ctx id of
                    SOME (id', fctx) =>
                       let
                          val (m', _) = traverseMod ctx m
                       in
                          ((Mapp (id', m), span), fctx)
                       end

                  | NONE =>
                       raise (E.SemanticError ("unbound functor identifier " ^ idToString id, span)))

           | Mappalt (id, ds, dspan) => 
                (case C.lookupFun ctx id of
                    SOME (id', fctx) =>
                       let
                          val (ds', _, _) = traverseDecs ctx ds
                       in
                          (case !Language.target of
                              Language.OCAML =>
                                 ((Mapp (id', (Mstruct ds', dspan)), span), fctx)

                            | _ =>
                                 ((Mappalt (id', ds', dspan), span), fctx))
                       end

                  | NONE =>
                       raise (E.SemanticError ("unbound functor identifier " ^ idToString id, span)))
                
           | Mseal (m, s) => 
                let
                   val (m', _) = traverseMod ctx m
                   val (s', sctx) = traverseSig ctx s
                in
                   ((Mseal (m', s'), span), sctx)
                end)


      fun traverseGdefsMain ctx infixes rules reserved starts default gdefs =
         (case gdefs of
             [] =>
                { infixes = rev infixes,
                  rules = rev rules,
                  reserved = reserved,  (* the order doesn't matter *)
                  starts = rev starts,
                  default = default }

           | Ginfix (assoc, mode, (precnum, precnumsp), ids) :: rest =>
                let
                   val assoc' =
                      if assoc then PrecedenceTable.LEFT else PrecedenceTable.RIGHT

                   val mode' =
                      if mode then PrecedenceTable.CURRIED else PrecedenceTable.TUPLED

                   val () =
                      if precnum < 0 orelse precnum > 9 then
                         raise (E.SemanticError ("illegal infix precedence", precnumsp))
                      else
                         ()

                   val precedence = (precnum, assoc', mode')

                   val infixes' = map (fn (sym, _) => (sym, precedence)) ids @ infixes
                in
                   traverseGdefsMain ctx infixes' rules reserved starts default rest
                end

           | Grule ((id, idsp), n, rhs, action as (_, actionsp), sp) :: rest =>
                let
                   val action' =
                      (case C.lookupExp ctx action of
                          Present ((action', _), _) => action'

                        | Absent longid' =>
                             raise (E.SemanticError ("unbound identifier " ^ longidToString longid', actionsp)))

                   val rhs' =
                      map
                         (fn Terminal sym => Parse.Terminal sym
                           | TerminalIdent sym => Parse.TerminalIdent sym
                           | Nonterminal ((sym, _), id) => Parse.Nonterminal (sym, id))
                         rhs

                   val rule = ((id, n), rhs', action')

                   val () =
                      if List.exists (fn sym => Symbol.eq (id, sym)) Parse.reservedNonterminals then
                         raise (E.SemanticError ("reserved nonterminal " ^ Symbol.toValue id ^ " on left-hand-side of production", idsp))
                      else
                         ()
                in
                   traverseGdefsMain ctx infixes (rule :: rules) reserved starts default rest
                end

           | Greserved (idents, (nonterm, _)) :: rest =>
                let
                   val reserved' =
                      List.foldl
                         (fn ((sym, _), l) => (sym, nonterm) :: l)
                         reserved
                         idents
                in
                   traverseGdefsMain ctx infixes rules reserved' starts default rest
                end

           | Gstart ((sym, _), idopts) :: rest =>
                let
                   val start =
                      (sym, map (fn SOME (s, _) => SOME s | NONE => NONE) idopts)
                in
                   traverseGdefsMain ctx infixes rules reserved (start :: starts) default rest
                end

           | Gdefault (id, _) :: rest =>
                traverseGdefsMain ctx infixes rules reserved starts (SOME id) rest

           | Gmod ((id, _), longid as (_, sp)) :: rest =>
                let
                   val ctx' =
                      (case C.lookupMod ctx longid of
                          Present ((longid', _), mctx) =>
                             C.forwardMod ctx id (longid', mctx)

                        | Absent longid' =>
                             raise (E.SemanticError ("unbound identifier " ^ longidToString longid', sp)))
                in
                   traverseGdefsMain ctx' infixes rules reserved starts default rest
                end

           | Gopen (longid as (_, sp)) :: rest =>
                let
                   val ctx' =
                      (case C.lookupMod ctx longid of
                          Present ((longid', _), mctx) =>
                             C.union ctx
                                (C.relocate (fn longid'' => longid' @ longid'') mctx)

                        | Absent longid' =>
                             raise (E.SemanticError ("unbound identifier " ^ longidToString longid', sp)))
                in
                   traverseGdefsMain ctx' infixes rules reserved starts default rest
                end

           | Ginclude (id, idsp) :: rest =>
                (case C.lookupBundle ctx id of
                    NONE =>
                       raise (E.SemanticError ("undefined grammar extension " ^ Symbol.toValue id, idsp))

                  | SOME { infixes=infixes', rules=rules', reserved=reserved', starts=starts', default=default' } =>
                       traverseGdefsMain ctx
                          (List.revAppend (infixes', infixes))
                          (List.revAppend (rules', rules))
                          (reserved' @ reserved)
                          (List.revAppend (starts', starts))
                          (case default' of NONE => default | SOME _ => default')
                          rest))
                    

      fun traverseGdefs ctx gdefs = traverseGdefsMain ctx [] [] [] [] NONE gdefs


      val symIt = Symbol.fromValue "it"

      fun traverseDirective ctx (dir, span) =
         (case dir of
             Vdec d => 
                let
                   val (d', ctx', dctx) = traverseDec ctx d
                in
                   ((Vdec d', span), ctx', dctx)
                end

           | Vexp e =>
                let
                   val e' = traverseExp ctx e
                   val (pos, _) = span
                   val itspan = (pos, pos)
                in
                   ((Vdec (Dval ([], (Pident (symIt, itspan), itspan), e'), span), span),
                    C.bindExp ctx (symIt, itspan),
                    C.bindExp C.empty (symIt, itspan))
                end

           | Vgrammardef ((id, idsp), gdefs) =>
                if C.defined ctx id then
                   raise (E.SemanticError ("multiply defined grammar extension " ^ Symbol.toValue id, idsp))
                else
                   let
                      val gdefs' = traverseGdefs ctx gdefs
                   in
                      ((Vnull, span),
                       C.define ctx id gdefs',
                       C.define C.empty id gdefs')
                   end

           | Vgrammaron ids =>
                let
                   val (c, dc) =
                      List.foldl
                         (fn ((id, idsp), (c, dc)) =>
                             if C.defined ctx id then
                                (C.activate c id,
                                 C.activate dc id)
                             else
                                raise (E.SemanticError ("undefined grammar extension " ^ Symbol.toValue id, idsp)))
                         (ctx, C.empty)
                         ids
                in
                   ((Vnull, span), c, dc)
                end

           | Vgrammaroff ids =>
                let
                   val (c, dc) =
                      List.foldl
                         (fn ((id, idsp), (c, dc)) =>
                             if C.defined ctx id then
                                (C.deactivate c id,
                                 C.deactivate dc id)
                             else
                                raise (E.SemanticError ("undefined grammar extension " ^ Symbol.toValue id, idsp)))
                         (ctx, C.empty)
                         ids
                in
                   ((Vnull, span), c, dc)
                end

           | Vnull => ((Vnull, span), ctx, C.empty))


      fun traverse ctx (dirs, span) =
         let
            val (dirs', ctx', exports) =
               foldl
               (fn (dir, (l, ctx, exports)) =>
                   let
                      val (dir', ctx', exports') = traverseDirective ctx dir
                   in
                      (dir' :: l, ctx', C.union exports exports')
                   end)
               ([], ctx, C.empty)
               dirs
         in
            ((rev dirs', span), ctx', exports)
         end

   end
