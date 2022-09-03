
signature CONTEXT =
   sig

      type symbol = Symbol.symbol
      type identifier = Syntax.identifier
      type longid = Syntax.longid

      type context

      val empty : context


      (* Identifier stuff *)
      
      val forwardExp : context -> symbol -> symbol list * int -> context
      val forwardType : context -> symbol -> symbol list -> context
      val forwardTyvar : context -> symbol -> symbol -> context
      val forwardSig : context -> symbol -> (symbol * context) -> context
      val forwardMod : context -> symbol -> (symbol list * context) -> context
      val forwardFun : context -> symbol -> (symbol * context) -> context

      val bindExp : context -> identifier -> context
      val bindConstr : context -> identifier -> int -> context
      val bindType : context -> identifier -> context
      val bindTyvar : context -> identifier -> context
      val bindSig : context -> identifier -> context -> context
      val bindMod : context -> identifier -> context -> context
      val bindFun : context -> identifier -> context -> context

      datatype 'a result = Absent of longid | Present of 'a

      val lookupExp : context -> longid -> (longid * int) result
      val lookupType : context -> longid -> longid result
      val lookupTyvar : context -> identifier -> identifier option
      val lookupSig : context -> identifier -> (identifier * context) option
      val lookupMod : context -> longid -> (longid * context) result
      val lookupFun : context -> identifier -> (identifier * context) option

      (* Applies function to the longid of each binding (except tyvars).
         If context contains any sig or functor bindings, the
         function must not alter the longid's length.
      *)
      val relocate : (symbol list -> symbol list) -> context -> context


      (* Grammar stuff *)

      type key = Symbol.symbol

      type bundle =
         {
         infixes : (symbol * PrecedenceTable.precedence) list,
         rules : Parse.rule list,
         reserved : (symbol * symbol) list,
         starts : (symbol * symbol option list) list,
         default : symbol option
         }

      val defined : context -> key -> bool
      val define : context -> key -> bundle -> context
      val activate : context -> key -> context
      val deactivate : context -> key -> context
      
      val lookupBundle : context -> key -> bundle option
      val infixes : context -> PrecedenceTable.table
      val parsers : context -> Parse.parser SymbolDict.dict
      val starts : context -> symbol option list SymbolHashTable.table * symbol option
      val actives : context -> symbol list



      val union : context -> context -> context

      exception Collision of string
      val unionDisj : context -> context -> context


      val pu : context Pickle.pu


      (* Detect dependencies *)
      val register : context -> (unit -> unit) -> unit
      val pingActives : context -> unit
      val reset : unit -> unit

   end


structure Context :> CONTEXT =
   struct

      type symbol = Symbol.symbol

      type identifier = Syntax.identifier
      type longid = Syntax.longid

      structure D = SymbolDict
      structure T = SymbolHashTable

      type key = Symbol.symbol

      type bundle =
         {
         infixes : (symbol * PrecedenceTable.precedence) list,
         rules : Parse.rule list,
         reserved : (symbol * symbol) list,
         starts : (symbol * symbol option list) list,
         default : symbol option
         }

      datatype context =
         C of { 
              exps  : (symbol list * int) D.dict,
              types : symbol list D.dict,
              tyvars : symbol D.dict,
              sigs : (symbol * context) D.dict,
              mods : (symbol list * context) D.dict,
              funs : (symbol * context) D.dict,

              defs : bundle D.dict,
              acts : symbol list,
              deacts : symbol list,
              infixCache : PrecedenceTable.table Susp.susp,
              parsersCache : Parse.parser D.dict Susp.susp,
              startsCache : (symbol option list SymbolHashTable.table * symbol option) Susp.susp
              }


 
      val empty = 
         C { exps = D.empty,
             types = D.empty,
             tyvars = D.empty,
             sigs = D.empty,
             mods = D.empty,
             funs = D.empty,
             defs = D.empty,
             acts = nil,
             deacts = nil,
             infixCache = Susp.delay (fn () => T.table 1),
             parsersCache = Susp.delay (fn () => D.empty),
             startsCache = Susp.delay (fn () => (SymbolHashTable.table 1, NONE)) }
 
 
      fun forwardExp (C {exps, types, tyvars, sigs, mods, funs, defs, acts, deacts, infixCache, parsersCache, startsCache}) id (longid, arity) =
         C { exps = D.insert exps id (longid, arity),
             types = types,
             tyvars = tyvars,
             sigs = sigs,
             mods = mods,
             funs = funs,
             defs = defs,
             acts = acts,
             deacts = deacts,
             infixCache = infixCache,
             parsersCache = parsersCache,
             startsCache = startsCache }
 
      fun forwardType (C {exps, types, tyvars, sigs, mods, funs, defs, acts, deacts, infixCache, parsersCache, startsCache}) id longid =
         C { exps = exps,
             types = D.insert types id longid,
             tyvars = tyvars,
             sigs = sigs,
             mods = mods,
             funs = funs,
             defs = defs,
             acts = acts,
             deacts = deacts,
             infixCache = infixCache,
             parsersCache = parsersCache,
             startsCache = startsCache }
 
      fun forwardTyvar (C {exps, types, tyvars, sigs, mods, funs, defs, acts, deacts, infixCache, parsersCache, startsCache}) id id' =
         C { exps = exps,
             types = types,
             tyvars = D.insert tyvars id id',
             sigs = sigs,
             mods = mods,
             funs = funs,
             defs = defs,
             acts = acts,
             deacts = deacts,
             infixCache = infixCache,
             parsersCache = parsersCache,
             startsCache = startsCache }
 
      fun forwardSig (C {exps, types, tyvars, sigs, mods, funs, defs, acts, deacts, infixCache, parsersCache, startsCache}) id (id', c) =
         C { exps = exps,
             types = types,
             tyvars = tyvars,
             sigs = D.insert sigs id (id', c),
             mods = mods,
             funs = funs,
             defs = defs,
             acts = acts,
             deacts = deacts,
             infixCache = infixCache,
             parsersCache = parsersCache,
             startsCache = startsCache }
 
      fun forwardMod (C {exps, types, tyvars, sigs, mods, funs, defs, acts, deacts, infixCache, parsersCache, startsCache}) id (longid, c) =
         C { exps = exps,
             types = types,
             tyvars = tyvars,
             sigs = sigs,
             mods = D.insert mods id (longid, c),
             funs = funs,
             defs = defs,
             acts = acts,
             deacts = deacts,
             infixCache = infixCache,
             parsersCache = parsersCache,
             startsCache = startsCache }
 
      fun forwardFun (C {exps, types, tyvars, sigs, mods, funs, defs, acts, deacts, infixCache, parsersCache, startsCache}) id (id', c) =
         C { exps = exps,
             types = types,
             tyvars = tyvars,
             sigs = sigs,
             mods = mods,
             funs = D.insert funs id (id', c),
             defs = defs,
             acts = acts,
             deacts = deacts,
             infixCache = infixCache,
             parsersCache = parsersCache,
             startsCache = startsCache }
 
 
      fun bindExp ctx (id, _) = forwardExp ctx id ([id], 0)
      fun bindConstr ctx (id, _) n = forwardExp ctx id ([id], n)
      fun bindType ctx (id, _) = forwardType ctx id [id]
      fun bindTyvar ctx (id, _) = forwardTyvar ctx id id
      fun bindSig ctx (id, _) c = forwardSig ctx id (id, c)
      fun bindMod ctx (id, _) c = forwardMod ctx id ([id], c)
      fun bindFun ctx (id, _) c = forwardFun ctx id (id, c)
 
 
      val currEpoch = ref 0
      
      val registeredMods : (int ref * (unit -> unit)) T.table = T.table 53
      val registeredSigs : (int ref * (unit -> unit)) T.table = T.table 53
      val registeredFuns : (int ref * (unit -> unit)) T.table = T.table 53
      val registeredGrammars :  (int ref * (unit -> unit)) T.table = T.table 53

      fun register (C { mods, sigs, funs, defs, ... }) f =
         let
            val entry = (ref 0, f)
         in
            currEpoch := !currEpoch + 1;
   
            D.app
               (fn (sym, _) => T.insert registeredMods sym entry)
               mods;
   
            D.app
               (fn (sym, _) => T.insert registeredSigs sym entry)
               sigs;
   
            D.app
               (fn (sym, _) => T.insert registeredFuns sym entry)
               funs;
   
            D.app
               (fn (sym, _) => T.insert registeredGrammars sym entry)
               defs
         end

      fun reset () =
         (
         currEpoch := 0;
         T.reset registeredMods 53;
         T.reset registeredSigs 53;
         T.reset registeredFuns 53;
         T.reset registeredGrammars 53
         )

      fun ping t sym =
         (case T.find t sym of
             NONE => ()

           | SOME (er, f) =>
                if !currEpoch > !er then
                   (
                   er := !currEpoch;
                   f ()
                   )
                else
                   ())

      fun pingActives (C { acts, ... }) =
         List.app (ping registeredGrammars) acts

      fun pingHead l =
         (case l of
             [] => raise (Fail "preconditions")

           | [_] => ()

           | headsym :: _ :: _ =>
                ping registeredMods headsym)


      datatype 'a result = Absent of longid | Present of 'a

      fun loop (ctx as C {mods, ...}) acc longid span k =
         (case longid of
             nil => raise (Fail "precondition")
 
           | [id] =>
                k (ctx, acc, id)
 
           | id :: rest =>
                (case D.find mods id of
                    NONE => Absent (List.rev (id :: acc), span)
 
                  | SOME (longid', ctx') =>
                       loop ctx' (List.revAppend (longid', acc)) rest span k))


      fun lookupExp ctx (longid, span) =
         loop ctx [] longid span
         (fn (C {exps, ...}, acc, id) =>
             (case D.find exps id of
                 NONE => Absent (List.rev (id :: acc), span)

               | SOME (l, arity) =>
                    let
                       val longid' = rev (List.revAppend (l, acc))
                    in
                       pingHead longid';
                       Present ((longid', span), arity)
                    end))
 
 
      fun lookupType ctx (longid, span) =
         loop ctx [] longid span
         (fn (C {types, ...}, acc, id) =>
             (case D.find types id of
                 NONE => Absent (List.rev (id :: acc), span)

               | SOME l =>
                    let
                       val longid' = rev (List.revAppend (l, acc))
                    in
                       pingHead longid';
                       Present (longid', span)
                    end))

 
      fun lookupTyvar (C {tyvars, ...}) (id, span) =
         (case D.find tyvars id of
             NONE => NONE
 
           | SOME id' =>
                SOME (id', span))
 
      
      fun lookupSig (C {sigs, ...}) (id, span) =
         (case D.find sigs id of
             NONE => NONE
 
           | SOME (id', ctx') =>
                (
                ping registeredSigs id';
                SOME ((id', span), ctx')
                ))
 
      
      fun lookupMod ctx (longid, span) =
         loop ctx [] longid span
         (fn (C {mods, ...}, acc, id) =>
             (case D.find mods id of
                 NONE => Absent (List.rev (id :: acc), span)

               | SOME (l, ctx') =>
                    let
                       val longid' = rev (List.revAppend (l, acc))
                    in
                       ping registeredMods (hd longid');
                       Present ((longid', span), ctx')
                    end))
 

      fun lookupFun (C {funs, ...}) (id, span) =
         (case D.find funs id of
             NONE => NONE
 
           | SOME (id', ctx') =>
                (
                ping registeredFuns id';
                SOME ((id', span), ctx')
                ))
 

      fun relocate f (C {exps, types, tyvars, sigs, mods, funs, defs, acts, deacts, infixCache, parsersCache, startsCache }) =
         C {
           exps = D.map (fn (longid, arity) => (f longid, arity)) exps,

           types = D.map f types,

           tyvars = tyvars,

           sigs = D.map 
                     (fn (id, ctx) => 
                            (case f [id] of [id'] => (id', ctx) 
                        | _ => raise (Fail "precondition")))
                     sigs,

           mods = D.map (fn (longid, ctx) => (f longid, ctx)) mods,

           funs = D.map 
                     (fn (id, ctx) => 
                            (case f [id] of [id'] => (id', ctx) 
                        | _ => raise (Fail "precondition")))
                     funs,

           defs = defs,
           acts = acts,
           deacts = deacts,
           infixCache = infixCache,
           parsersCache = parsersCache,
           startsCache = startsCache
           }


      
      fun defined (C {defs, ...}) key = D.member defs key

      fun define (C {exps, types, tyvars, sigs, mods, funs, defs, acts, deacts, infixCache, parsersCache, startsCache}) key bundle =
         C { exps = exps,
             types = types,
             tyvars = tyvars,
             sigs = sigs,
             mods = mods,
             funs = funs,
             defs = D.insert defs key bundle,
             acts = acts,
             deacts = deacts,
             infixCache = infixCache,
             parsersCache = parsersCache,
             startsCache = startsCache }

      fun remove key l acc =
         (case l of
             nil => rev acc

           | h :: t =>
                if Symbol.eq (key, h) then
                   List.revAppend (acc, t)
                else
                   remove key t (h :: acc))

      fun makeInfix defs acts =
         Susp.delay
         (fn () =>
            let
               val table : PrecedenceTable.precedence T.table = T.table 43

               val () =
                  ListUtil.revapp
                     (fn key =>
                         (case D.find defs key of
                             NONE =>
                                (* This shouldn't happen in use; here we'll just ignore it. *)
                                ()

                           | SOME ({ infixes, ... }:bundle) =>
                                List.app
                                   (fn (sym, prec) =>
                                       T.insert table sym prec)
                                   infixes))
                     acts
            in
               table
            end)

      fun makeParsers defs acts =
         Susp.delay
         (fn () =>
            let
               val (rules, reserved, starts) =
                  List.foldl
                     (fn (key, (r, d, s)) =>
                         (case D.find defs key of
                             NONE =>
                                (* This shouldn't happen in use; here we'll just ignore it. *)
                                (r, d, s)
   
                           | SOME ({ rules, reserved, starts, default, ... }:bundle) =>
                                (rules @ r,

                                 foldl
                                    (fn ((sym, nonterm), d) =>
                                        let
                                           val (_, _, d') =
                                              SymbolDict.operate d nonterm
                                                 (fn () => SymbolSet.singleton sym)
                                                 (fn s => SymbolSet.insert s sym)
                                        in
                                           d'
                                        end)
                                    d
                                    reserved,

                                 foldl
                                    (fn ((_, l), s) => 
                                        foldl
                                           (fn (NONE, s) => s
                                             | (SOME sym, s) => SymbolSet.insert s sym)
                                           s
                                           l)
                                    (case default of
                                        NONE => s
                                      | SOME sym => SymbolSet.insert s sym)
                                    starts)))
                     (nil, SymbolDict.empty, SymbolSet.empty)
                     acts

               val parsers = Parse.compile rules reserved starts
            in
               parsers
            end)

      fun makeStarts defs acts =
         Susp.delay
         (fn () =>
             let
                val table : symbol option list SymbolHashTable.table = SymbolHashTable.table 43
   
                val default =
                   (* for side-effects in addition to default *)
                   List.foldr
                      (fn (key, default) =>
                          (case D.find defs key of
                              NONE =>
                                 (* This shouldn't happen in use; here we'll just ignore it. *)
                                 default

                            | SOME ({ starts, default=default', ...}:bundle) =>
                                 (
                                 List.app
                                    (fn (sym, symopts) =>
                                        SymbolHashTable.insert table sym symopts)
                                    starts;
                                 (case default' of NONE => default | SOME _ => default')
                                 )))
                      NONE
                      acts
             in
                (table, default)
             end)


      fun activate (C {exps, types, tyvars, sigs, mods, funs, defs, acts, deacts, infixCache, parsersCache, startsCache}) key =
         let
            val acts' = key :: remove key acts []
            val deacts' = remove key deacts []
         in
            ping registeredGrammars key;
   
            C { exps = exps,
                types = types,
                tyvars = tyvars,
                sigs = sigs,
                mods = mods,
                funs = funs,
                defs = defs,
                acts = acts',
                deacts = deacts',
                infixCache = makeInfix defs acts',
                parsersCache = makeParsers defs acts',
                startsCache = makeStarts defs acts' }
         end

      fun deactivate (C {exps, types, tyvars, sigs, mods, funs, defs, acts, deacts, infixCache, parsersCache, startsCache}) key =
         let
            val acts' = remove key acts []
            val deacts' = key :: remove key deacts []
         in
            C { exps = exps,
                types = types,
                tyvars = tyvars,
                sigs = sigs,
                mods = mods,
                funs = funs,
                defs = defs,
                acts = acts',
                deacts = deacts',
                infixCache = makeInfix defs acts',
                parsersCache = makeParsers defs acts',
                startsCache = makeStarts defs acts' }
         end
   
      fun actives (C { acts, ... }) = acts

      fun infixes (C { infixCache, ... }) = Susp.force infixCache

      fun parsers (C { parsersCache, ... }) = Susp.force parsersCache

      fun starts (C { startsCache, ... }) = Susp.force startsCache

      fun lookupBundle (C { defs, ... }) key = D.find defs key


      exception Collision of string

      fun unionMain tolerant
         (C {exps=exps1, types=types1, tyvars=tyvars1, sigs=sigs1, mods=mods1, funs=funs1, defs=defs1, acts=acts1, deacts=deacts1, ...}) 
         (C {exps=exps2, types=types2, tyvars=tyvars2, sigs=sigs2, mods=mods2, funs=funs2, defs=defs2, acts=acts2, deacts=deacts2, ...}) =
         let
            fun collide namespace (sym, _, x) =
               if tolerant then
                  x
               else
                  raise (Collision (String.concat [namespace, " identifier ", Symbol.toValue sym]))

            val defs = D.union defs1 defs2 (collide "grammar")

            val acts =
               acts2
               @
               (case deacts2 of
                   nil => acts1

                 | _ =>
                      List.filter
                         (fn sym => not (List.exists (fn sym' => Symbol.eq (sym, sym')) deacts2))
                         acts1)

            val deacts =
               deacts2
               @
               (case acts2 of
                   nil => deacts1

                 | _ =>
                      List.filter
                      (fn sym => not (List.exists (fn sym' => Symbol.eq (sym, sym')) acts2))
                      deacts1)
         in
            C {
              exps = D.union exps1 exps2 (collide "expression"),
              types = D.union types1 types2 (collide "type"),
              tyvars = D.union tyvars1 tyvars2 (collide "tyvar"),
              sigs = D.union sigs1 sigs2 (collide "signature"),
              mods = D.union mods1 mods2 (collide "structure"),
              funs = D.union funs1 funs2 (collide "functor"),

              defs = defs,
              acts = acts,
              deacts = deacts,
              infixCache = makeInfix defs acts,
              parsersCache = makeParsers defs acts,
              startsCache = makeStarts defs acts
              }
         end

      val union = unionMain true
      val unionDisj = unionMain false



      structure P = Pickle

      structure DP = DictPickleableFun (structure Key = SymbolPickleable
                                        structure Dict = SymbolDict)

      val puSymbol = SymbolPickleable.pu
      val puDict = DP.pu

      local
         open PrecedenceTable
      in

         val puAssoc =
            P.alt
            (fn LEFT => 0 | RIGHT => 1)
            [P.const LEFT, P.const RIGHT]

         val puMode =
            P.alt
            (fn CURRIED => 0 | TUPLED => 1)
            [P.const CURRIED, P.const TUPLED]
            
      end

      val puPrecedence = P.tuple3 P.int puAssoc puMode

      val puNonterm = P.pair puSymbol P.int

      local
         open Parse

         fun impossible () = raise (Fail "impossible")
      in

         val puRhselem =
            P.alt
               (fn Terminal _ => 0 | TerminalIdent _ => 1 | Nonterminal _ => 2)
               [P.wrap (fn (Terminal x) => x | _ => impossible ()) Terminal puSymbol,
                P.wrap (fn (TerminalIdent x) => x | _ => impossible ()) TerminalIdent puSymbol,
                P.wrap (fn (Nonterminal x) => x | _ => impossible ()) Nonterminal puNonterm]

      end

      val puAction = P.list puSymbol

      val puRule =
         P.tuple3
            puNonterm
            (P.list puRhselem)
            puAction

      val puBundle =
         P.wrap
            (fn { infixes, rules, reserved, starts, default } => (infixes, rules, reserved, starts, default))
            (fn (infixes, rules, reserved, starts, default) =>
                { infixes=infixes, rules=rules, reserved=reserved, starts=starts, default=default })
            (P.tuple5
                (P.list (P.pair puSymbol puPrecedence))
                (P.list puRule)
                (P.list (P.pair puSymbol puSymbol))
                (P.list (P.pair puSymbol (P.list (P.option puSymbol))))
                (P.option puSymbol))

      val pu =
         P.fix
            (fn pu =>
                P.wrap
                   (fn (C { exps, types, tyvars, sigs, mods, funs, defs, acts, deacts, ... }) =>
                       (exps, types, tyvars, sigs, mods, funs, defs, acts, deacts))
                   (fn (exps, types, tyvars, sigs, mods, funs, defs, acts, deacts) =>
                      C { exps=exps, types=types, tyvars=tyvars, sigs=sigs, mods=mods, funs=funs,
                          defs=defs, acts=acts, deacts=deacts,
                          infixCache = makeInfix defs acts,
                          parsersCache = makeParsers defs acts,
                          startsCache = makeStarts defs acts })
                   (P.tuple9
                       (puDict (P.pair (P.list puSymbol) P.int))
                       (puDict (P.list puSymbol))
                       (puDict puSymbol)
                       (puDict (P.pair puSymbol pu))
                       (puDict (P.pair (P.list puSymbol) pu))
                       (puDict (P.pair puSymbol pu))
                       (puDict puBundle)
                       (P.list puSymbol)
                       (P.list puSymbol)))

   end
