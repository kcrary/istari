
(* The customizable parser for terms. *)

signature PARSE =
   sig

      type symbol = Symbol.symbol
      type nonterm = symbol * int

      datatype rhselem =
         Terminal of symbol  (* matches Llexemes *)
       | TerminalIdent of symbol  (* matches Lidents *)
       | Nonterminal of symbol * int

      type action = Symbol.symbol list
      type rule = nonterm * rhselem list * action

      type parser

      val nullParser : parser

      (* Takes (rules, reserved, starts)
         where
         - rules is a list of rules
         - reserved maps nonterminals to blacklisted symbols
         - start is a set of start symbols

         Returns a mapping from start symbols to parsers.

         Priority:
         1. higher-precedence rules take priority
         2. rules appearing later in the list take priority
         3. left-associative parses take priority
      *)
      val compile : rule list 
                    -> SymbolSet.set SymbolDict.dict
                    -> SymbolSet.set 
                    -> parser SymbolDict.dict

      val parse : parser -> Syntax.element list -> Span.span -> (Syntax.exp, Span.pos) Sum.sum

      val reservedNonterminals : Symbol.symbol list

   end


structure Parse :> PARSE =
   struct

      structure S = Syntax

      type span = Span.span
      type identifier = S.identifier
      type exp = S.exp
      type element = S.element

      type symbol = Symbol.symbol
      type nonterm = symbol * int

      datatype rhselem =
         Terminal of symbol  (* matches Llexemes *)
       | TerminalIdent of symbol  (* matches Lidents *)
       | Nonterminal of symbol * int

      type action = symbol list
      type rule = nonterm * rhselem list * action

      structure P = FHParseFun (type elem = element)

      structure D = SplayDict (structure Key =
                                  PairOrdered (structure Ordered1 = SymbolOrdered
                                               structure Ordered2 = IntOrdered))

      structure SS = SymbolSet

      type parser = exp P.parser

      val impossible = Fail "impossible"

      val nullParser : parser = P.fail



      (* Putting the starting position into a ref is a hack, but it dramatically simplifies the plumbing. *)

      val startPos = ref Span.origin

      fun elementToSpan elem =
         (case elem of
             S.Lident (_, span) => span
           | S.Llongid (_, span) => span
           | S.Llexeme (_, span) => span
           | S.Lstring (_, span) => span
           | S.Lnumber (_, _, span) => span
           | S.Lembed (_, span) => span)

      (* |vec| > 0 and 0 <= i <= |vec| *)
      fun getInputPos vec i =
         #1 (elementToSpan (Vector.sub (vec, i)))
         handle Subscript =>
            (* error is at the end of the input *)
            (#2 (elementToSpan (Vector.sub (vec, i-1)))
             handle Subscript =>
                (* the input is empty *)
                !startPos)

      fun parse p elems (pos, _) = 
         (
         startPos := Span.add pos 1;
         
         (case P.parse p elems of
             Sum.INL x => Sum.INL x

           | Sum.INR i => Sum.INR (getInputPos (Vector.fromList elems) i))
         )




      type entry = 
         parser              (* anchored parser *)
         * parser ref        (* using the parser in this reference *)
         * parser list ref   (* which is to be updated with the combination of these *)


      fun lookup table key =
         (case D.find (!table) key of
             SOME (p, pr, lr) => (p, lr)

           | NONE =>
                let
                   val pr = ref P.fail
                   val p = P.anchor (Susp.delay (fn () => !pr))
                   val lr = ref nil
                in
                   table := D.insert (!table) key (p, pr, lr);
                   (p, lr)
                end)
            

      val unitExp = S.Etuple []


      local

         fun string _ elem =
            (case elem of
                S.Lstring (str, span) => SOME (S.Estring str, span)
              | _ => NONE)

         fun number _ elem =
            (case elem of
                S.Lnumber (n, _, span) => SOME (S.Enumber n, span)
              | _ => NONE)

         fun embed _ elem =
            (case elem of
                S.Lembed e => SOME e
              | _ => NONE)

         fun ident reserved elem =
            (case elem of
                S.Lident (sym, span) =>
                   if SS.member reserved sym then
                      NONE
                   else
                      SOME (S.Estring (Symbol.toValue sym), span)

              | _ => NONE)

         fun longid _ elem =
            (case elem of
                S.Llongid (syms, span) =>
                   SOME (S.Elist (map (fn sym => (S.Estring (Symbol.toValue sym), span)) syms),
                         span)

              | _ => NONE)

         fun lexeme _ elem =
            (case elem of
                S.Llexeme (sym, span) => SOME (S.Estring (Symbol.toValue sym), span)
              | _ => NONE)

         val builtin =
            [
            ("STRING", string),
            ("NUMBER", number),
            ("EMBED", embed),
            ("IDENT",  ident),
            ("LONGID", longid),
            ("LEXEME", lexeme)
            ]

      in

         val primitives =
            map
               (fn (ident, f) =>
                   (Symbol.fromValue ident, (fn reserved => P.match (f reserved))))
               builtin

         val reservedNonterminals =
            map (fn (ident, _) => Symbol.fromValue ident) builtin

      end


      (* returns (ps, c) where c expects its second argument to have length |ps| *)
      fun compileRhs table reserved rhs 
         : parser list * (exp * exp list * span -> exp) =
         (case rhs of
             nil => 
                ([],
                 (fn (x, [], _) => x
                   | _ => raise (Fail "precondition")))

           | Terminal sym :: rest =>
                let
                   val (parsers, collate) = compileRhs table reserved rest

                   val p =
                      P.match
                      (fn (S.Llexeme (sym', span)) => 
                             if Symbol.eq (sym, sym') then
                                SOME (unitExp, span)
                             else
                                NONE

                        | (S.Lnumber (_, sym', span)) =>
                             if Symbol.eq (sym, sym') then
                                SOME (unitExp, span)
                             else
                                NONE

                        | _ => NONE)

                   fun collate' (head, exps, span) =
                      (case exps of
                          _ :: exps' => collate (head, exps', span)
                        | nil => raise (Fail "precondition"))
                in
                   (p :: parsers, collate')
                end

           | TerminalIdent sym :: rest =>
                let
                   val (parsers, collate) = compileRhs table reserved rest

                   val p =
                      P.match
                      (fn (S.Lident (sym', span)) => 
                             if Symbol.eq (sym, sym') then
                                SOME (unitExp, span)
                             else
                                NONE
                        | _ => NONE)

                   fun collate' (head, exps, span) =
                      (case exps of
                          _ :: exps' => collate (head, exps', span)
                        | nil => raise (Fail "precondition"))
                in
                   (p :: parsers, collate')
                end

           | Nonterminal (nonterm, prec) :: rest =>
                let
                   val (parsers, collate) = compileRhs table reserved rest

                   val p =
                      (case
                          List.find
                             (fn (sym, p) => Symbol.eq (sym, nonterm))
                             primitives
                       of
                          NONE =>
                             let
                                val (p, _) = lookup table (nonterm, prec)
                             in
                                p
                             end

                        | SOME (_, p) =>
                             (* ignore the precedence *)
                             p reserved)

                   fun collate' (head, exps, span) =
                      (case exps of
                          e :: exps' =>
                             collate (((S.Eapp (head, e)), span), exps', span)

                        | nil => raise (Fail "precondition"))
                in
                   (p :: parsers, collate')
                end)


      fun longidToString longid =
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


      fun compile rules reserved starts =
         let
            val table : entry D.dict ref = ref D.empty

            val () =
               List.app
               (fn ((nonterm, prec), rhs, action) =>
                   let
                      val (_, lr) = lookup table (nonterm, prec)

                      val reservedHere =
                         (case SymbolDict.find reserved nonterm of
                             SOME set => set

                           | NONE => SymbolSet.empty)
                      
                      val (parsers, collate) = compileRhs table reservedHere rhs

                      val p =
                         P.mapAll
                         (fn (l, i, j, input) =>
                             let
                                val span = (getInputPos input i, getInputPos input j)

                                val e =
                                   (* Disregard the definition span.  Use the current one. *)
                                   (S.Eident (action, span), span)
                             in
                                collate (e, l, span)
                             end)
                         (P.seql parsers)
                   in
                      lr := p :: !lr
                   end)
               rules

            (* Do this before backpatching to ensure each start(0) exists. *)
            val pd =
               SymbolSet.foldl
               (fn (sym, pd) =>
                   let
                      val (p, _) = lookup table (sym, 0)
                   in
                      SymbolDict.insert pd sym p
                   end)
               SymbolDict.empty
               starts

            fun backpatch l =
               (case l of
                   nil => ()

                 | ((sym, prec), (_, pr, lr)) :: rest =>
                      let
                         (* Find the parser for the next higher precedence for this symbol,
                            if there are any higher precedences for this symbol.  If there
                            any higher precedences for this symbol, it will appear next in
                            the list, because the list is sorted first by symbol, and second
                            by increasing precedence.
                         *)
                         val rules =
                            (case rest of
                                [] => !lr

                              | ((sym', _), (nextp, _, _)) :: _ =>
                                   if Symbol.eq (sym, sym') then
                                      nextp :: !lr
                                   else
                                      !lr)
                      in
                         pr := P.or rules;
                         backpatch rest
                      end)
         in
            backpatch (D.toList (!table));
            pd
         end

   end
