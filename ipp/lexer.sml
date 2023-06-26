
signature LEXER =
   sig

      (* puts EOF marker at the end of stream, lexes ;/. as SEMICOLON/PERIOD *)
      val lexFull : char Stream.stream -> Token.token Stream.stream

      (* puts EOF marker at the end of stream, lexes ;/. as SEMICOLON_SEP/PERIOD_SEP *)
      val lexUse : char Stream.stream -> Token.token Stream.stream

      (* as lexUse, but takes the initial position as an argument *)
      val lexRepl : char Stream.stream -> Span.pos -> Token.token Stream.stream

      val lexIpc : char Stream.stream -> Token.token Stream.stream
      val lexProject : char Stream.stream -> (string * Span.span) list

   end


structure Lexer :> LEXER =
   struct

      open Span
      open Token

      structure Table = SymbolHashTable

      fun revappend l1 l2 =
         (case l1 of
             x :: rest =>
                revappend rest (x :: l2)

           | [] => l2)

      fun hexdigit ch =
         let val i = Char.ord ch
         in
            if i <= Char.ord #"9" then
               i - Char.ord #"0"
            else if i <= Char.ord #"F" then
               i - Char.ord #"A" + 10
            else
               i - Char.ord #"a" + 10
         end

      fun hexStringToInt l acc =
         (case l of
             [] => acc

           | ch :: rest =>
                hexStringToInt rest (acc * 16 + IntInf.fromInt (hexdigit ch)))
            

      fun advance pos l =
         (case l of
             nil => pos

           | #"\n" :: rest =>
                advance (addnl pos) rest

           | _ :: rest =>
                advance (add pos 1) rest)


      fun mktok str f =
         let val sym = Symbol.fromValue str
         in
            (fn span => f (sym, span))
         end

      fun smlOnly f (span as (pos, _)) =
         if !Language.smlCompatibility then
            f span
         else
            raise (Error.SyntaxError ("deprecated SML keyword (use --sml flag)", pos))

      fun ifSml f g span =
         if !Language.smlCompatibility then
            f span
         else
            g span

      exception Block
      exception BlockModal

      datatype lex_mode = FULL | USE
      val theLexMode = ref FULL

      val imlKeywordList =
         [
         ("::", mktok "::" USIDENT),
         ("true", mktok "true" ULIDENT),
         ("false", mktok "false" ULIDENT),
         ("nil", mktok "nil" ULIDENT),

         ("->", ARROW),
         ("|", BAR),
         (":", COLON),
         ("=>", DARROW),
         ("...", smlOnly ELLIPSIS),
         (".", (fn span => (case !theLexMode of FULL => PERIOD span | _ => PERIOD_SEP span))),
         ("=", EQUAL),
         (":>", SEAL),
         ("*", TIMES),

         ("and", AND),
         ("andalso", ANDALSO),
         ("as", AS),
         ("begin", BEGIN),
         ("case", CASE),
         ("datatype", DATATYPE),
         ("do", DO),
         ("else", ELSE),
         ("end", END),
         ("exception", EXTENSION),
         ("extension", EXTENSION),
         ("fn", FN),
         ("fnc", FNC),
         ("fns", FNS),
         ("fun", FUN),
         ("functor", FUNCTOR),
         ("grammaroff", GRAMMAROFF),
         ("grammaron", GRAMMARON),
         ("handle", smlOnly HANDLE),
         ("if", IF),
         ("in", IN),
         ("include", INCLUDE),
         ("let", LET),
         ("of", OF),
         ("op", smlOnly OP),
         ("open", OPEN),
         ("orelse", ORELSE),
         ("raise", RAISE),
         ("ref", REF),
         ("sig", SIG),
         ("signature", SIGNATURE),
         ("struct", STRUCT),
         ("structure", STRUCTURE),
         ("then", THEN),
         ("try", TRY),
         ("type", TYPE),
         ("val", VAL),
         ("with", WITH),
         ("where", WHERE),
         ("withtype", smlOnly WITHTYPE)
         ]

      val grammarKeywordList =
         [
         ("::=", PRODUCES),

         ("curried", CURRIED),
         ("infix", INFIX),
         ("start", START),
         ("default", DEFAULT),
         ("left", LEFT),
         ("right", RIGHT),
         ("reserved", RESERVED),
         ("rule", RULE),
         ("tupled", TUPLED)
         ]
         @ 
         imlKeywordList  (* don't use most of these keywords, but they should be reserved anyway *)

      val imlKeywords : (span -> token) Table.table = Table.table 60
      val grammarKeywords : (span -> token) Table.table = Table.table 60

      val () =
         List.app
         (fn (str, token) => Table.insert imlKeywords (Symbol.fromValue str) token)
         imlKeywordList

      val () =
         List.app
         (fn (str, token) => Table.insert grammarKeywords (Symbol.fromValue str) token)
         grammarKeywordList

      (* check for consecutive underscores *)
      fun isLegal str =
         let
            fun loop l =
               (case l of
                   nil => true
                 | ch :: rest =>
                      if ch = #"_" then
                         loop' rest
                      else
                         loop rest)

            and loop' l =
               (case l of
                   nil => true
                 | ch :: rest =>
                      if ch = #"_" then
                         false
                      else
                         loop rest)
         in
            loop (String.explode str)
         end

      (* requires str <> "" *)
      fun identify table str span =
         let
            val sym = Symbol.fromValue str
         in
            (case Table.find table sym of
                NONE =>
                   if isLegal str then
                      let
                         val ch = String.sub (str, 0)
                      in
                         if Char.isLower ch then
                            LIDENT (sym, span)
                         else if Char.isUpper ch then
                            UIDENT (sym, span)
                         else
                            SIDENT (sym, span)
                      end
                   else
                      raise (Error.SyntaxError ("illegal identifier", #1 span))

              | SOME tokfn =>
                   tokfn span)
         end

      fun longIdentify table acc curr currstart pos l =
         (case l of
             [] =>
                (* The lexer ensures that the longid is nonempty, and longIdentify
                   never calls itself recursively with curr=nil, so curr is not nil here.
                *)
                rev (identify table (implode (rev curr)) (currstart, pos) 
                     :: acc)

           | #"." :: rest =>
                let
                   (* The lexer ensures that the longid cannot begin with dot, and the
                      symbol case below deals with any case when there are consecutive dots,
                      so curr can never be nil at this point.
                   *)
                   val acc =
                      DOT (pos, add pos 1)
                      :: identify table (implode (rev curr)) (currstart, pos) 
                      :: acc
                in
                   (case rest of
                       nil =>
                          (* The lexer ensures that the final identifier in a longid is nonempty,
                             so rest cannot be nil here.
                          *)
                          raise (Fail "impossible")

                     | ch :: rest' =>
                          if Char.isAlpha ch then
                             longIdentify table acc [ch] (add pos 1) (add pos 2) rest'
                          else
                             (* The lexer ensures that the remaining characters are all symbols. *)
                             let
                                val str = implode rest
                             in
                                rev (identify table str (add pos 1, add pos (1 + size str))
                                     :: acc)
                             end)
                end

           | ch :: rest =>
                longIdentify table acc (ch :: curr) currstart (add pos 1) rest)
                          

      open Stream
      open Error


      structure Arg =
         struct

            type symbol = char
            val ord = Char.ord

            datatype tlex = LEX of char stream -> t
            withtype t = tlex -> pos -> token front

            type u = pos -> pos -> char stream * pos                            (* current pos, then start of comment *)
            type v = pos -> pos -> char list -> char list * char stream * pos   (* current pos, then start of string *)
            type w = pos -> (string * span) list -> (string * span) list

            type self = { main : char stream -> t,
                          grammar : char stream -> t,
                          term : char stream -> t,
                          comment : char stream -> u,
                          string : char stream -> v,
                          ipc : char stream -> t,
                          project : char stream -> w }

            type info = { match : char list,
                          len : int,
                          start : char stream,
                          follow : char stream,
                          self : self }


            (* General *)
            
            fun action f ({ match, len, follow, ...}:info) (k as LEX cont) pos =
               Cons (f (match, len, pos), lazy (fn () => cont follow k (add pos len)))

            fun simple tokfn ({ match, len, follow, ...}:info) (k as LEX cont) pos =
               Cons (tokfn (pos, add pos len), lazy (fn () => cont follow k (add pos len)))

            fun skip ({ match, follow, ...}:info) (k as LEX cont) pos =
               cont follow k (advance pos match)

            fun switch tokfn (f : self -> char stream -> t) ({ len, follow, self, ...}:info) (LEX _)  pos =
               let val cont = f self
               in
                  Cons (tokfn (pos, add pos len), lazy (fn () => cont follow (LEX cont) (add pos len)))
               end

            fun ident table =
               action
               (fn (match, len, pos) => identify table (implode match) (pos, add pos len))

            fun longid table ({ match, len, follow, self, ...}:info) (k as LEX cont) pos =
               Stream.front
               (Stream.@ (Stream.fromList (longIdentify table [] [] pos pos match),
                          lazy (fn () => cont follow k (add pos len))))

               

            val tyvar =
               action
               (fn (match, len, pos) =>
                   TYVAR (Symbol.fromValue (implode match), (pos, add pos len)))

            val number =
               action
               (fn (match, len, pos) =>
                   (case Int.fromString (implode match) of
                       SOME n => NUMBER (n, (pos, add pos len))

                     | NONE =>
                          raise (SyntaxError ("illegal number", pos))))

            val bignumber =
               action
               (fn (match, len, pos) =>
                   (* the basis is happy to ignore the trailing 'I' *)
                   (case IntInf.fromString (implode match) of
                       SOME n => BIGNUM (n, (pos, add pos len))

                     | NONE =>
                          raise (SyntaxError ("illegal number", pos))))

            val bignumberhex =
               action
               (fn (match, len, pos) =>
                   (* the basis is happy to ignore the trailing 'I' *)
                   let
                      val n = hexStringToInt (List.drop (match, 2)) 0
                   in
                      BIGNUM (n, (pos, add pos len))
                   end)

            val nnumber =
               action
               (fn (match, len, pos) =>
                   (case Int.fromString (implode (List.tl match)) of
                       SOME n => NUMBER (~n, (pos, add pos len))

                     | NONE =>
                          raise (SyntaxError ("illegal number", pos))))

            val numberhex =
               action
               (fn (match, len, pos) =>
                   let
                      val n = IntInf.toInt (hexStringToInt (List.drop (match, 2)) 0)
                   in
                      NUMBER (n, (pos, add pos len))
                   end)

            val wordlit =
               action
               (fn (match, len, pos) =>
                   (case IntInf.fromString (implode (List.drop (match, 2))) of
                       SOME n => WORD (n, (pos, add pos len))

                     | NONE =>
                          raise (SyntaxError ("illegal number", pos))))

            val wordlithex =
               action
               (fn (match, len, pos) =>
                   let
                      val n = hexStringToInt (List.drop (match, 3)) 0
                   in
                      WORD (n, (pos, add pos len))
                   end)

            val number_lbrace =
               action
               (fn (match, len, pos) =>
                   (case Int.fromString (implode (List.take (match, len-2))) of
                       SOME n => NUMBER_LBRACE (n, (pos, add pos len))

                     | NONE =>
                          raise (SyntaxError ("illegal number", pos))))

            fun enter_comment ({ len, follow, self, ... }:info) (k as LEX cont) pos =
               let
                  val (follow', pos') = #comment self follow (add pos len) pos
               in
                  cont follow' k pos'
               end

            fun enter_string ({ len, follow, self, ...}:info) (k as LEX cont) pos =
               let
                  val (chars, follow', pos') = #string self follow (add pos len) pos []
               in
                  Cons (STRING (String.implode (rev chars), (pos, pos')),
                        lazy (fn () => cont follow' k pos'))
               end

            fun enter_char ({ len, follow, self, ...}:info) (k as LEX cont) pos =
               let
                  val (chars, follow', pos') = #string self follow (add pos len) pos []
               in
                  (case chars of
                      [ch] =>
                         Cons (CHAR (ch, (pos, pos')),
                               lazy (fn () => cont follow' k pos'))

                    | _ =>
                         raise (Error.SyntaxError ("illegal character constant", pos)))
               end

            val lparen = simple LPAREN
            val rparen = simple RPAREN
            val lbracket = simple LBRACKET
            val rbracket = simple RBRACKET
            val lbrace = simple LBRACE
            val rbrace = simple RBRACE
            val comma = simple COMMA
            val underscore = simple UNDERSCORE

            val semicolon =
               action
               (fn (_, len, pos) => 
                   (case !theLexMode of
                       FULL =>
                          SEMICOLON (pos, add pos len)

                     | _ =>
                          SEMICOLON_SEP (pos, add pos len)))

            fun eof _ _ pos = Cons (EOF (pos, pos), eager Nil)

            fun error _ _ pos = raise (SyntaxError ("illegal lexeme", pos))


            (* Main mode *)

            val enter_grammar = switch GRAMMARDEF #grammar
            val main_ident = ident imlKeywords
            val main_longid = longid imlKeywords
            val exit_main = switch EXIT_MAIN #term

            fun enter_term (info as { match, len, ... }:info) =
               switch (fn span => ENTER_TERM span) #term info


            (* Grammar mode *)

            (* This is a bit of a hack, but it avoids a lot of extra plumbing.
               Since we only need a mode stack in this one place, and it only needs
               to be one deep, I hate to thread it through everything.
            *)
            val exitGrammarTo : (self -> char stream -> t) ref = ref #main

            val exit_grammar = switch END (fn self => !exitGrammarTo self)

            val grammar_ident = ident grammarKeywords
            val grammar_longid = longid grammarKeywords

            val grammar_string =
               action
               (fn (match, len, pos) =>
                   LEXEME (Symbol.fromValue (String.substring (implode match, 1, len-2)),
                           (pos, add pos len)))

            val grammar_ident_string =
               action
               (fn (match, len, pos) =>
                   TIDENT (Symbol.fromValue (String.substring (implode match, 1, len-2)),
                           (pos, add pos len)))

            fun unclosed_grammar _ _ pos = 
               raise (SyntaxError ("unclosed grammardef", pos))


            (* Term mode *)
               
            val term_ident =
               action
               (fn (match, len, pos) =>
                   let
                      val sym = Symbol.fromValue (implode match)
                   in
                      TIDENT (sym, (pos, add pos len))
                   end)

            val term_longid =
               action
               (fn (match, len, pos) =>
                   (* Longids here are less messy than in main and grammar, so we can just use
                      String.tokens here.
                   *)
                   LONGTIDENT (List.map Symbol.fromValue (String.tokens (fn ch => ch = #".") (implode match)),
                               (pos, add pos len)))

            val term_number =
               action
               (fn (match, len, pos) =>
                   let
                      val str = implode match
                   in
                      (case Int.fromString (implode match) of
                          SOME n => TNUMBER (n, Symbol.fromValue str, (pos, add pos len))
   
                        | NONE =>
                             raise (SyntaxError ("illegal number", pos)))
                   end)

            val term_lexeme =
               action
               (fn (match, len, pos) =>
                   let
                      val sym = Symbol.fromValue (implode match)
                   in
                      LEXEME (sym, (pos, add pos len))
                   end)

            val exit_term = switch EXIT_TERM #main
            val enter_main = switch ENTER_MAIN #main

            fun unclosed_term _ _ pos =
               raise (SyntaxError ("unclosed term", pos))


            (* ipc mode *)

            val ipc_ident = ident grammarKeywords

            fun unbalanced_comment info k pos =
               error info k pos


            (* Comment mode *)

            fun comment_skip ({ match, follow, self, ...}:info) pos start =
               #comment self follow (advance pos match) start

            fun reenter_comment ({ len, follow, self, ... }:info) pos start =
               let
                  val (follow', pos') = #comment self follow (add pos len) start
               in
                  #comment self follow' pos' start
               end

            fun exit_comment ({ len, follow, ... }:info) pos _ =
               (follow, add pos len)

            fun unclosed_comment _ pos start =
               raise (SyntaxError ("unclosed comment", start))

            (* Not sure this can even happen. *)
            fun comment_error _ pos _ = raise (SyntaxError ("illegal character", pos))


            (* String mode *)

            fun string_action f ({ match, len, follow, self, ...}:info) pos start acc =
               #string self follow (add pos len) start (f (match, acc))
               
            val string_elem =
               string_action
               (fn (match, acc) => revappend match acc)

            val string_newline =
               string_action
               (fn (_, acc) => #"\n" :: acc)
               
            val string_backslash =
               string_action
               (fn (_, acc) => #"\\" :: acc)
               
            val string_quote =
               string_action
               (fn (_, acc) => #"\"" :: acc)

            val string_hex2 =
               string_action
               (fn ([_, _, a, b], acc) => Char.chr (hexdigit a * 16 + hexdigit b) :: acc
                 | _ => raise (Fail "impossible by lexer design"))

            val string_hex4 =
               string_action
               (fn ([_, _, a, b, c, d], acc) => 
                      Char.chr 
                         (((hexdigit a * 16 + hexdigit b) * 16 + hexdigit c) * 16 + hexdigit d)
                      :: acc
                 | _ => raise (Fail "impossible by lexer design"))

            fun string_skip ({ match, follow, self, ... }:info) pos start acc =
               #string self follow (advance pos match) start acc

            fun exit_string ({ len, follow, ... }:info) pos _ acc =
               (acc, follow, add pos len)

            fun unclosed_string _ pos start _ =
               raise (SyntaxError ("unclosed string", start))

            fun string_error _ pos _ _ = raise (SyntaxError ("illegal character", pos))

            fun incomplete_string_skip (info as { follow, ...}:info) pos start acc =
               string_error info pos start acc



            (* project *)

            fun project_skip ({ match, follow, self, ...}:info) pos acc =
               #project self follow (advance pos match) acc

            fun project_filename ({ len, follow, self, match, ...}:info) pos acc =
               #project self follow (add pos len) 
                  ((String.implode match, (pos, add pos len)) :: acc)

            fun project_comment ({ len, follow, self, ...}:info) pos acc =
               let
                  val (follow', pos') = #comment self follow (add pos len) pos
               in
                  #project self follow' pos' acc
               end

            fun project_eof _ _ acc = rev acc

            fun project_error _ pos _ =
               raise (SyntaxError ("illegal lexeme", pos))

         end

      structure LexMain =
         LexMainFun
         (structure Streamable = StreamStreamable
          structure Arg = Arg)

      fun doLex f s pos = lazy (fn () => f s (Arg.LEX f) pos)

      fun lexFull s = 
         (
         Arg.exitGrammarTo := #main;
         theLexMode := FULL;
         doLex LexMain.main s origin
         )

      fun lexUse s = 
         (
         Arg.exitGrammarTo := #main;
         theLexMode := USE;
         doLex LexMain.main s origin
         )

      fun lexRepl s pos = 
         (
         Arg.exitGrammarTo := #main;
         theLexMode := USE;
         doLex LexMain.main s pos
         )

      fun lexIpc s =
         (
         Arg.exitGrammarTo := #ipc;
         doLex LexMain.ipc s origin
         )

      fun lexProject s =
         LexMain.project s origin []

   end
