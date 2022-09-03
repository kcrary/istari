
signature LEXER =
   sig

      exception SyntaxError of Token.pos
      val lex : char Stream.stream -> Token.token Stream.stream

   end


structure Lexer :> LEXER =
   struct

      open Token

      val tosym = Symbol.fromValue
      structure Table = HashTable (structure Key = SymbolHashable)
         

      val keywords : (pos -> token) Table.table = Table.table 31

      val () =
         List.app
         (fn (str, token) => Table.insert keywords (tosym str) token)
         [
         ("demote", DEMOTE),
         ("ext", EXT),
         ("fn", FN),
         ("hide", HIDE),
         ("lrule", LRULE),
         ("next", NEXT),
         ("promote", PROMOTE),
         ("rule", RULE),
         ("type", TYPE),
         ("Ki", KI),
         ("Ui", UI)
         ]

      exception SyntaxError of pos

      structure Arg =
         struct

            open Stream

            type symbol = char
            val ord = Char.ord

            type t = pos -> token front
            type u = pos -> char stream * pos

            type self = { lex : symbol stream -> t,
                          comment : symbol stream -> u }

            type info = { match : char list,
                          len : int,
                          start : char stream,
                          follow : char stream,
                          self : self }

            fun action f ({ match, len, follow, self, ...}:info) pos =
               Cons (f (match, len, pos), lazy (fn () => #lex self follow (pos+len)))
            
            fun simple tokfn ({ match, len, follow, self, ...}:info) pos =
               Cons (tokfn pos, lazy (fn () => #lex self follow (pos+len)))

            fun skip ({ len, follow, self, ... }:info) pos =
               #lex self follow (pos+len)
            
            val ident =
               action
               (fn (match, len, pos) =>
                   let
                      val str = String.implode match
                      val sym = tosym str
                   in
                      (case Table.find keywords sym of
                          NONE =>
                             let
                                val ch = String.sub (str, 0)
                             in
                                if Char.isLower ch then
                                   LIDENT (sym, pos)
                                else
                                   UIDENT (sym, pos)
                             end

                        | SOME tokfn => tokfn pos)
                   end)
            
            val pi1 = simple PI1
            val pi2 = simple PI2
            val prev = simple PREV
            val lparen = simple LPAREN
            val rparen = simple RPAREN
            val lbracket = simple LBRACKET
            val rbracket = simple RBRACKET
            val lbrace = simple LBRACE
            val rbrace = simple RBRACE
            val colon = simple COLON
            val comma = simple COMMA
            val dollar = simple DOLLAR
            val dot = simple DOT
            val ellipsis = simple ELLIPSIS
            val equal = simple EQUAL
            val iif = simple IF
            val semicolon = simple SEMICOLON
            val slash = simple SLASH
            val subtype = simple SUBTYPE
            val turnstile = simple TURNSTILE

            fun eof _ pos = Cons (EOF pos, eager Nil)

            fun error _ pos = raise (SyntaxError pos)

            fun enter_comment ({ len, follow, self, ... }:info) pos =
               let
                  val (follow', pos') = #comment self follow (pos + len)
               in
                  #lex self follow' pos'
               end

            fun comment_skip ({ len, follow, self, ...}:info) pos =
               #comment self follow (pos + len)

            fun reenter_comment ({ len, follow, self, ... }:info) pos =
               let
                  val (follow', pos') = #comment self follow (pos + len)
               in
                  #comment self follow' pos'
               end

            fun exit_comment ({ len, follow, ... }:info) pos =
               (follow, pos+len)

            fun comment_error _ pos = raise (SyntaxError pos)

         end
      
      structure LexMain = 
         LexMainFun (structure Streamable = StreamStreamable
                     structure Arg = Arg)

      fun lex s = Stream.lazy (fn () => LexMain.lex s 0)

   end
