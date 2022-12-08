
structure Token =
   struct

      type pos = int
      type symbol = Symbol.symbol

      datatype token =
         UIDENT of symbol * pos
       | LIDENT of symbol * pos
       | PI1 of pos
       | PI2 of pos
       | PREV of pos
       | LPAREN of pos
       | RPAREN of pos
       | LBRACKET of pos
       | RBRACKET of pos
       | LBRACE of pos
       | RBRACE of pos
       | COLON of pos
       | COMMA of pos
       | DOLLAR of pos
       | DOT of pos
       | ELLIPSIS of pos
       | EQUAL of pos
       | IF of pos
       | SEMICOLON of pos
       | SLASH of pos
       | TURNSTILE of pos
       | AXIOM of pos
       | DEMOTE of pos
       | EXT of pos
       | FN of pos
       | HIDE of pos
       | LRULE of pos
       | NEXT of pos
       | PROMOTE of pos
       | RULE of pos
       | SUBTYPE of pos
       | TYPE of pos
       | KI of pos
       | UI of pos
       | EOF of pos

   end
