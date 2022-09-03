
structure Token =
   struct

      type symbol = Symbol.symbol
      type span = Span.span

      datatype token =
         UIDENT of symbol * span
       | LIDENT of symbol * span
       | ULIDENT of symbol * span  (* upper case for val purposes, lower for others *)
       | SIDENT of symbol * span
       | USIDENT of symbol * span  (* upper_case symbolic identifier *)
       | TYVAR of symbol * span

       | NUMBER of int * span
       | WORD of int * span
       | STRING of string * span
       | CHAR of char * span

       | LPAREN of span
       | RPAREN of span
       | LBRACKET of span
       | RBRACKET of span
       | LBRACE of span
       | RBRACE of span

       | NUMBER_LBRACE of int * span

       | ARROW of span
       | BAR of span
       | COLON of span
       | COMMA of span
       | DARROW of span
       | DOT of span
       | ELLIPSIS of span
       | EQUAL of span
       | PERIOD of span
       | PERIOD_SEP of span
       | SEAL of span
       | SEMICOLON of span
       | SEMICOLON_SEP of span
       | TIMES of span
       | UNDERSCORE of span

       | AND of span
       | ANDALSO of span
       | AS of span
       | BEGIN of span
       | CASE of span
       | DATATYPE of span
       | DO of span
       | ELSE of span
       | END of span
       | EXTENSION of span
       | FN of span
       | FNC of span
       | FNS of span
       | FUN of span
       | FUNCTOR of span
       | GRAMMARDEF of span
       | GRAMMAROFF of span
       | GRAMMARON of span
       | HANDLE of span
       | IF of span
       | IN of span
       | INCLUDE of span
       | LET of span
       | OF of span
       | OP of span
       | OPEN of span
       | ORELSE of span
       | RAISE of span
       | REF of span
       | SIG of span
       | SIGNATURE of span
       | STRUCT of span
       | STRUCTURE of span
       | THEN of span
       | TRY of span
       | TYPE of span
       | VAL of span
       | WHERE of span
       | WITH of span
       | WITHTYPE of span

       | PRODUCES of span
       | CURRIED of span
       | INFIX of span
       | START of span
       | DEFAULT of span
       | LEFT of span
       | RIGHT of span
       | RESERVED of span
       | RULE of span
       | TUPLED of span

       | ENTER_TERM of span
       | EXIT_TERM of span
       | ENTER_MAIN of span
       | EXIT_MAIN of span

       | TIDENT of symbol * span
       | TNUMBER of int * symbol * span
       | LEXEME of symbol * span
       | LONGTIDENT of symbol list * span

       | EOF of span

       | FULL
       | INCREMENTAL
       | IPC

   end
