
structure PostProcess :> POSTPROCESS =
   struct

      type errinfo = string * ((int * int) * (int * int)) * string

      datatype preclass = PreError | PreWarning | PreBoring | PreNeither

      structure Arg =
         struct

            open Stream

            type symbol = char
            val ord = Char.ord


            type t = preclass

            type self = { classify : char stream -> t }

            type info = { match : char list,
                          len : int,
                          start : char stream,
                          follow : char stream,
                          self : self }

            fun error _ = PreError
            fun warning _ = PreWarning
            fun boring _ = PreBoring
            fun neither _ = PreNeither

         end

      structure Lex =
         LexReplFun (structure Streamable = StreamStreamable
                     structure Arg = Arg)

      structure R =
         RegexpFun (structure Streamable =
                       MonomorphizeStreamable (structure Streamable = StreamStreamable
                                               type elem = char))

      local
         open R
         val digit = set Char.isDigit
         fun plus p = seq [p, star p]
         val number = plus' digit
         val pos = seq [capture number, string ".", capture number]
         val span = seq [pos, string "-", pos]
      in
         val reError = seq [capture (plus' any), string ":", 
                            span,
                            lookahead (alt' [string " Error:", string " Warning:"]),
                            capture (plus' any)]

      end

      datatype class = Error of errinfo | Warning of errinfo | Boring | Neither

      fun s2i str = Option.valOf (Int.fromString str)

      fun errinfo s =
         (case R.match reError s of
             SOME [R.One msg, R.One c2, R.One r2, R.One c1, R.One r1, R.One filename] =>
                let
                   val r1' = s2i r1
                   val r2' = s2i r2
                   
                   (* SML/NJ columns are off by one, except in the first row where they
                      are off by two.
                   *)
                   val c1' = if r1' = 1 then s2i c1 - 2 else s2i c1 - 1
                   val c2' = if r2' = 1 then s2i c2 - 2 else s2i c2 - 1
                in
                   (filename, ((r1', c1'), (r2', c2')), msg)
                end

           | _ =>
                (* The lexer ensures that this must match. *)
                raise (Fail "impossible"))

      fun classify s =
         (case Lex.classify s of
             PreError =>
                Error (errinfo s)

           | PreWarning =>
                Warning (errinfo s)

           | PreBoring => Boring

           | PreNeither => Neither)

   end
