
signature ERROR =
   sig

      datatype place = POS of Span.pos | SPAN of Span.span | UNKNOWN

      val placeToString : string -> place -> string
      val isUnknown : place -> bool
      
      exception Error of string * place
      exception NotFound

      val SyntaxError : string * Span.pos -> exn
      val SemanticError : string * Span.span -> exn
      val GeneralError : string -> exn

      val warning : string * place -> unit

   end


structure Error :> ERROR =
   struct

      datatype place = POS of Span.pos | SPAN of Span.span | UNKNOWN

      fun posToString (row, col) =
         String.concat [Int.toString row, ".", Int.toString col]

      fun placeToString prefix place =
         (case place of
             POS pos => prefix ^ posToString pos

           | SPAN (l, r) => String.concat [prefix, posToString l, "-", posToString r]

           | UNKNOWN => "")

      fun isUnknown place =
         (case place of
             UNKNOWN => true
           | _ => false)


      exception Error of string * place
      exception NotFound

      fun SyntaxError (str, pos) = Error (str, POS pos)
      fun SemanticError (str, span) = Error (str, SPAN span)
      fun GeneralError str = Error (str, UNKNOWN)

      fun warning (str, place) =
         (
         print "Warning: ";
         print str;
         print (placeToString " at " place);
         print "\n"
         )

   end
