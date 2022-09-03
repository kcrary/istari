
signature ROWCOL =
   sig
      
      type source

      val empty : source
      val filenameToSource : string -> source
      val stringsToSource : string list -> source

      val fromSpan : source -> Span.span -> (int * int) * (int * int)
      val display : source -> (int * int) * (int * int) -> unit

      val maxContext : int ref

   end


structure RowCol :> ROWCOL =
   struct

      (* These NotFound errors shouldn't happen unless someone is modifying the file as we use it. *)

      fun fromSpanMain src (left, right) =
         let
            fun scan n row col =
               if n = 0 then
                  (row, col)
               else
                  (case src () of
                      NONE => raise Error.NotFound
   
                    | SOME ch =>
                         if ch = #"\n" then
                            scan (n-1) (row+1) 0
                         else
                            scan (n-1) row (col+1))

            (* The row should not start from one, but it is, alas, standard. *)
            val (row1, col1) = scan left 1 0

            (* We shouldn't have right < left, but easiest just to handle it. *)
            val (row2, col2) = scan (Int.max (right-left, 0)) row1 col1
         in
            ((row1, col1), (row2, col2))
         end

         
      fun repeat n f =
         if n <= 0 then
            ()
         else
            (
            f ();
            repeat (n-1) f
            )


      val maxContext = ref 8

      fun displayMain src ((row1, col1), (row2, col2)) =
         if !maxContext = 0 then
            ()
         else
            let
               val max = !maxContext
            
               fun skipLine () =
                  (case src () of
                      NONE => raise Error.NotFound
   
                    | SOME ch =>
                         if ch = #"\n" then
                            ()
                         else
                            skipLine ())

               fun skipChar () =
                  (case src () of
                      NONE => raise Error.NotFound

                    | SOME _ => ())

               fun copyLine () =
                  (case src () of
                      NONE => raise Error.NotFound

                    | SOME ch =>
                         if ch = #"\n" then
                            print "\n"
                         else
                            (
                            print (String.str ch);
                            copyLine ()
                            ))

               fun copyChar () =
                  (case src () of
                      NONE => raise Error.NotFound

                    | SOME ch => print (String.str ch))
            in
               print "\n";
            
               if row1 = row2 then
                  (
                  repeat (row1-1) skipLine;
                  print "| ";
                  copyLine ();
                  repeat col1 (fn () => print " ");
                  print "  ";
                  repeat (col2-col1) (fn () => print "^");
                  print "\n"
                  )
               else
                  (
                  repeat (row1-1) skipLine;
                  repeat col1 skipChar;
                  print "| ";
                  repeat col1 (fn () => print " ");
                  copyLine ();
                  
                  if row2-row1+1 <= max then
                     repeat (row2-row1-1) (fn () => (print "| "; copyLine ()))
                  else
                     let
                        (* if max = 1, print two lines anyway *)
                        val rest = Int.max (max - 2, 0)
                        val b = rest div 2 + rest mod 2
                        val a = rest div 2
                     in
                        repeat b (fn () => (print "| "; copyLine ()));
                        repeat (row2 - row1 - 1 - b - a) skipLine;
                        print "...\n";
                        repeat a (fn () => (print "| "; copyLine ()))
                     end;

                  print "| ";
                  repeat col2 copyChar;
                  print "\n"
                  )
            end handle Error.NotFound => print "\n"


      (* character generator, cleanup *)
      type source = unit -> ((unit -> char option) * (unit -> unit))

      val empty : source = fn () => ((fn () => NONE), (fn () => ()))

      fun filenameToSource filename () =
         let
            val ins = TextIO.openIn filename
         in
            ((fn () => 
                 (TextIO.input1 ins
                  handle IO.Io _ => NONE)),
             (fn () => TextIO.closeIn ins))
         end

      fun dropEmpty l =
         (case l of
             [] => []

           | str :: rest =>
                if str = "" then
                   dropEmpty rest
                else
                   l)

      fun stringsToFun strs =
         let
            val first = ref ""
            val rest = ref strs
            val i = ref 0
         in
            fn () =>
               (let
                   val ch = String.sub (!first, !i)
                in
                   i := !i + 1;
                   SOME ch
                end
                handle Subscript =>
                   (case dropEmpty (!rest) of
                       [] => NONE

                     | h' :: t' =>
                          (
                          first := h';
                          rest := t';
                          i := 1;
                          SOME (String.sub (h', 0))
                          )))
         end

      fun stringsToSource strs () =
         (stringsToFun strs, (fn () => ()))

      fun usingSource source f =
         let
            val (src, cleanup) = source ()
         in
            Finally.finally
               (fn () => f src)
               cleanup
         end

      fun fromSpan source span =
         usingSource source (fn src => fromSpanMain src span)

      fun display source span =
         usingSource source (fn src => displayMain src span)

   end
