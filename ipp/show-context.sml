
signature SHOW_CONTEXT =
   sig
      
      type source

      val empty : source
      val filenameToSource : string -> source

      (* position is where the stream begins *)
      val streamToSource : int -> char Stream.stream -> source

      val display : source -> Span.span -> unit

      val maxContext : int ref

   end


structure ShowContext :> SHOW_CONTEXT =
   struct

      fun repeat n f =
         if n <= 0 then
            ()
         else
            (
            f ();
            repeat (n-1) f
            )


      val maxContext = ref 8

      (* row0 is where src begins *)
      fun displayMain row0 src ((row1, col1), (row2, col2)) =
         if !maxContext = 0 then
            ()
         else
            let
               val row1 = row1 - row0 + 1
               val row2 = row2 - row0 + 1

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
               if row1 = row2 then
                  (
                  repeat (row1-1) skipLine;
                  print "| ";
                  copyLine ();
                  print "  ";
                  repeat col1 (fn () => print " ");
                  repeat (Int.max (1, col2-col1)) (fn () => print "^");
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


      (* first row of the source, character generator, cleanup *)
      type source = unit -> (int * (unit -> char option) * (unit -> unit))

      val empty : source = fn () => (1, (fn () => NONE), (fn () => ()))

      fun filenameToSource filename () =
         let
            val ins = TextIO.openIn filename
         in
            (1,
             (fn () => 
                 (TextIO.input1 ins
                  handle IO.Io _ => NONE)),
             (fn () => TextIO.closeIn ins))
         end

      fun streamLoop sr () =
         (case Stream.front (!sr) of
             Stream.Nil => NONE

           | Stream.Cons (ch, s') =>
                (
                sr := s';
                SOME ch
                ))

      fun streamToSource row s () =
         (row, streamLoop (ref s), (fn () => ()))


      fun display source span =
         let
            val (start, src, cleanup) = source ()
         in
            Finally.finally
               (fn () => displayMain start src span)
               cleanup
         end

   end
