
signature TACTICGEN =
   sig

      val gen : TextIO.outstream -> Rule.clause list -> unit

   end


structure Tacticgen :> TACTICGEN =
   struct

      open Rule

      fun solebind l i =
         (case l of
             nil => NONE

           | h :: t =>
                if h = 0 then
                   solebind t (i+1)
                else if List.all (fn n => n = 0) t then
                   SOME (i, h)
                else
                   NONE)


      fun gen outs rules =
         let
            fun write str = TextIO.output (outs, str)

            val rules' =
               map
               (fn rule => (rule, Check.check rule))
               rules
         in
            List.app
               (fn (Rule (name, _)) =>
                   (
                   write "      val ";
                   write (Symbol.toValue name);
                   write " : tactic\n"
                   )

                 | _ => ())
               rules;

            write "\n";

            List.app
               (fn (Rule (name, (premises, _, _)), (oset, _)) =>
                      let
                         val hs =
                            map (fn (_, hyps, _, _) => length hyps) premises
                      in
                         write "      val ";
                         write (Symbol.toValue name);
                         write " = ";

                         if List.all (fn n => n = 0) hs then
                            ()
                         else
                            (case solebind hs 0 of
                                SOME (i, 1) =>
                                   (
                                   write "andthenBindOn ";
                                   write (Int.toString i);
                                   write " $ "
                                   )

                              | SOME (i, n) =>
                                   (
                                   write "andthenBindsOn ";
                                   write (Int.toString n);
                                   write " ";
                                   write (Int.toString i);
                                   write " $ "
                                   )

                              | NONE =>
                                   (
                                   write "andthenBinds [";
                                   app 
                                      (fn n =>
                                          (
                                          write (Int.toString n);
                                          write ","
                                          ))
                                      hs;
                                   write "] $ "
                                   ));

                         write "refine";
                         write (Int.toString (length oset));
                         write " Rule.";
                         write (Symbol.toValue name);
                         write "\n"
                      end

                 | _ => ())
               rules'
         end

   end