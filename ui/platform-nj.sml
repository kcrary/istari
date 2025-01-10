
(* This can't go in the CM project, since it refers to some stuff (e.g., CM) that 
   CM projects don't have access to.
*)

structure Platform :> PLATFORM =
   struct

      val use = use

      fun load basename = CM.make (basename ^ ".cm")

      val oldout = { say = print, flush = (fn () => ()) }

      fun captureOutput f =
         Control.Print.out :=
         { say = f, flush = (fn () => ()) }

      fun resetOutput () =
         Control.Print.out := oldout

      val printDepth = Control.Print.printDepth
      val printLength = Control.Print.printLength
      val stringLength = Control.Print.stringDepth

      val gcMessages = SMLofNJ.Internals.GC.messages

      fun exnHistory exn =
         (case SMLofNJ.exnHistory exn of
             [] => []

           | _ :: l => 
             (* the first entry is always bogus *)
             l)

   end
