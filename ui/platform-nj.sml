
structure PlatformNJ :> PLATFORM =
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

   end
