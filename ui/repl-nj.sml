
local

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
   
         structure Tools =
            struct
   
               val printDepth = Control.Print.printDepth
               val printLength = Control.Print.printLength
               val stringDepth = Control.Print.stringDepth
   
            end
         
      end

   structure ReplStuff = ReplFun (structure Platform = PlatformNJ
                                  structure PostProcess = PostProcessNJ)
   
in

   structure Repl = ReplStuff.Repl
   structure Ctrl = ReplStuff.Ctrl
   structure RecoverRepl = ReplStuff.RecoverRepl
   structure RecoverReplInside = ReplStuff.RecoverReplInside

end

