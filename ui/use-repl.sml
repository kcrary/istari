CM.make "sources.cm";
use "platform-nj.sml";
CM.make "../ipp/basis/basis.cm";

local

   structure ReplStuff =
      ReplFun (structure Platform = Platform
               structure UI = NullUI
               structure PostProcess = PostProcess
               structure Memory = NullMemory
               structure Buffer = SimpleBuffer)
               
in

   structure Repl = ReplStuff.Repl
   structure Ctrl = ReplStuff.Ctrl
   structure RecoverRepl = ReplStuff.RecoverRepl
   structure RecoverReplInside = ReplStuff.RecoverReplInside

end;
