
(* For parsing IPC *)

structure PreContext =
   struct

      type identifier = Syntax.identifier

      datatype item =
         VAL of identifier * int
       | TYPE of identifier
       | SIG of identifier * class
       | MOD of identifier * class
       | FUN of identifier * class

      and class =
         LIST of precontext
       | NAME of identifier

      withtype precontext = item list

   end