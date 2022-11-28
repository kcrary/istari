
signature VALUE =
   sig

      val value : Syntax.exp -> bool

   end


structure Value :> VALUE =
   struct

      open Syntax

      fun value (exp_, _) =
         (case exp_ of
             Eunit => true
           | Eident _ => true
           | Econstr _ => true
           | Enumber _ => true
           | Eword _ => true
           | Estring _ => true
           | Echar _ => true
             
           | Etuple l => List.all value l

           | Elist l => List.all value l

           | Eapp ((Econstr _, _), e) => value e

           | Eapprecord (_, l) => List.all (fn (_, e) => value e) l

           | Elam _ => true

           | Elams (_ :: _, _, _) => true

           | Eannot (e, _) => value e

           | _ => false)

   end