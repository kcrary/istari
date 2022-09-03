
signature HARDCODE =
   sig
      val apply : Syntax.exp -> Syntax.directive
      val enter : Span.span -> Syntax.directive
      val leave : Span.span -> Syntax.directive
      val entern : int -> Span.span -> Syntax.directive
   end


structure Hardcode :> HARDCODE =
   struct

      open Syntax

      val applySyms = map Symbol.fromValue ["Prover", "apply"]
      val enterSyms = map Symbol.fromValue ["Prover", "enter"]
      val leaveSyms = map Symbol.fromValue ["Prover", "leave"]
      val enternSyms = map Symbol.fromValue ["Prover", "entern"]

      fun apply (e as (_, (span as (l, _)))) =
         let
            val span' = (l, l)
         in
            (Vexp (Eapp ((Eident (applySyms, span'), span'), e),
                   span),
             span)
         end

      fun enter span =
         (Vexp (Eapp ((Eident (enterSyms, span), span),
                      (Eunit, span)),
                span),
          span)
            
      fun entern i span =
         (Vexp (Eapp ((Eident (enternSyms, span), span),
                      (Enumber i, span)),
                span),
          span)
            
      fun leave span =
         (Vexp (Eapp ((Eident (leaveSyms, span), span),
                      (Eunit, span)),
                span),
          span)

   end
