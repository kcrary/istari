
open Susp;;
open Nonce_sig;;

module Nonce : NONCE =
   struct

      (* This is sorta dumb, but the OCaml standard library doesn't seem to give access
         to the clock.
      *)

      let n =
         Susp.delay (function () ->
                        let () = Random.self_init ()
                        in
                           Basis.Word32.fromInt (Random.bits ()))

      let nonce () = Susp.force n

   end
