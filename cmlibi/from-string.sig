
(* Omits the stuff involving StringCvt. *)

signature FROM_STRING =
   sig

      val toInt : string -> int option
      val toIntM : string -> int option  (* rejects "~" for leading minus *)
      val toWord8 : string -> Word8.word option
      val toWord8Hex : string -> Word8.word option

   end
