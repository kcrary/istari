
(* Operations provided by the underlying ML platform (e.g., SML/NJ) that the repl requires. *)

signature PLATFORM =
   sig

      (* load the code from the given file name *)
      val use : string -> unit

      (* install a function to process the ML platform's output *)
      val captureOutput : (string -> unit) -> unit

      (* set the output function back to the default *)
      val resetOutput : unit -> unit

      val printDepth : int ref
      val printLength : int ref
      val stringLength : int ref

      (* turn GC messages on/off *)
      val gcMessages : bool -> unit

      (* get the backtrace from an exception *)
      val exnHistory : exn -> string list

   end
