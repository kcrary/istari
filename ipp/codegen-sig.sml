
signature CODEGEN =
   sig

      val writeProgram : string list -> Syntax.program -> unit

   end


signature OUTPUT =
   sig

      type t
      val init : t -> unit

      val enter : Span.span -> unit
      val leave : unit -> unit
      val write : string -> unit

   end
