
signature RENDER =
   sig

      val render : TextIO.outstream -> string list -> Syntax.program -> unit

   end


structure Render :> RENDER =
   struct

      val theStream = ref TextIO.stdOut

      structure Output :> OUTPUT where type t = unit =
         struct

            type t = unit
            fun init () = ()

            fun enter _ = ()
            fun leave () = ()
            fun write str = TextIO.output (!theStream, str)

         end

      structure NarrowOutput = NarrowOutputFun (Output)

      structure CodegenSml = CodegenSmlFun (Output)
      structure CodegenOcaml = CodegenOcamlFun (NarrowOutput)

      fun render s deps prog =
         let
            val (init, writeProgram) =
               (case !Language.target of
                   Language.SML =>
                      (Output.init, CodegenSml.writeProgram)

                 | Language.OCAML =>
                      (NarrowOutput.init, CodegenOcaml.writeProgram))
         in
            theStream := s;
            init ();
            writeProgram deps prog
         end

   end
