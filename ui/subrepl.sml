
signature SUBREPL =
   sig

      (* set this to true to make the subrepl not echo the next line *)
      val skipLine : bool ref  

      (* call this to process a line of output from the ML repl *)
      val process : string -> unit

      (* the subrepl sets this to true when an error occurs *)
      val errorDetected : bool ref



      (* filename, span, message *)
      type errinfo = string * ((int * int) * (int * int)) * string

      (* callback for error handling *)
      val errorHandler : (errinfo -> unit) ref

   end


functor SubReplFun (structure PostProcess : POSTPROCESS) :> SUBREPL =
   struct

      type errinfo = string * ((int * int) * (int * int)) * string

      structure S = Stream
      structure PP = PostProcess

      val skipLine = ref false
      val errorDetected = ref false
      val errorHandler : (errinfo -> unit) ref = ref (fn _ => ())

      (* carried over output text
         invariant: contains no newlines
      *)
      val theBuffer : string list ref = ref []

      fun processLine s =
         (case PP.classify s of
             PP.Error err =>
                (
                errorDetected := true;
                !errorHandler err
                )

           | PP.Warning err =>
                !errorHandler err

           | PP.Boring =>
                ()

           | PP.Neither =>
                (
                S.app (fn ch => TextIO.output1 (TextIO.stdOut, ch)) s;
                print "\n"
                ))


      (* strs is not [] and contains no newlines *)
      fun processLoop strs =
         (case strs of
             [] => raise (Fail "precondition")

           | [str] =>
                theBuffer := [str]

           | str :: rest =>
                (
                processLine (S.fromString str);
                processLoop rest
                ))


      fun process str =
         (case String.fields (fn ch => ch = #"\n") str of
             [] => raise (Fail "impossible")

           | [_] =>
                (* stuff after the last newline *)
                theBuffer := str :: !theBuffer

           | first :: rest =>
                if !skipLine then
                   (
                   skipLine := false;
                   theBuffer := [];
                   processLoop rest
                   )
                else
                   let
                      val s =
                         foldl
                         (fn (str, s) => S.@ (S.fromString str, s))
                         (S.eager S.Nil) 
                         (first :: !theBuffer)
                   in
                      theBuffer := [];
                      processLine s;
                      processLoop rest
                   end)

   end