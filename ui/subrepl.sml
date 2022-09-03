
signature SUBREPL =
   sig

      (* filename, span, message *)
      type errinfo = string * ((int * int) * (int * int)) * string

      val skipLine : bool ref  (* don't echo the next line *)
      val errorDetected : bool ref
      val errorHandler : (errinfo -> unit) ref

      val process : string -> unit

   end


functor SubReplFun (structure PostProcess : POSTPROCESS) :> SUBREPL =
   struct

      type errinfo = string * ((int * int) * (int * int)) * string

      structure S = Stream
      structure PP = PostProcess

      val skipLine = ref false
      val errorDetected = ref false
      val errorHandler : (errinfo -> unit) ref = ref (fn _ => ())

      val theBuffer : string list ref = ref []  (* invariant: contains no newlines *)

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