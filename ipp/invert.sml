
signature INVERT =
   sig

      type inspan
      val invert : string list -> Syntax.program -> inspan -> Span.span

   end


signature POS =
   sig

      type t

      val zero : t
      val advance : string -> t -> t
      val compare : t * t -> order

   end


functor InvertFun (structure Pos : POS)
   :> INVERT where type inspan = Pos.t * Pos.t
   =
   struct

      exception Answer of Span.span

      type inspan = Pos.t * Pos.t

      structure InvertOutput :> OUTPUT where type t = Span.span * inspan =
         struct

            (* Run a coroutine concurrently with the code generator. *)
      
            datatype message = ENTER of Span.span | LEAVE | WRITE of string
            datatype state = Yield of message -> state
      
            (* find the right endpoint, having already found the left *)
            fun lookRight right stack extra pos msg =
               (case msg of
                   ENTER _ =>
                      Yield (lookRight right stack (extra+1) pos)
      
                 | LEAVE =>
                      if extra > 0 then
                         Yield (lookRight right stack (extra-1) pos)
                      else
                         (case stack of
                             nil =>
                                raise (Fail "misbalanced enter/leave in code generation")
      
                           | _ :: stack' =>
                                Yield (lookRight right stack' 0 pos))
      
                 | WRITE str =>
                      let
                         val pos' = Pos.advance str pos
                      in
                         (case Pos.compare (pos', right) of
                             LESS =>
                                Yield (lookRight right stack extra pos')

                           | _ =>
                                (* found the right side *)
                                (case stack of
                                    nil =>
                                       raise (Fail "misbalanced enter/leave in code generation")
          
                                  | span :: _ =>
                                       raise (Answer span)))
                      end)
      
            (* find the left endpoint *)
            fun lookLeft left right stack pos msg =
               (case msg of
                   ENTER span =>
                      Yield (lookLeft left right (span :: stack) pos)
      
                 | LEAVE =>
                      (case stack of
                          nil =>
                             raise (Fail "misbalanced enter/leave in code generation")
      
                        | _ :: stack' =>
                             Yield (lookLeft left right stack' pos))
      
                 | WRITE str =>
                      let
                         val pos' = Pos.advance str pos
                      in
                         (case Pos.compare (pos', left) of
                             GREATER =>
                                (* found the left side *)
                                Yield (lookRight right stack 0 pos')

                           | _ =>
                                Yield (lookLeft left right stack pos'))
                      end)
      
            val theState = ref (Yield (fn _ => raise (Fail "uninitialized inverter")))
      
            type t = Span.span * inspan
      
            fun init (fullspan, (targetleft, targetright)) =
               theState := Yield (lookLeft targetleft targetright [fullspan] Pos.zero)
      
            fun send msg =
               let val Yield f = !theState
               in
                  theState := f msg
               end
      
            fun enter span = send (ENTER span)
            fun leave () = send LEAVE
            fun write str = send (WRITE str)
      
         end

      structure NarrowInvertOutput = NarrowOutputFun (InvertOutput)

      structure CodegenSml = CodegenSmlFun (InvertOutput)
      structure CodegenOcaml = CodegenOcamlFun (NarrowInvertOutput)

      fun invert deps (program as (_, fullspan)) targetspan =
         (let
             val (init, writeProgram) =
                (case !Language.target of
                    Language.SML =>
                       (InvertOutput.init, CodegenSml.writeProgram)
 
                  | Language.OCAML =>
                       (NarrowInvertOutput.init, CodegenOcaml.writeProgram))
          in
             init (fullspan, targetspan);
             
             writeProgram deps program;
   
             (* If we get here, the span to invert is not within the generated code. *)
             raise Error.NotFound
          end
          handle Answer sp => sp)

   end


structure IntPos :> POS where type t = int  =
   struct

      type t = int
      val zero = 0
      fun advance str n = n + String.size str
      val compare = Int.compare

   end


structure RCPos :> POS where type t = int * int  =
   struct

      type t = int * int

      val zero = (1, 0)

      fun advance str (r, c) =
         let
            val len = String.size str
         
            fun loop r c i =
               if i = len then
                  (r, c)
               else if String.sub (str, i) = #"\n" then
                  loop (r+1) 0 (i+1)
               else
                  loop r (c+1) (i+1)
         in
            loop r c 0
         end

      fun compare ((r, c), (r', c')) =
         (case Int.compare (r, r') of
             EQUAL => Int.compare (c, c')
           | order => order)

   end


structure Invert = InvertFun (structure Pos = IntPos)
structure InvertRC = InvertFun (structure Pos = RCPos)
