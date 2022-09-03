
structure PrecedenceTable =
   struct

      datatype assoc = LEFT | RIGHT
      datatype mode = CURRIED | TUPLED
      type precedence = int * assoc * mode
      type table = precedence SymbolHashTable.table

   end


signature PRECEDENCE =
   sig

      type t

      val parse : PrecedenceTable.table -> t Syntax.juxta list -> Span.span -> t

   end


signature PRECEDENCE_ARG =
   sig

      type t_
      type t = t_ * Span.span

      val apply : t -> t -> t
      val applyCurriedInfix : t -> t -> t -> t  (* infix operator first *)
      val applyTupledInfix : t -> t -> t -> t   (* infix operator first *)

   end


functor PrecedenceFun (structure Arg : PRECEDENCE_ARG) 
   :> PRECEDENCE 
      where type t = Arg.t 
   =
   struct
      open PrecedenceTable
      open Arg

      structure Table = SymbolHashTable

      type symbol = Symbol.symbol
      type pos = Span.pos
      type span = Span.span

      datatype elem =
         Oper of t * int * assoc * mode * span
       | Arg of t



      fun resolve table jux =
         (case jux of
             Syntax.Jident ((sym, span), e) =>
                (case Table.find table sym of
                    NONE => Arg e

                  | SOME (prec, assoc, mode) => Oper (e, prec, assoc, mode, span))

           | Syntax.Jatom e => Arg e)


      fun applyInfix oper mode item1 item2 =
         (case mode of
             CURRIED => applyCurriedInfix oper item1 item2
           | TUPLED => applyTupledInfix oper item1 item2)
       

      fun tighter prec prec' assoc assoc' pos =
         (case Int.compare (prec, prec') of
             GREATER => true

           | LESS => false

           | EQUAL =>
                (case (assoc, assoc') of
                    (LEFT, LEFT) => false
                  | (RIGHT, RIGHT) => true
                  | _ =>
                       raise (Error.SyntaxError ("adjacent equal-precedence infix operators have opposite associativity", pos))))


      (* A well-formed stack is a nonempty list, with alternating Oper and Arg elements,
         and with the last element an Arg. *)

      (* stack is well-formed and its first element is an Arg, returns same way *)
      fun flushStack prec assoc stack pos =
         (case stack of
             [Arg _] => stack

           | Arg item1 :: Oper (oper, prec', assoc', mode, span) :: Arg item2 :: tail =>
                if
                   tighter prec prec' assoc assoc' pos
                then
                   stack
                else
                   let
                      val stack' =
                         Arg (applyInfix oper mode item2 item1) :: tail
                   in
                      flushStack prec assoc stack' pos
                   end

           | _ => raise (Fail "precondition"))


      (* stack is well-formed *)
      fun parseLoop table stack l =
         (case l of
             [] =>
                stack

           | (jux, _) :: rest =>
                let
                   val elem = resolve table jux
                in
                   (case elem of
                       Oper (_, prec, assoc, _, span) =>
                          (case stack of
                              [] => raise (Fail "ill-formed stack")
   
                            | Oper _ :: _ =>
                                 raise (Error.SyntaxError ("misplaced infix operator", #1 span))
   
                            | Arg _ :: _ =>
                                 let
                                    val stack' = flushStack prec assoc stack (#1 span)
                                 in
                                    parseLoop table (elem :: stack') rest
                                 end)

                     | Arg item =>
                          (case stack of
                              [] => raise (Fail "ill-formed stack")

                            | Arg item' :: tail =>
                                 parseLoop table (Arg (apply item' item) :: tail) rest

                            | Oper _ :: _ =>
                                 parseLoop table (Arg item :: stack) rest))
                end)


      fun parse table l (fullspan : Span.span) =
         (case l of
             [] => raise (Fail "excluded syntactically")

           (* solitary operator, don't treat as infix *)
           | [(jux as Syntax.Jident ((sym, _), e), _)] => e

           (* optimization *)
           | [(Syntax.Jatom item, _)] => item

           | (first, _) :: rest =>
                (case resolve table first of
                    Oper (_, _, _, _, span) =>
                       raise (Error.SyntaxError ("misplaced infix operator", #1 span))

                  | arg as (Arg _) =>
                       let
                          val stack = parseLoop table [arg] rest
                       in
                          (case stack of
                              Oper _ :: _ =>
                                 raise (Error.SyntaxError ("missing infix argument", #2 fullspan))

                            | [] =>
                                 raise (Fail "ill-formed stack")

                            | Arg _ :: _ =>
                                 let
                                    val stack' = flushStack ~1 LEFT stack (#2 fullspan)

                                    (* Since stack' is well-formed, begins with an Arg,
                                       and was just flushed with ~1 precedence, it must consist
                                       of exactly one Arg. *)
                                 in
                                    (case stack' of
                                        [Arg item] => item

                                      | _ => raise (Fail "impossible"))
                                 end)
                       end))

   end


structure ExpPrecedence =
   PrecedenceFun
   (structure Arg =
       struct
          open Syntax
          open Span

          type t_ = exp_
          type t = exp

          fun apply e1 e2 =
             (Eapp (e1, e2), join (#2 e1) (#2 e2))

          fun applyCurriedInfix oper e1 e2 =
             let
                val span = join (#2 e1) (#2 e2)
             in
                (Eapp
                    ((Eapp (oper, e1),
                      span),
                     e2),
                 span)
             end

          fun applyTupledInfix oper e1 e2 =
             let
                val span = join (#2 e1) (#2 e2)
             in
                (Eapp
                    (oper,
                     (Etuple [e1, e2], span)),
                 span)
             end
          
       end)


structure PatPrecedence =
   PrecedenceFun
   (structure Arg =
       struct
          open Syntax
          open Span

          type t_ = pat_
          type t = pat

          val refsym = Symbol.fromValue "ref"

          fun isref ([x], _) = Symbol.eq (x, refsym)
            | isref _ = false

          fun apply (p1 : pat) p2 =
             (case p1 of
                 (Pconstr id, sp1) =>
                    if isref id then
                       (Pref p2, join sp1 (#2 p2))
                    else
                       (Papp (id, p2), join sp1 (#2 p2))

               | (_, span) =>
                    raise (Error.SemanticError ("pattern operator is not a constructor", span)))

          fun applyCurriedInfix (oper as (_, (operspanl, _))) e1 e2 =
             raise (Error.SyntaxError ("infix pattern operator is curried", operspanl))

          fun applyTupledInfix oper e1 e2 =
             (case oper of
                 (Pconstr id, _) =>
                    let
                       val span = join (#2 e1) (#2 e2)
                    in
                       (Papp (id,
                              (Ptuple [e1, e2], span)),
                        span)
                    end

               | _ =>
                    (* We never make a Jident [pat] with anything but Pconstr. *)
                    raise (Fail "impossible"))
          
       end)
