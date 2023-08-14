
(* Combinators for a Frost-Hafiz Parser *)

signature FH_PARSE =
   sig

      type elem
      type 'a parser

      val return    : 'a -> 'a parser
      val fail      : 'a parser
      val or        : 'a parser list -> 'a parser
      val seqp      : 'a parser -> 'b parser -> ('a * 'b) parser
      val seql      : 'a parser list -> 'a list parser
      val match     : (elem -> 'a option) -> 'a parser

      val map       : ('a -> 'b) -> 'a parser -> 'b parser
      val mapSpan   : ('a * int * int -> 'b) -> 'a parser -> 'b parser
      val mapAll    : ('a * int * int * elem Vector.vector -> 'b) -> 'a parser -> 'b parser

      val anchor    : 'a parser Susp.susp -> 'a parser

      val parse     : 'a parser -> elem list -> ('a, int) Sum.sum

   end


(* The recognizer works basically as Frost & Hafiz suggest, but we build parse
   trees a little differently.

   They suggest replacing the sets with dictionaries, so instead of a recognizer
   returning only the set of locations at which a parse could end, each ending
   location is paired with a parse tree corresponding to a parse ending at that
   location.  To use dictionaries this way makes the code much messier, and I fear
   it will take an enormous amount of space to store many parse trees that will
   not be used.  (I considered using suspensions, but it seems that a suspension
   would take at least as much space as the parse tree.  Parse trees are pretty
   compact for the information they carry.)

   Instead, after the recognizer runs and determines there is a parse, we run a
   second pass that obtains the parse tree.  The second pass does backtrack,
   but it should still be reasonably fast because it has access to the memo
   tables, so it will only backtrack at a single level of the parse.

   To avoid a big space leak, we conclude by running a cleanup pass that frees
   all the memo and curtailment tables.

   We do not support *indirect* left recursion.
*)

functor FHParseFun (type elem) 
   :> FH_PARSE where type elem = elem 
   =
   struct

      type elem = elem

      structure S = SplaySet (structure Elem = IntOrdered)

      type 'a parser =
         (elem Vector.vector -> int -> S.set)             (* recognize *)
         * (elem Vector.vector -> int -> int -> 'a)       (* return parse tree *)
         * (unit -> unit)                                 (* cleanup *)


      exception NoMatch

      fun noop () = ()


      fun return x =
         let
            fun r _ i = S.singleton i

            fun p _ (i : int) j = if i = j then x else raise NoMatch
         in
            (r, p, noop)
         end


      val fail =
         ((fn _ => fn _ => S.empty),
          (fn _ => fn _ => fn _ => raise NoMatch),
          noop)


      fun or l =
         let
            fun r input i =
               foldl
               (fn ((r1, _, _), s) => S.union s (r1 input i))
               S.empty
               l

            fun ploop input i j l =
               (case l of
                   nil => raise NoMatch

                 | (_, p1, _) :: rest =>
                      (p1 input i j
                       handle NoMatch => ploop input i j rest))

            fun p input i j = ploop input i j l

            fun c () =
               app (fn (_, _, c1) => c1 ()) l
         in
            (r, p, c)
         end


      (* Finds the last element x in the set such that f(x) does not raise an
         exception, and returns the value of f(x).

         We want the last one, because that will give us parse trees that favor
         earlier nonterminals consuming as much input as possible.  That is, it
         favors left-associative parses.  We want it to work that way for
         left-associative operators, because a shorter-than-maximal parse of the
         left-hand operand will just have to be backed out.  We actually also want
         it for right-associative operators, because then the left-hand operand
         is at a higher precedence anyway; we want to get as much of it as possible
         before turning to the lower precedence operator.

         The implementation is clunky, but it's the best we can do without extending
         the set interface.
      *)
      fun find (f : int -> 'a) s =
         let
            exception Succ of 'a
         in
            (* foldr gives us the last success *)
            (S.foldr
                (fn (x, ()) => ((raise (Succ (f x)))
                                handle NoMatch => ())) () s ;
             raise NoMatch)
            handle (Succ y) => y
         end
                

      fun seqp (r1, p1, c1) (r2, p2, c2) =
         let
            fun r input i =
               let
                  val s1 = r1 input i
               in
                  S.foldl
                  (fn (j, s) => S.union (r2 input j) s)
                  S.empty
                  s1
               end

            fun p input i j =
               let
                  val s1 = r1 input i

                  val k =
                     find
                     (fn k => if S.member (r2 input k) j then k else raise NoMatch)
                     s1
               in
                  (p1 input i k, p2 input k j)
               end

            fun c () = (c1 (); c2 ())
         in
            (r, p, c)
         end


      fun seql l =
         let
            fun rloop input i l =
               (case l of
                   [] => S.singleton i

                 (* optimize *)
                 | [(r1, _, _)] => r1 input i

                 | (r1, _, _) :: rest =>
                      let
                         val s1 = r1 input i
                      in
                         S.foldl
                         (fn (j, s) => S.union (rloop input j rest) s)
                         S.empty
                         s1
                      end)
                      
            fun r input i = rloop input i l

            fun findpath input i j l =
               (case l of
                   [] =>
                      if i = j then 
                         []
                      else
                         raise NoMatch

                 | (r1, _, _) :: rest =>
                      let
                         val s1 = r1 input i
                      in
                         find
                         (fn k => k :: findpath input k j rest)
                         s1
                      end)

            fun ploop input i ks l =
               (case (ks, l) of
                   ([], []) => []

                 | (k :: krest, (_, p1, _) :: lrest) =>
                      p1 input i k :: ploop input k krest lrest

                 | _ =>
                      (* length ks = length l *)
                      raise (Fail "impossible"))

            fun p input i j =
               let
                  val ks = findpath input i j l
               in
                  ploop input i ks l
               end

            fun c () =
               app (fn (_, _, c1) => c1 ()) l
         in
            (r, p, c)
         end


      (* Furthest we've made it into the input.  Provides a guess at the location of 
         syntax errors.

         It might be better to thread this through, rather than be a global, but it
         will be a reference in any case.
      *)
      val furthest = ref 0

      fun match f =
         let
            fun r input i =
               (
               furthest := Int.max (i, !furthest);

               (case f (Vector.sub (input, i)) of
                   NONE => S.empty
                 | SOME _ => S.singleton (i+1))
               handle Subscript => S.empty
               )

            fun p input i j =
               if i+1 = j then
                  let
                     val x = 
                        Vector.sub (input, i)
                        handle Subscript => raise NoMatch
                  in
                     (case f x of
                         SOME y => y
                       | NONE => raise NoMatch)
                  end
               else
                  raise NoMatch
         in
            (r, p, noop)
         end
 
         
      fun map f (r1, p1, c1) =
         let
            fun p input i j = f (p1 input i j)
         in
            (r1, p, c1)
         end


      fun mapSpan f (r1, p1, c1) =
         let
            fun p input i j = f (p1 input i j, i, j)
         in
            (r1, p, c1)
         end

         
      fun mapAll f (r1, p1, c1) =
         let
            fun p input i j = f (p1 input i j, i, j, input)
         in
            (r1, p, c1)
         end

         
      fun anchor susp =
         let
            val memo : S.set option ArrayInf.array = ArrayInf.array NONE
            val curtail = ArrayInf.array 0

            fun r input i =
               (case ArrayInf.sub (memo, i) of
                   SOME s => s

                 | NONE =>
                      let
                         val depth = ArrayInf.sub (curtail, i)
                      in
                         if i + depth > Vector.length input then
                            (* curtail this branch *)
                            S.empty
                         else
                            let
                               val (r1, _, _) = Susp.force susp
                               val () = ArrayInf.update (curtail, i, depth+1)
                               val s = r1 input i
                            in
                               ArrayInf.update (memo, i, SOME s);
                               s
                            end
                      end)

            fun p input i j =
               let
                  val (_, p1, _) = Susp.force susp
               in
                  p1 input i j
               end

            fun c () =
               (* If curtail is empty, this nonterminal was never reached or has already
                  been cleaned up.  Consequently, everything below it also was never
                  reached (by this path) or has already been (or is already being)
                  cleaned up, so there is no need to recurse.
               *)
               if ArrayInf.isEmpty curtail then
                  ()
               else
                  let
                     val (_, _, c1) = Susp.force susp
                  in
                     ArrayInf.erase memo;
                     ArrayInf.erase curtail;
                     c1 ()
                  end
         in
            (r, p, c)
         end
               

      datatype 'a result = Success of 'a | Failure of int

      fun parse (r, p, c) inputl =
         let
            val input = Vector.fromList inputl

            val n = Vector.length input

            val () = furthest := 0

            val s = r input 0
         in
            if S.member s n then
               let
                  val x = p input 0 n
               in
                  c ();
                  Sum.INL x
               end
            else
               (
               c ();
               Sum.INR (!furthest)
               )
         end

   end
