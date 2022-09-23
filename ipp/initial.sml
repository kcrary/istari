
signature INITIAL =
   sig

      (* bool: SML-compatibility mode? *)
      val basis : Language.language -> bool -> Context.context

   end


structure Initial :> INITIAL =
   struct

      type bundle = Context.bundle

      open PrecedenceTable

      fun infixesMain mode =
         map (fn (str, prec) => (Symbol.fromValue str, prec))
            [
            ("*", (7, LEFT, mode)),
            ("div", (7, LEFT, mode)),
            ("rem", (7, LEFT, CURRIED)),
            ("+", (6, LEFT, mode)),
            ("-", (6, LEFT, mode)),
            ("^", (6, LEFT, mode)),
            ("::", (5, RIGHT, TUPLED)),
            ("@", (5, RIGHT, mode)),
            ("=", (4, LEFT, mode)),
            ("=$", (4, LEFT, CURRIED)),
            ("=#", (4, LEFT, CURRIED)),
            ("<>", (4, LEFT, mode)),
            (">", (4, LEFT, mode)),
            (">=", (4, LEFT, mode)),
            ("<", (4, LEFT, mode)),
            ("<=", (4, LEFT, mode)),
            (":=", (3, LEFT, mode)),
            ("$", (0, RIGHT, CURRIED))
            ]

      fun infixes smlCompat : bundle =
         { 
         infixes = 
            if smlCompat then
               [
               (Symbol.fromValue "mod", (7, LEFT, TUPLED)),
               (Symbol.fromValue "o", (3, LEFT, TUPLED))
               ]
               @
               infixesMain TUPLED
            else
               infixesMain CURRIED ,

         rules = [],
         reserved = [],
         starts = [],
         default = NONE
         }

      structure C = Context

      (* put pervasive infixes under the empty key so they cannot be deactivated *)
      val symNull = Symbol.fromValue ""

      val infixesIml = C.activate (C.define C.empty symNull (infixes false)) symNull
      val infixesSml = C.activate (C.define C.empty symNull (infixes true)) symNull


      val symBasis = Symbol.fromValue "\\Basis"
      val symSmlbasis = Symbol.fromValue "\\Smlbasis"

      fun collUnd path = Symbol.fromValue (String.concatWith "__" (map Symbol.toValue path))
      fun collDot path = Symbol.fromValue (String.concatWith "." (map Symbol.toValue path))
      fun collFail _ = raise (Fail "nested signaure")

      datatype data = 
         E of int
       | EQ of string list * int    (* do not relocate, use indicated name *)
       | T
       | TQ of string list          (* do not relocate, use indicated name *)
       | S of (string * data) list
       | M of (string * data) list


      fun makeContext prefix coll data =
         foldl
         (fn ((str, x), ctx) =>
             let
                val id = Symbol.fromValue str
             in
                (case x of
                    E arity => 
                       C.forwardExp ctx id (prefix @ [id], arity)

                  | EQ (path, arity) => 
                       C.forwardExp ctx id (map Symbol.fromValue path, arity)

                  | T => 
                       C.forwardType ctx id (prefix @ [id])

                  | TQ path => 
                       C.forwardType ctx id (map Symbol.fromValue path)

                  | S data' => 
                       C.forwardSig ctx id (coll (prefix @ [id]), makeContext [] collFail data')

                  | M data' => 
                       C.forwardMod ctx id (prefix @ [id], makeContext [] collFail data'))
             end)
         C.empty
         data


      (* A leading backslash indicates to the code generator not to sanitize this variable.
         If the user rebinds them, they will be sanitized as usual.
         The lexer ensures that identifiers with a leading backslash never occur in nature.

         This is needed in OCaml for true, false, [], and ::, which are reserved words,
         and in both SML and OCaml where I've made some identifiers (e.g. Basis) into reserved
         words so they can't be shadowed.

         We can't just forward them to new names, because we need/want these particular
         names.  (In the case of true, etc, we want it to agree with the built-in meanings,
         and you cannot rename constructors.)
      *)

      val commonPervasives =
         [
         ("bool", TQ ["bool"]),
         ("int", TQ ["int"]),
         ("list", TQ ["list"]),
         ("option", TQ ["option"]),
         ("ref", TQ ["ref"]),
         ("string", TQ ["string"]),
         ("char", TQ ["char"]),
         ("exn", TQ ["exn"]),
         ("unit", TQ ["unit"]),
         ("ref", EQ (["ref"], 0)),
         ("Fail", EQ (["\\Basis", "General", "Fail"], 1))
         ]

      val commonModulePervasives =
         [
         ("not", "Bool"),
         ("~", "Int"),
         ("+", "Int"),
         ("-", "Int"),
         ("*", "Int"),
         ("div", "Int"),
         ("<", "Int"),
         (">", "Int"),
         ("<=", "Int"),
         (">=", "Int"),
         ("^", "String"),
         ("@", "List"),
         ("foldl", "List"),
         ("foldr", "List"),
         ("map", "List"),
         ("app", "List"),
         ("print", "TextIO"),
         ("!", "General"),
         (":=", "General"),
         ("LESS", "General"),
         ("EQUAL", "General"),
         ("GREATER", "General"),
         ("Div", "General")
         ]


      val imlPervasives =
         [
         ("=$", EQ (["\\Basis", "String", "="], 0)),
         ("=#", EQ (["\\Basis", "Char", "="], 0)),
         ("Invalid", EQ (["\\Basis", "General", "Invalid"], 1)),
         ("fst", EQ (["\\Basis", "General", "fst"], 0)),
         ("snd", EQ (["\\Basis", "General", "snd"], 0)),
         ("n1of3", EQ (["\\Basis", "General", "n1of3"], 0)),
         ("n2of3", EQ (["\\Basis", "General", "n2of3"], 0)),
         ("n3of3", EQ (["\\Basis", "General", "n3of3"], 0))
         ]
         @
         map (fn (oper, loc) => (oper, EQ (["\\Basis", loc, oper], 0)))
            ([
             ("rem", "Int"),
             ("=", "Int"),
             ("<>", "Int"),
             ("$", "General")
             ] @ commonModulePervasives)
         @ 
         commonPervasives

      val smlPervasives =
         [
         ("array", TQ ["array"]),
         ("=", EQ (["\\Smlbasis", "="], 0)),
         ("<>", EQ (["\\Smlbasis", "<>"], 0))
         ]
         @
         map (fn (oper, loc) => (oper, EQ (["\\Smlbasis", loc, oper], 0)))
            ([
             ("mod", "Int"),
             ("size", "String"),
             ("length", "List"),
             ("hd", "List"),
             ("tl", "List"),
             ("rev", "List"),
             ("isSome", "Option"),
             ("valOf", "Option"),
             ("o", "General"),
             ("Subscript", "General")
             ] @ commonModulePervasives)
         @ commonPervasives
      

      val commonPervasivesSml =
         [
         ("order", TQ ["order"]),
         ("true", EQ (["true"], 0)),
         ("false", EQ (["false"], 0)),
         ("nil", EQ (["nil"], 0)),
         ("::", EQ (["::"], 2)),
         ("NONE", EQ (["NONE"], 0)),
         ("SOME", EQ (["SOME"], 1))
         ]

      val commonPervasivesOcaml =
         [
         ("order", TQ ["\\Order", "order"]),
         ("true", EQ (["\\true"], 0)),
         ("false", EQ (["\\false"], 0)),
         ("nil", EQ (["\\[]"], 0)),
         ("::", EQ (["\\(::)"], 2)),
         ("NONE", EQ (["\\None"], 0)),
         ("SOME", EQ (["\\Some"], 1))
         ]

      val imlPervasivesSml' = commonPervasivesSml @ imlPervasives
      val imlPervasivesOcaml' = commonPervasivesOcaml @ imlPervasives

      val smlPervasivesSml' =
         [("word", TQ ["word"])] @ commonPervasivesSml @ smlPervasives

      val smlPervasivesOcaml' =
         [("word", TQ ["\\Word62", "word"])] @ commonPervasivesOcaml @ smlPervasives


      val imlPervasivesSml =
         C.union
            (makeContext [symBasis] collUnd imlPervasivesSml')
            infixesIml

      val imlPervasivesOcaml =
         C.union
            (makeContext [symBasis] collDot imlPervasivesOcaml')
            infixesIml

      val smlPervasivesSml =
         C.union
            (makeContext [symSmlbasis] collUnd smlPervasivesSml')
            infixesSml

      val smlPervasivesOcaml =
         C.union
            (makeContext [symSmlbasis] collDot smlPervasivesOcaml')
            infixesSml
         

      structure TB = TheBasis (datatype data = datatype data)


      fun basis language smlCompat =
         (case (language, smlCompat) of
             (Language.SML, false) =>
                C.union
                   imlPervasivesSml
                   (makeContext [symBasis] collUnd TB.basis1)

           | (Language.OCAML, false) =>
                C.union
                   imlPervasivesOcaml
                   (makeContext [symBasis] collDot TB.basis1)

           | (Language.SML, true) =>
                C.union
                   smlPervasivesSml
                   (makeContext [symSmlbasis] collUnd TB.basis2)

           | (Language.OCAML, true) =>
                C.union
                   smlPervasivesOcaml
                   (makeContext [symSmlbasis] collDot TB.basis2))

   end
