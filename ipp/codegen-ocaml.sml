
functor CodegenOcamlFun (Output : OUTPUT) :> CODEGEN =
   struct

      open Output
      open Syntax

      fun fst (x, y) = x
      fun snd (x, y) = y

      fun writes str f l =
         (case l of
             [] => ()

           | h :: t =>
                (
                f h;
                app (fn x => (write str; f x)) t
                ))

      structure Table = SymbolHashTable

      val reserved : unit Table.table = Table.table 101

      (* Many of these are impossible, but it's easiest to dump them all in.
         We make Basis and Smlbasis unshadowable.
      *)

      val () =
         List.app
         (fn str => Table.insert reserved (Symbol.fromValue str) ())
         ["Basis", "Smlbasis", 
          "and", "as", "assert", "asr", "begin", "class", "constraint", "do", "done", "downto", "else", "end", "exception", "external", "false", "for", "fun", "function", "functor", "if", "in", "include", "inherit", "initializer", "land", "lazy", "let", "lor", "lsl", "lsr", "lxor", "match", "method", "mod", "module", "mutable", "new", "nonrec", "object", "of", "open", "or", "private", "rec", "sig", "struct", "then", "to", "true", "try", "type", "val", "virtual", "when", "while", "with", "!=", "#", "&", "&&", "'", "(", ")", "*", "+", ",", "-", "-.", "->", ".", ".~", ":", "::", ":=", ":>", ";", ";;", "<", "<-", "=", ">", ">]", ">}", "?", "[", "[<", "[>", "[|", "]", "_", "`", "{", "{<", "|", "|]", "||", "}", "~"]

      (* str must be nonempty *)
      fun legalOcamlSymbol str =
         (case String.explode str of
             [] => raise (Fail "precondition")
           | ch :: rest =>
                (case ch of
                    #"$" => true
                  | #"&" => true
                  | #"*" => true
                  | #"+" => true
                  | #"-" => true
                  | #"/" => true
                  | #"=" => true
                  | #">" => true
                  | #"@" => true
                  | #"^" => true
                  | #"|" => true
                  | _ => false)
                andalso
                List.all
                   (fn #"$" => true
                     | #"&" => true
                     | #"*" => true
                     | #"+" => true
                     | #"-" => true
                     | #"=" => true
                     | #">" => true
                     | #"@" => true
                     | #"^" => true
                     | #"|" => true
                     | #"~" => true
                     | #"!" => true
                     | #"?" => true
                     | #"%" => true
                     | #"<" => true
                     | #":" => true
                     | #"." => true
                     | _ => false)
                  rest)

      (* sym must be a valid identifier or type variable or a string with leading backslash *)
      fun sanitize sym =
         let 
            val str = Symbol.toValue sym
            val ch = String.sub (str, 0)
         in
            (* See the comment in Initial for an explanation of leading backslash. *)
            if ch = #"\\" then
               String.extract (str, 1, NONE)
            else if ch = #"'" then
               str
            else if Char.isAlpha ch then
               if Table.member reserved sym then
                  str ^ "__"
               else
                  str
            else if
               not (Table.member reserved sym)
               andalso
               legalOcamlSymbol str
            then
               String.concat ["( ", str, " )"]
            else
               (* This identifier is reserved or uses symbols that OCaml doesn't allow. *)
               "s__" ^
               String.translate
                  (fn #"!" => "b"
                    | #"#" => "o"
                    | #"$" => "d"
                    | #"%" => "p"
                    | #"&" => "a"
                    | #"'" => "R"
                    | #"*" => "T"
                    | #"+" => "P"
                    | #"-" => "M"
                    | #"." => "D"
                    | #":" => "c"
                    | #"<" => "L"
                    | #"=" => "e"
                    | #">" => "G"
                    | #"?" => "q"
                    | #"@" => "A"
                    | #"^" => "C"
                    | #"|" => "v"
                    | #"~" => "t"
                    | #"`" => "l"
                    | ch => raise (Fail "precondition"))
                  str
         end
         
             

      fun writeIdentifier (sym, span) =
         (
         enter span;
         write (sanitize sym);
         write " ";
         leave ()
         )

      fun writeLongid (syms, span) =
         (
         enter span;
         writes "." (fn sym => write (sanitize sym)) syms;
         write " ";
         leave ()
         )

      fun writeTy (ty, span) =
         (
         enter span;

         (case ty of
             Tident longid => writeLongid longid

           | Ttyvar id => writeIdentifier id

           | Tapp ([], _) => raise (Fail "invariant")

           | Tapp (args, longid) =>
                (
                write "((";
                writes "," writeTy args;
                write ")";
                writeLongid longid;
                write ")"
                )

           | Tprod ts =>
                (
                write "(";
                writes "* " writeTy ts;
                write ")"
                )

           | Tarrow (t1, t2) =>
                (
                write "(";
                writeTy t1;
                write "-> ";
                writeTy t2;
                write ")"
                ));

         leave ()
         )

      fun writeInt n =
         if n < 0 then
            (
            write "(-";
            write (Int.toString (~ n));
            write ")"
            )
         else
            (
            write (Int.toString n);
            write " "
            )

      fun charToOcamlString ch =
         (case ch of
             #"\\" => "\\\\"
           | #"\"" => "\\\""
           | _ =>
                if Char.isPrint ch then
                   String.str ch
                else if Char.ord ch <= 255 then
                   "\\x" ^ StringCvt.padLeft #"0" 2 (Int.fmt StringCvt.HEX (Char.ord ch))
                else
                   raise (Fail "character out of range"))

      fun stringToOcamlString str =
         String.translate charToOcamlString str

      fun writePat (pat, span) =
         (
         enter span;

         (case pat of
             Pwild => write "_ "

           | Punit => write "()"

           | Pident id => writeIdentifier id

           | Pconstr longid => writeLongid longid

           | Pnumber n => writeInt n
                
           | Pstring str =>
                (
                write "\"";
                write (stringToOcamlString str);
                write "\" "
                )

           | Pchar ch =>
                (
                write "'";
                write (charToOcamlString ch);
                write "' "
                )

           | Pword n =>
                (
                write "(Basis.Word.fromInt ";
                write (Int.toString n);
                write ")"
                )

           | Ptuple ps =>
                (
                write "(";
                writes "," writePat ps;
                write ")"
                )

           | Plist ps =>
                (
                write "[";
                writes ";" writePat ps;
                write "]"
                )

           | Papp (longid, p) =>
                (
                write "(";
                writeLongid longid;
                writePat p;
                write ")"
                )

           | Papprecord (longid, fields) =>
                (
                write "(";
                writeLongid longid;
                write "{";
                app
                   (fn (label, p) =>
                       (
                       writeIdentifier label;
                       write "= ";
                       writePat p;
                       write ";"
                       ))
                   fields;
                write "}) "
                )

           | Pref p =>
                (
                write "{contents= ";
                writePat p;
                write "}"
                )

           | Pas (id, p) =>
                (
                write "(";
                writePat p;
                write "as ";
                writeIdentifier id;
                write ")"
                )

           | Pannot (p, t) =>
                (
                write "(";
                writePat p;
                write ": ";
                writeTy t;
                write ")"
                )

           | Pjuxta _ =>
                raise (Fail "invariant"));

         leave ()
         )

      fun writeTyargs args =
         (case args of
             [] => ()

           | [arg] => writeIdentifier arg

           | _ :: _ :: _ =>
                (
                write "(";
                writes "," writeIdentifier args;
                write ")"
                ))

      fun writeTyargsExplicit args =
         (case args of
             [] => ()

           | _ ::_ =>
                (
                write "(type ";
                List.app writeIdentifier args;
                write ")"
                ))

      (* Assume binds is given in standard form. *)
      fun writeTypeBind binds =
         let
            fun loop first binds =
               (case binds of
                   [] => ()

                 | Data (args, id, dcons, sp) :: rest =>
                      (
                      if first then
                         write "type "
                      else
                         write "and ";

                      enter sp;
                      writeTyargs args;
                      writeIdentifier id;
                      write "= ";
                      writes "| "
                         (fn Dcon (id, tyo, sp') =>
                                (
                                enter sp';
                                writeIdentifier id;
                                (case tyo of
                                    NONE => ()

                                  | SOME (Tprod ts, _) =>
                                       (* We have to make sure not to parenthesize this product! *)
                                       (
                                       write "of ";
                                       writes "* " writeTy ts
                                       )

                                  | SOME t =>
                                       (
                                       write "of ";
                                       writeTy t
                                       ));
                                leave ()
                                )
                           | Record (id, fields, sp') =>
                                (
                                enter sp';
                                writeIdentifier id;
                                write "of {";
                                writes ";"
                                   (fn (label, t) =>
                                       (
                                       writeIdentifier label;
                                       write ": ";
                                       writeTy t
                                       ))
                                   fields;
                                write "}";
                                leave ()
                                ))
                         dcons;
                      leave ();
                      loop false rest
                      )

                 | With (args, id, t, sp) :: rest =>
                      (
                      if first then
                         write "type "
                      else
                         write "and ";

                      enter sp;
                      writeTyargs args;
                      writeIdentifier id;
                      write "= ";
                      writeTy t;
                      leave ();
                      loop false rest
                      ))
         in
            loop true binds
         end

      fun writeSpec (spec, span) =
         (
         enter span;

         (case spec of
             Sval (id, t) =>
                (
                write "val ";
                writeIdentifier id;
                write ": ";
                writeTy t
                )

           | Sabstype (args, id) =>
                (
                write "type ";
                writeTyargs args;
                writeIdentifier id
                )

           | Stype (args, id, t) =>
                (
                write "type nonrec ";
                writeTyargs args;
                writeIdentifier id;
                write "= ";
                writeTy t
                )

           | Sdatatype binds => writeTypeBind binds

           | Smod (id, sg) =>
                (
                write "module ";
                writeIdentifier id;
                write ": ";
                writeSg sg
                )

           | Sextension (id, tyo) =>
                (
                write "exception ";
                writeIdentifier id;
                (case tyo of
                    NONE => ()

                  | SOME t => 
                       (
                       write "of ";
                       writeTy t
                       ))
                )

           | Sinclude id =>
                (
                write "include ";
                writeIdentifier id
                ));

         leave ()
         )

      and writeSg (sg, span) =
         (
         enter span;

         (case sg of
             Sident id =>
                writeIdentifier id

           | Ssig specs =>
                (
                write "sig ";
                app writeSpec specs;
                write "end "
                )

           | Swhere (sg1, longid, args, t) =>
                (
                writeSg sg1;
                write "with type ";
                writeTyargs args;
                writeLongid longid;
                write "= ";
                writeTy t
                ));

         leave ()
         )

      fun toOcamlString str =
         String.translate
            (fn #"\\" => "\\\\"
              | #"\"" => "\\\""
              | ch =>
                   if Char.isPrint ch then
                      String.str ch
                   else
                      let 
                         val n = Char.ord ch
                      in
                         if n > 255 then
                            raise (Fail "character out of range")
                         else
                            "\\x" ^ Int.fmt StringCvt.HEX n
                      end)
            str

      fun writeExp (exp, span) =
         (
         enter span;

         (case exp of
             Eunit => write "()"

           | Eident longid => writeLongid longid

           | Econstr longid => writeLongid longid

           | Enumber n => writeInt n

           | Eword n =>
                (
                write "(Basis.Word.fromInt ";
                write (Int.toString n);
                write ")"
                )

           | Estring str =>
                (
                write "\"";
                write (stringToOcamlString str);
                write "\" "
                )

           | Echar ch =>
                (
                write "'";
                write (charToOcamlString ch);
                write "' "
                )

           | Elet (ds, e) =>
                (
                write "(";
                writeLet (SOME (fst span)) ds e;
                write ")"
                )

           | Etuple es =>
                (
                write "(";
                writes "," writeExp es;
                write ")"
                )

           | Elist es =>
                (
                write "[";
                writes ";" writeExp es;
                write "]"
                )

           | Eapp (e1, e2) =>
                (
                write "(";
                writeExp e1;
                writeExp e2;
                write ")"
                )

           | Eapprecord (longid, fields) =>
                (
                write "(";
                writeLongid longid;
                write "{";
                writes ";" (fn (label, e) =>
                                 (
                                 writeIdentifier label;
                                 write "= ";
                                 writeExp e
                                 )) fields;
                write "})"
                )

           | Ecase (e, clauses) =>
                (
                write "(match ";
                writeExp e;
                write "with ";
                writeMatch clauses;
                write ")"
                )

           | Etry (e, clauses) =>
                (
                write "(try(";
                writeExp e;
                write ")with ";
                writeMatch clauses;
                write ")"
                )

           | Elam clauses =>
                (
                write "(function ";
                writeMatch clauses;
                write ")"
                )

           | Elams (ps, tyo, e) =>
                (
                write "(fun ";
                app writePat ps;
                Option.app (fn t => 
                               (
                               write ": ";
                               writeTy t
                               )) tyo;
                write "-> ";
                writeExp e;
                write ")"
                )

           | Eannot (e, t) =>
                (
                write "(";
                writeExp e;
                write ": ";
                writeTy t;
                write ")"
                )

           | Eif (e1, e2, e3) =>
                (
                write "(if ";
                writeExp e1;
                write "then ";
                writeExp e2;
                write "else ";
                writeExp e3;
                write ")"
                )

           | Eseq es =>
                (
                write "(";
                writes ";" writeExp es;
                write ")"
                )

           | Eandalso (e1, e2) =>
                (
                write "(";
                writeExp e1;
                write "&& ";
                writeExp e2;
                write ")"
                )

           | Eorelse (e1, e2) =>
                (
                write "(";
                writeExp e1;
                write "|| ";
                writeExp e2;
                write ")"
                )

           | Eraise e =>
                (
                write "(raise ";
                writeExp e;
                write ")"
                )

           | Ejuxta _ =>
                raise (Fail "precondition")

           | Eterm _ =>
                raise (Fail "precondition"));
                
         leave ()
         )

      and writeClause (p, e, sp) =
         (
         enter sp;
         writePat p;
         write "-> ";
         writeExp e;
         leave ()
         )

      and writeMatch clauses =
         writes "| " writeClause clauses

      and writeLet lposo decs (exp as (_, (_, rpos))) =
         (case decs of
             [] =>
                writeExp exp

           | (dec_, (lpos, _)) :: rest =>
                (
                (case lposo of
                    SOME lpos' =>
                       enter (lpos', rpos)

                  | NONE =>
                       enter (lpos, rpos));

                (case dec_ of
                    Dval (tyargs, p, e) =>
                       (
                       write "let ";
                       writeTyargsExplicit tyargs;
                       writePat p;
                       write "= ";
                       writeExp e;
                       write "in ";
                       writeLet NONE rest exp
                       )

                  | Dfun (tyargs, funs) =>
                       (
                       write "let rec ";
                       writes "and " (writeFun tyargs) funs;
                       write "in ";
                       writeLet NONE rest exp
                       )

                  | Ddo _ =>
                       (* traversal eliminates these *)
                       raise (Fail "precondition")

                  | Dtype (args, id, t) =>
                       (* for some reason OCaml won't let you write this directly *)
                       (
                       write "let module M__ = struct ";
                       write "type nonrec ";
                       writeTyargs args;
                       writeIdentifier id;
                       write "= ";
                       writeTy t;
                       write "end in let open M__ in ";
                       writeLet NONE rest exp
                       )

                  | Ddatatype binds =>
                       (* for some reason OCaml won't let you write this directly *)
                       (
                       write "let module M__ = struct ";
                       writeTypeBind binds;
                       write "end in let open M__ in ";
                       writeLet NONE rest exp
                       )

                  | Dextension (id, tyo) =>
                       (
                       write "let exception ";
                       writeIdentifier id;
                       Option.app (fn t =>
                                      (
                                      write "of ";
                                      writeTy t
                                      )) tyo;
                       write "in ";
                       writeLet NONE rest exp
                       )

                  | Dextcopy (id, longid) =>
                       (
                       write "let module M__ = struct exception ";
                       writeIdentifier id;
                       write "= ";
                       writeLongid longid;
                       write "end in let open M__ in ";
                       writeLet NONE rest exp
                       )

                  | Dinclude longid =>
                       (
                       write "let open ";
                       writeLongid longid;
                       write "in ";
                       writeLet NONE rest exp
                       )

                  (* only expdecs can be let bound in a term *)
                  | Dmod _ => raise (Fail "precondition")
                  | Dfunctor _ => raise (Fail "precondition")
                  | Dfunctoralt _ => raise (Fail "precondition")
                  | Dsig _ => raise (Fail "precondition"));

                leave ()
                ))

      and writeFun tyargs (id, arms, span) =
         (
         enter span;

         writeIdentifier id;
         writeTyargsExplicit tyargs;
         write "= ";
         (case arms of
             [(ps, tyo, e, sp)] =>
                (* one arm, use fun *)
                (
                enter sp;
                write "(fun ";
                app writePat ps;
                Option.app (fn t =>
                               (
                               write ": ";
                               writeTy t
                               )) tyo;
                write "-> ";
                writeExp e;
                write ")";
                leave ()
                )

           | _ =>
                let
                   val n =
                      (case arms of
                          (ps, _, _, _) :: _ => length ps
                        | _ =>
                             (* the parser ensures that fun declarations are not empty *)
                             raise (Fail "precondition"))
                in
                   if n = 1 then
                      (* every arm has just one pattern, use function *)
                      (
                      write "(function ";
                      app (fn ([p], tyo, e, sp) =>
                                 (
                                 enter sp;
                                 write "| ";
                                 writePat p;
                                 write "-> ";
                                 (case tyo of
                                     NONE => writeExp e
                                   | SOME t =>
                                        (
                                        write "(";
                                        writeExp e;
                                        write ": ";
                                        writeTy t;
                                        write ")"
                                        ));
                                 leave ()
                                 )
                            | _ => raise (Fail "impossible")) arms;
                      write ")"
                      )
                   else
                      (* multiple arms with multiple patterns, do it the hard way *)
                      let
                         fun loopargs sep i =
                            if i >= n then
                               ()
                            else
                               (
                               write sep;
                               write "a__";
                               write (Int.toString i);
                               loopargs sep (i+1)
                               )

                         fun args sep =
                            (
                            write "a__0 ";
                            loopargs sep 1
                            )
                      in
                         write "(fun ";
                         args " ";
                         write "-> ";
                         write "(match (";
                         args ",";
                         write ")with ";

                         app (fn (ps, tyo, e, sp) =>
                                 (
                                 enter sp;
                                 write "| (";
                                 writes "," writePat ps;
                                 write ")-> ";
                                 (case tyo of
                                     NONE => writeExp e
                                   | SOME t =>
                                        (
                                        write "(";
                                        writeExp e;
                                        write ": ";
                                        writeTy t;
                                        write ")"
                                        ));
                                 leave ()
                                 )) arms;

                         write "))"
                      end
                end);

         leave ()
         )

      and writeDec (dec, span) =
         (
         enter span;

         (case dec of
             Dval (tyargs, p, e) =>
                (
                write "let ";
                writeTyargsExplicit tyargs;
                writePat p;
                write "= ";
                writeExp e
                )

           | Dfun (tyargs, funs) =>
                (
                write "let rec ";
                writes "and " (writeFun tyargs) funs
                )

           | Ddo _ =>
                (* traversal eliminates these *)
                raise (Fail "precondition")

           | Dtype (args, id, t) =>
                (
                write "type nonrec ";
                writeTyargs args;
                writeIdentifier id;
                write "= ";
                writeTy t
                )

           | Ddatatype binds => writeTypeBind binds

           | Dextension (id, tyo) =>
                (
                write "exception ";
                writeIdentifier id;
                (case tyo of
                    NONE => ()

                  | SOME t => 
                       (
                       write "of ";
                       writeTy t
                       ))
                )

           | Dextcopy (id, longid) =>
                (
                write "exception ";
                writeIdentifier id;
                write "= ";
                writeLongid longid
                )

           | Dinclude longid =>
                (
                write "include ";
                writeLongid longid
                )

           | Dmod (id, m, sgo) =>
                (
                write "module ";
                writeIdentifier id;
                (case sgo of
                    NONE => ()
                  | SOME sg =>
                       (
                       write ": ";
                       writeSg sg
                       ));
                write "= ";
                writeMod m
                )

           | Dfunctor (id, arg, dom, m, codo) =>
                (
                write "module ";
                writeIdentifier id;
                write "(";
                writeIdentifier arg;
                write ": ";
                writeSg dom;
                write ") ()";
                (case codo of
                    NONE => ()
                  | SOME sg =>
                       (
                       write ": ";
                       writeSg sg
                       ));
                write "= ";
                writeMod m
                )

           | Dfunctoralt _ =>
                (* elmininated in traversal *)
                raise (Fail "precondition")
             
           | Dsig (id, sg) =>
                (
                write "module type ";
                writeIdentifier id;
                write "= ";
                writeSg sg
                ));

         leave ()
         )

      and writeMod (md, span) =
         (
         enter span;

         (case md of
             Mident longid =>
                writeLongid longid

           | Mstruct ds =>
                (
                write "struct ";
                app writeDec ds;
                write "end "
                )

           | Mapp (funct, arg) =>
                (
                writeIdentifier funct;
                write "(";
                writeMod arg;
                write ") ()"
                )

           | Mappalt _ =>
                (* eliminated in traversal *)
                raise (Fail "precondition")

           | Mseal (m, sg) =>
                (
                write "(";
                writeMod m;
                write ": ";
                writeSg sg;
                write ")"
                ));
                
         leave ()
         )

      fun writeDirective (dir, span) =
         (
         enter span;

         (case dir of
             Vdec d =>
                (
                writeDec d;
                write ";;"
                )

           | Vnull => ()

             (* should have eliminated these already *)
           | Vexp _ => raise (Fail "precondition")
           | Vgrammardef _ => raise (Fail "precondition")
           | Vgrammaron _ => raise (Fail "precondition")
           | Vgrammaroff _ => raise (Fail "precondition"));

         leave ()
         )


      fun writeProgram deps (l, span) =
         (
         enter span;

         app
            (fn dep =>
                let
                   val dep' =
                      String.str (Char.toUpper (String.sub (dep, 0)))
                      ^ String.extract (dep, 1, NONE)
                in
                   write "open ";
                   write dep';
                   write ";; "
                end)
            deps;
         
         app writeDirective l;
         leave ()
         )

   end

