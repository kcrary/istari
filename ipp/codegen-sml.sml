
functor CodegenSmlFun (Output : OUTPUT) :> CODEGEN =
   struct

      open Output
      open Syntax

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
          "abstype", "and", "andalso", "as", "case", "datatype", "do", "else", "end", "eqtype", "exception", "fn", "fun", "handle", "if", "in", "infix", "infixr", "let", "local", "nonfix", "of", "op", "open", "orelse", "raise", "rec", "then", "type", "val", "with", "withtype", "while", "...", "=", "#"]

      (* str must be nonempty *)
      fun legalSmlSymbol str =
         List.all
            (fn #"!" => true
              | #"%" => true
              | #"&" => true
              | #"$" => true
              | #"#" => true
              | #"+" => true
              | #"-" => true
              | #"/" => true
              | #":" => true
              | #"<" => true
              | #"=" => true
              | #">" => true
              | #"?" => true
              | #"@" => true
              | #"\\" => true
              | #"~" => true
              | #"`" => true
              | #"^" => true
              | #"|" => true
              | #"*" => true
              | _ => false)
            (String.explode str)
      
      (* str is a valid identifier or type variable (the leading backslash convention isn't used for SML) *)
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
               legalSmlSymbol str
            then
               str
            else
               (* This identifier is reserved or uses symbols that SML doesn't allow. *)
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
   
      fun writeIdentifierGen doOp (sym, span) =
         (
         enter span;
         if doOp then write "op " else ();
         write (sanitize sym);
         write " ";
         leave ()
         )

      fun writeLongidGen doOp (syms, span) =
         (case syms of
             [sym] =>
                writeIdentifierGen doOp (sym, span)

           | _ =>
                (
                enter span;
                writes "." (fn sym => write (sanitize sym)) syms;
                write " ";
                leave ()
                ))

      val writeIdentifier = writeIdentifierGen false
      val writeIdentifierOp = writeIdentifierGen true
      val writeLongid = writeLongidGen false
      val writeLongidOp = writeLongidGen true

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

      fun writePat (pat, span) =
         (
         enter span;

         (case pat of
             Pwild => write "_ "

           | Punit => write "()"

           | Pident id => writeIdentifierOp id

           | Pconstr longid => writeLongidOp longid

           | Pnumber n =>
                (
                write (Int.toString n);
                write " "
                )
                
           | Pstring str =>
                (
                write "\"";
                write (String.toString str);
                write "\" "
                )

           | Pchar ch =>
                (
                write "#\"";
                write (Char.toString ch);
                write "\" "
                )

           | Pword n =>
                (
                write "(0w";
                write (IntInf.toString n);
                write " : Basis.Word.word)"
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
                writes "," writePat ps;
                write "]"
                )

           | Papp (longid, p) =>
                (
                write "(";
                writeLongidOp longid;
                writePat p;
                write ")"
                )

           | Papprecord (longid, fields) =>
                (
                write "(";
                writeLongidOp longid;
                write "{";
                app
                   (fn (label, p) =>
                       (
                       writeIdentifier label;
                       write "= ";
                       writePat p;
                       write ","
                       ))
                   fields;
                write "...}) "
                )

           | Pref p =>
                (
                write "(ref ";
                writePat p;
                write ")"
                )

           | Pas (id, p) =>
                (
                write "(";
                writeIdentifierOp id;
                write "as ";
                writePat p;
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

      (* Assume binds is given in standard form. *)
      fun writeTypeBind binds =
         (case binds of
             [] => raise (Fail "invariant")

           | (With _ :: _) =>
                (* No datatypes; these are ordinary type definitons. *)
                app
                   (fn Data _ => raise (Fail "invariant")
                     | With (args, id, t, sp) =>
                           (
                           write "type ";
                           enter sp;
                           writeTyargs args;
                           writeIdentifier id;
                           write "= ";
                           writeTy t;
                           leave ()
                           ))
                   binds

           | (Data _ :: _) =>
                (* Datatype declaration *)
                let
                   fun loop first binds =
                      (case binds of
                          [] => ()

                        | Data (args, id, dcons, sp) :: rest =>
                             (
                             if first then
                                write "datatype "
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
                                       writes ","
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

                        | With _ :: _ =>
                             (* remaining are all withtypes *)
                             (
                             write "withtype ";
                             writes "and "
                                (fn Data _ => raise (Fail "invariant")
                                  | With (args, id, t, sp) =>
                                       (
                                       enter sp;
                                       writeTyargs args;
                                       writeIdentifier id;
                                       write "= ";
                                       writeTy t;
                                       leave ()
                                       ))
                                binds
                             ))
                in
                   loop true binds
                end)

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
                write "type ";
                writeTyargs args;
                writeIdentifier id;
                write "= ";
                writeTy t
                )

           | Sdatatype binds => writeTypeBind binds

           | Smod (id, sg) =>
                (
                write "structure ";
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
                write "where type ";
                writeTyargs args;
                writeLongid longid;
                write "= ";
                writeTy t
                ));

         leave ()
         )

      
      fun writeExp (exp, span) =
         (
         enter span;

         (case exp of
             Eunit => write "()"

           | Eident longid => writeLongidOp longid

           | Econstr longid => writeLongidOp longid

           | Enumber n =>
                (
                write "(";
                write (Int.toString n);
                write " : int)"
                )

           | Ebignum n =>
                (
                write "(";
                write (IntInf.toString n);
                write " : IntInf.int)"
                )

           | Eword n =>
                (
                write "(0w";
                write (IntInf.toString n);
                write " : Basis.Word.word)"
                )

           | Estring str =>
                (
                write "\"";
                write (String.toString str);
                write "\" "
                )

           | Echar ch =>
                (
                write "#\"";
                write (Char.toString ch);
                write "\" "
                )

           | Elet (ds, e) =>
                (
                write "let ";
                app (writeDec false) ds;
                write "in ";
                writeExp e;
                write "end "
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
                writes "," writeExp es;
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
                writes "," (fn (label, e) =>
                                 (
                                 writeIdentifier label;
                                 write "= ";
                                 writeExp e
                                 )) fields;
                write "})"
                )

           | Ecase (e, clauses) =>
                (
                write "(case ";
                writeExp e;
                write "of ";
                writeMatch clauses;
                write ")"
                )

           | Etry (e, clauses) =>
                (
                write "((";
                writeExp e;
                write ")handle ";
                writeMatch clauses;
                write ")"
                )

           | Elam clauses =>
                (
                write "(fn ";
                writeMatch clauses;
                write ")"
                )

           | Elams (ps, tyo, e) =>
                (
                write "(";
                app (fn p => (
                             write "fn ";
                             writePat p;
                             write "=> "
                             )) ps;
                write "(";
                writeExp e;
                Option.app (fn t => 
                               (
                               write ": ";
                               writeTy t
                               )) tyo;
                write "))"
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
                write "andalso ";
                writeExp e2;
                write ")"
                )

           | Eorelse (e1, e2) =>
                (
                write "(";
                writeExp e1;
                write "orelse ";
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
         write "=> ";
         writeExp e;
         leave ()
         )

      and writeMatch clauses =
         writes "| " writeClause clauses

      and writeDec top (dec, span) =
         (
         enter span;

         (case dec of
             Dval (tyargs, p, e) =>
                (
                write "val ";
                writeTyargs tyargs;
                writePat p;
                write "= ";
                writeExp e
                )

           | Dfun (tyargs, funs) =>
                (
                write "fun ";
                writeTyargs tyargs;
                writes "and "
                   (fn (id, arms, sp) =>
                       (
                       enter sp;
                       writes "| "
                          (fn (ps, tyo, e, sp') =>
                              (
                              enter sp';
                              writeIdentifierOp id;
                              app writePat ps;
                              Option.app (fn t =>
                                             (
                                             write ": ";
                                             writeTy t
                                             )) tyo;
                              write "= ";
                              writeExp e;
                              leave ()
                              ))
                          arms;
                       leave ()
                       ))
                   funs
                )

           | Ddo _ =>
                (* traversal eliminates these *)
                raise (Fail "precondition")

           | Dtype (args, id, t) =>
                (
                write "type ";
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
                write "open ";
                writeLongid longid
                )

           | Dmod (id, m, sgo) =>
                (
                write "structure ";
                writeIdentifier id;
                (case sgo of
                    NONE => ()
                  | SOME sg =>
                       (
                       write ":> ";
                       writeSg sg
                       ));
                write "= ";
                writeMod m
                )

           | Dfunctor (id, arg, dom, m, codo) =>
                (
                write "functor ";
                writeIdentifier id;
                write "(";
                writeIdentifier arg;
                write ": ";
                writeSg dom;
                write ")";
                (case codo of
                    NONE => ()
                  | SOME sg =>
                       (
                       write ":> ";
                       writeSg sg
                       ));
                write "= ";
                writeMod m
                )

           | Dfunctoralt (id, specs, specspan, m, codo) =>
                (
                write "functor ";
                writeIdentifier id;
                enter specspan;
                write "(";
                app writeSpec specs;
                write ")";
                leave ();
                (case codo of
                    NONE => ()
                  | SOME sg =>
                       (
                       write ":> ";
                       writeSg sg
                       ));
                write "= ";
                writeMod m
                )
             
           | Dsig (id, sg) =>
                (
                write "signature ";
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
                app (writeDec true) ds;
                write "end "
                )

           | Mapp (funct, arg) =>
                (
                writeIdentifier funct;
                write "(";
                writeMod arg;
                write ")"
                )

           | Mappalt (funct, ds, dspan) =>
                (
                writeIdentifier funct;
                enter dspan;
                write "(";
                app (writeDec true) ds;
                write ")";
                leave ()
                )

           | Mseal (m, sg) =>
                (
                write "(";
                writeMod m;
                write ":> ";
                writeSg sg;
                write ")"
                ));

         leave ()
         )

      fun writeDirective (dir, span) =
         (
         enter span;

         (case dir of
             Vdec d => writeDec true d

           | Vnull => ()

             (* should have eliminated these already *)
           | Vexp _ => raise (Fail "precondition")
           | Vgrammardef _ => raise (Fail "precondition")
           | Vgrammaron _ => raise (Fail "precondition")
           | Vgrammaroff _ => raise (Fail "precondition"));

         leave ()
         )

      fun writeProgram _ (l, span) =
         (
         enter span;
         app writeDirective l;
         leave ()
         )

   end
