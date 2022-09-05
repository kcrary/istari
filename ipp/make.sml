
signature MAKE =
   sig

      val currentFilename : string ref
      val withInstream : string -> (TextIO.instream -> 'a) -> 'a

      (* project file, basis directory, write build info? *)
      val make : string -> string -> bool -> unit

      (* project file, source-file goodname 
         -> source-file fullname, context, dependencies, sml-compatibility *)
      val inversionInfo : string -> string -> string * Context.context * string list * bool

      (* project file -> context *)
      val load : string -> Context.context

      val getProjectBase : string -> string

   end


structure Make :> MAKE =
   struct

      structure L = Language
      structure C = Context
      structure P = Pickle
      structure E = Error
      structure PC = PreContext

      structure F  = SymbolFun (structure Value = StringHashable)
      structure PF = SymbolPickleableFun (structure Value = StringPickleable
                                          structure Symbol = F)
      structure D  = RedBlackDict (structure Key = SymbolOrderedFun (structure Symbol = F))
      structure PD = DictPickleableFun (structure Key = PF
                                        structure Dict = D)
      structure FS  = RedBlackSet (structure Elem = SymbolOrderedFun (structure Symbol = F))
      structure PFS = SetPickleableFun (structure Elem = PF
                                        structure Set = FS)
      structure PS  = SymbolPickleable

      type project = (string * Span.span) list

      (* modtime, active grammars, dependencies, context *)
      (* Source files are entered into the database using the santized basename. *)
      type database = (IntInf.int * Symbol.symbol list * FS.set * C.context) D.dict

      (* database, timestamp, timestamps of subprojects * final context *)
      type projdata = database * IntInf.int * IntInf.int D.dict * C.context

      val nullProjdata : projdata = (D.empty, 0, D.empty, C.empty)

      val puProjdata : projdata P.pu =
         P.tuple4
            (PD.pu (P.tuple4 P.intInf (P.list PS.pu) PFS.pu Context.pu))
            P.intInf
            (PD.pu P.intInf)
            Context.pu



      val currentFilename = ref ""

      fun withInstream filename f =
         let
            val () = currentFilename := filename

            val ins = 
               TextIO.openIn filename
               handle Io =>
                  raise (E.GeneralError ("unable to open input file " ^ filename))
         in
            Finally.finally
               (fn () => f ins)
               (fn () => TextIO.closeIn ins)
         end


      fun withOutstream filename f =
         let
            val outs =
               TextIO.openOut filename
               handle Io =>
                  raise (E.GeneralError ("unable to open output file " ^ filename))
         in
            Finally.finally
               (fn () => f outs)
               (fn () => TextIO.closeOut outs)
         end


      fun copyLoop ins outs =
         (case TextIO.input ins of
             "" => ()

           | str =>
                (
                TextIO.output (outs, str);
                copyLoop ins outs
                ))

      (* SML basis provides rename, but not copy. *)
      fun copy infile outfile =
         let
            val ins =
               TextIO.openIn infile
               handle Io =>
                  raise (E.GeneralError ("unable to open input file " ^ infile))
         in
            Finally.finally
               (fn () =>
                   let
                      val outs =
                         TextIO.openOut outfile
                         handle Io =>
                            raise (E.GeneralError ("unable to open output file " ^ outfile))
                   in
                      Finally.finally
                         (fn () => copyLoop ins outs)
                         (fn () => TextIO.closeOut outs)
                   end)
               (fn () => TextIO.closeIn ins)
         end


      fun sunderFilename fullname =
         let
            val fullname =
               Path.canonize fullname
               handle Path.Path =>
                  raise (E.GeneralError ("bad path name " ^ fullname))

            val (path, filename) = Path.split fullname
         in
            (case Path.splitExt filename of
                SOME (basename, ext) =>
                   (path, filename, basename, ext)

              | NONE =>
                   raise (E.GeneralError ("unknown file type " ^ filename)))
         end


      fun readProject filename =
         withInstream filename
         (fn ins => Lexer.lexProject (Stream.fromTextInstream ins))

      
      fun getProjectBase projname =
         let
            val (path, _, projbase, ext) = sunderFilename projname
         in
            if ext = "proj" then
               Path.join path projbase
            else
               raise (E.GeneralError "project file extension not recognized")
         end


      fun databaseFilename basename =
         (case !L.target of
             L.SML => Path.joinExt basename "ipds"
           | L.OCAML => Path.joinExt basename "ipdo")



      fun readDatabase insist basename =
         let
            val filename = databaseFilename basename
         in
            (case
                SOME (BinIO.openIn (databaseFilename basename))
                handle Io => NONE
             of
                NONE =>
                   if insist then
                      raise (E.GeneralError (String.concat ["required database file ", filename, " not present"]))
                   else
                      nullProjdata
   
              | SOME ins =>
                   Finally.finally
   
                   (fn () =>
                       ((
                        P.reset puProjdata;
                        P.unpickle
                           (fn () => (case BinIO.input1 ins of
                                         SOME b => b
                                       | NONE => raise Pickle.Error))
                           puProjdata
                        )
                        handle Pickle.Error =>
                           if insist then
                              raise (E.GeneralError (String.concat ["required database file ", filename, " corrupted"]))
                           else
                              (
                              E.warning ("database corrupted", E.UNKNOWN);
                              nullProjdata
                              )))
   
                   (fn () => BinIO.closeIn ins))
         end
                          
   
      fun writeDatabase basename projdata =
         let
            val outs =
               BinIO.openOut (databaseFilename basename)
               handle Io =>
                  raise (E.GeneralError "unable to open database file for writing")
         in
            Finally.finally

            (fn () =>
                ((
                 P.reset puProjdata;
                 P.pickle
                    (fn b => BinIO.output1 (outs, b))
                    puProjdata
                    projdata
                 )
                 handle Pickle.Error =>
                    raise (E.GeneralError "error writing database file")))

            (fn () => BinIO.closeOut outs)
         end


      (* returns (laundered basename, outfilename)

         The outfile name is used for writing output, but also
         for the list of files to recompile.
      *)
      fun processName basename ext =
         let
            val goodname = 
               String.translate
               (fn ch => if ch = #"-" then "_" else String.str ch)
               basename
         
            val goodname =
               if ext = "sig" then
                  goodname ^ "_sig"
               else
                  goodname

            val outfilename =
               Path.joinExt
                  goodname
                  (case (!L.target, ext) of
                      (L.SML, "iml") => "iml.sml"
                    | (L.SML, "sml") => "sml.sml"
                    | (L.SML, "sig") => "sml.sml"
                    | (L.SML, "ist") => "ist.sml"
                    | (L.SML, "ipc") => "ipc.sml"
                    | (L.OCAML, "iml") => "iml-ml"
                    | (L.OCAML, "sml") => "sml-ml"
                    | (L.OCAML, "sig") => "sml-ml"
                    | (L.OCAML, "ist") => "ist-ml"
                    | (L.OCAML, "ipc") => "ipc-ml"

                    | _ =>
                         raise (E.GeneralError ("unknown file type " ^ Path.joinExt goodname ext)))
         in
            (goodname, outfilename)
         end


      fun classToContext ctx p =
         (case p of
             PC.LIST items =>
                makeContext ctx items

           | PC.NAME (id as (sym, span)) =>
                (case C.lookupSig ctx id of
                    NONE =>
                       raise (Error.SemanticError ("unbound signature identifier " ^ Symbol.toValue sym, span))

                  | SOME (_, c) => c))

      and makeContext ctx items =
         #2 (List.foldl
                (fn (item, (ctx, c)) =>
                    (case item of
                        PC.VAL (id, arity) =>
                           (ctx, C.bindConstr c id arity)
           
                      | PC.TYPE id =>
                           (ctx, C.bindType c id)
           
                      | PC.SIG (id, p) => 
                           let
                              val c' = classToContext ctx p
                           in
                              (C.bindSig ctx id c',
                               C.bindSig c id c')
                           end
           
                      | PC.MOD (id, p) => 
                           (ctx, C.bindMod c id (classToContext ctx p))
           
                      | PC.FUN (id, p) => 
                           (ctx, C.bindFun c id (classToContext ctx p))))
                (ctx, C.empty)
                items)


      val currentDeps : FS.set ref = ref FS.empty

      fun register sym ctx =
         C.register ctx (fn () => currentDeps := FS.insert (!currentDeps) sym)

      fun depsToList deps =
         FS.foldl 
            (fn (sym, l) => F.toValue sym :: l)
            nil
            deps

      
      fun make1 ctx infile outfile ext span =
         if ext = "iml" orelse ext = "sml" orelse ext = "sig" orelse ext = "ist" then
            let
               val smlCompat =
                  ext = "sml" orelse ext = "sig"

               val () = L.smlCompatibility := smlCompat

               val () =
                  (
                  print "ipp: ";
                  print infile;
                  print " -> ";
                  print outfile;
                  print "\n"
                  )

               val ctx =
                  (* put the right pervasives in *)
                  Context.union 
                     ctx
                     (Initial.basis (!Language.target) smlCompat)

                val oldCurrentFilename = !currentFilename
                     
                val () = currentDeps := FS.empty
                val () = C.pingActives ctx

                val (program, _, ectx) =
                   withInstream infile
                   (fn ins =>
                       Traverse.traverse ctx
                       (Parser.parseFull (Stream.fromTextInstream ins)))

                val deps = !currentDeps
            in
               withOutstream outfile
                  (fn outs => Render.render outs (depsToList deps) program);

               currentFilename := oldCurrentFilename;

               (ectx, deps)
            end
         else if ext = "ipc" then
            let
               val oldCurrentFilename = !currentFilename

               val ectx =
                  withInstream infile
                  (fn ins =>
                      makeContext ctx (Parser.parseIpc (Stream.fromTextInstream ins)))

               val (basename, _) = Option.valOf (Path.splitExt infile)
               val sourceExt =
                  (case !L.target of
                      L.SML => "sml"
                    | L.OCAML => "ml")
            in
               copy (Path.joinExt basename sourceExt) outfile;

               currentFilename := oldCurrentFilename;

               (ectx, FS.empty)
            end
         else
            raise (E.SemanticError ("unknown file type " ^ infile, span))


      fun getModTime filename =
         Time.toMilliseconds (OS.FileSys.modTime filename)
         handle OS.SysErr _ =>
            raise (E.GeneralError ("cannot stat file " ^ filename))

      fun getTimestamp () = Time.toMilliseconds (Time.now ())


      fun makeLoop ctx database newDatabase unchanged timestamps newTimestamps project =
         (case project of
             [] => (newDatabase, newTimestamps, ctx)

           | (fullname, span) :: rest =>
                let
                   val (path, filename, basename, ext) = sunderFilename fullname
                in
                   if ext = "proj" then
                      let
                         val (subdatabase, timestamp, _, _) = readDatabase true (Path.join path basename)

                         val subprojFilesym = F.fromValue (Path.canonize fullname)
                         
                         val changed =
                            (case D.find timestamps subprojFilesym of
                                NONE => true

                              | SOME timestamp' =>
                                   timestamp <> timestamp')

                         val () =
                            if changed then
                               (
                               print "ipp: subproject ";
                               print fullname;
                               print " has been rebuilt\n"
                               )
                            else
                               ()

                         val (ctx', unchanged') =
                            D.foldl
                            (fn (filesym, (_, _, _, ectx), (ctx, unchanged)) =>
                                let
                                   val () = register filesym ectx

                                   val ctx' =
                                      C.unionDisj ctx ectx
                                      handle C.Collision cause =>
                                         raise (E.GeneralError (String.concat ["redefinition of ", cause, " in ", fullname]))

                                   val unchanged' = FS.insert unchanged filesym
                                in
                                   (ctx', unchanged')
                                end)
                            (ctx, unchanged)
                            subdatabase
                      in
                         (* If a subproject's timestamp has changed, everything can be different,
                            so we cannot re-use any source files after this.  (In principle, we
                            could chase down all the differences, but that's too much trouble.)
                            We'll make that happen by blanking out the old database.
                         *)
                         makeLoop 
                            ctx' 
                            (if changed then D.empty else database)
                            newDatabase
                            unchanged'
                            timestamps
                            (D.insert newTimestamps subprojFilesym timestamp)
                            rest
                      end
                   else
                      let
                         val (goodname, outfile) = processName basename ext
                         val filesym = F.fromValue goodname
      
                         val () =
                            if D.member newDatabase filesym then
                               raise (E.SemanticError (String.concat ["file ", fullname, " appears multiple times in project"], span))
                            else
                               ()
      
                         val modtime = getModTime fullname
      
                         (* NONE if we should rebuild; (SOME entry) if we can re-use *)
                         val shouldBuild =
                            (case D.find database filesym of
                                NONE => NONE
      
                              | SOME (entry as (modtime', actives, deps, ectx)) =>
                                   (* Don't need to rebuild if:
                                      1. the modtime is unchanged
                                      2. no dependencies have been rebuilt
                                      3. the list of active grammars is unchanged
                                   *)
                                   if
                                      modtime = modtime' 
                                      andalso
                                      FS.isEmpty (FS.difference deps unchanged)
                                      andalso
                                      ListPair.allEq Symbol.eq (actives, C.actives ctx)
                                   then
                                      SOME entry
                                   else
                                      NONE)
      
                         val (ectx, entry, unchanged') =
                            (case shouldBuild of
                                SOME (entry as (_, _, _, ectx))  =>
                                   (ectx, entry, FS.insert unchanged filesym)
      
                              | NONE =>
                                   let
                                      val (ectx, deps) = make1 ctx fullname outfile ext span
                                   in
                                      (ectx, 
                                       (modtime, C.actives ctx, deps, ectx),
                                       unchanged)
                                   end)
      
                         val ctx' =
                            C.unionDisj ctx ectx
                            handle C.Collision cause =>
                               raise (E.GeneralError (String.concat ["redefinition of ", cause, " in ", fullname]))
      
                         val () = register filesym ectx
                      in
                         makeLoop 
                            ctx' 
                            database 
                            (D.insert newDatabase filesym entry)
                            unchanged'
                            timestamps
                            newTimestamps
                            rest
                      end
                end)


      fun writeSmlBuild projbase basisdir project =
         let
            val outfile = projbase ^ ".cm"
         in
            withOutstream outfile
            (fn outs =>
                let
                   fun out str = TextIO.output (outs, str)
                in
                   out "Group\n   source(-)\n   library(";
                   out basisdir;
                   out "/basis.cm)\n";

                   List.app
                      (fn (fullname, _) =>
                          let
                             val (path, _, basename, ext) = sunderFilename fullname
                          in
                             if ext = "proj" then
                                (
                                out "   group(";
                                out (Path.join path (Path.joinExt basename "cm"));
                                out ")\n"
                                )
                             else
                                ()
                          end)
                      project;

                   out "is\n   ";
                   out basisdir;
                   out "/basis.cm\n";
                   
                   List.app
                      (fn (fullname, _) =>
                          let
                             val (path, _, basename, ext) = sunderFilename fullname
                          in
                             if ext = "proj" then
                                (
                                out "   ";
                                out (Path.join path (Path.joinExt basename "cm"));
                                out "\n"
                                )
                             else
                                let
                                   val (_, outname) = processName basename ext
                                in
                                   out "   ";
                                   out outname;
                                   out "\n"
                                end
                          end)
                      project;

                   print "ipp: ";
                   print outfile;
                   print " written\n"
                end)
          end


      fun writeOcamlBuild projbase basisdir database project =
         let
            val outfile = projbase ^ ".make"

            val inclstr =
               String.concat
               (List.foldl
                   (fn ((fullname, _), l) =>
                       let
                          val (path, _, _, ext) = sunderFilename fullname
                       in
                          if ext = "proj" then
                             " -I " :: path :: l
                          else
                             l
                       end)
                   [" -I ", basisdir]
                   project)
         in
            withOutstream outfile
            (fn outs =>
                let
                   fun out str = TextIO.output (outs, str)

                   val () =
                      (
                      out "INCL=";
                      out inclstr;
                      out "\n\n"
                      )

                   val locals =
                      (* evaluated for side-effects in addition to locals *)
                      List.foldl
                      (fn ((fullname, _), locals) =>
                          let
                             val (path, _, basename, ext) = sunderFilename fullname
                          in
                             if ext = "proj" then
                                locals
                             else
                                let
                                   val (goodname, outname) = processName basename ext
                                   val filesym = F.fromValue goodname
                                   val (_, _, deps, _) = D.lookup database filesym
                                   val locals' = FS.insert locals filesym
                                in
                                   out goodname;
                                   out ".cmi ";
                                   out goodname;
                                   out ".cmo : ";
                                   out outname;
                                   
                                   FS.app
                                      (fn dep =>
                                          (
                                          out " ";
                                          out (F.toValue dep);
                                          out ".cmi"
                                          ))
                                      (FS.intersection deps locals);
         
                                   out "\n\tocamlc -c -error-style short $(INCL)";
                                   out " -impl ";
                                   out outname;
                                   out "\n\n";
                                   locals'
                                end
                          end)
                      FS.empty
                      project
                in
                   out "OBJS =";

                   FS.app
                      (fn filesym =>
                          (
                          out " ";
                          out (F.toValue filesym);
                          out ".cmo"
                          ))
                      locals;

                   out "\n"
                end);

            print "ipp: ";
            print outfile;
            print " written\n"
         end


      fun make projname basisdir writebuild =
         let
            val () = Context.reset ()

            val project =
               withInstream projname
               (fn ins =>
                   Lexer.lexProject (Stream.fromTextInstream ins))

            val projbase = getProjectBase projname

            val (database, _, timestamps, _) = readDatabase false projbase

            val (database', timestamps', ctx) = 
               makeLoop  
                  C.empty
                  database
                  D.empty
                  FS.empty
                  timestamps
                  D.empty
                  project
         in
            writeDatabase projbase (database', getTimestamp (), timestamps', ctx);

            if writebuild then
               (case !L.target of
                   L.SML =>
                      writeSmlBuild projbase basisdir project
   
                 | L.OCAML =>
                      writeOcamlBuild projbase basisdir database' project)
            else
               ()
         end


      fun inversionInfo projname goodname =
         let
            val project =
               withInstream projname
               (fn ins =>
                   Lexer.lexProject (Stream.fromTextInstream ins))

            val (projpath, _) = Path.split projname
            val (database, _, _, _) = readDatabase true (getProjectBase projname)

            val filesym = F.fromValue goodname

            fun loop ctx project =
               (case project of
                   nil =>
                      raise (E.GeneralError (String.concat ["component ", goodname, " not found in project"]))

                 | (fullname', span) :: rest =>
                      let
                         val (path', _, basename', ext') = sunderFilename fullname'
                      in
                         if ext' = "proj" then
                            let
                               val (_, _, _, subctx) = readDatabase true (Path.join path' basename')
                            in
                               loop (Context.union ctx subctx) rest
                            end
                         else
                            let
                               val (goodname', _) = processName basename' ext'
                               val filesym' = F.fromValue goodname'
                            in
                               (case D.find database filesym' of
                                   NONE =>
                                      raise (E.SemanticError (fullname' ^ " is absent from the database", span))
      
                                 | SOME (modtime, _, deps, ectx) =>
                                      if F.eq (filesym, filesym') then
                                         (Path.join projpath fullname',
                                          ext',
                                          modtime,
                                          deps,
                                          ctx)
                                      else
                                         loop (C.union ctx ectx) rest)
                            end
                      end)

            val (fullname, ext, modtime, deps, ctx) = loop C.empty project

            val () =
               if modtime = getModTime fullname then
                  ()
               else
                  raise (E.GeneralError (fullname ^ " has changed"))

            val smlCompat =
               if ext = "iml" orelse ext = "ist" then
                  false
               else if ext = "sig" orelse ext = "sml" then
                  true
               else
                  (* If it's in the database, this shouldn't happen. *)
                  raise (Fail "impossible")

            val ctx' =
               Context.union
                  ctx
                  (Initial.basis (!Language.target) smlCompat)
         in
            (fullname, ctx', depsToList deps, smlCompat)
         end

      fun load projname =
         let
            val (_, _, _, ctx) = readDatabase true (getProjectBase projname)
         in
            ctx
         end

   end
