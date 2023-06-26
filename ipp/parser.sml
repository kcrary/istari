
(* The parser for raw programs. *)

signature PARSER =
   sig

      val parseFull : char Stream.stream -> Syntax.program
      val parseIpc : char Stream.stream -> PreContext.precontext
      val parseIncremental : Token.token Stream.stream -> Syntax.program * Token.token Stream.stream

   end


structure Parser :> PARSER =
   struct

      open Syntax
      open Span

      structure S = Stream

      fun fst (x, _) = x
      fun snd (_, x) = x

      fun identity x = x
      fun null () = []
      fun sing x = [x]
      fun pair (x, y) = [x, y]

      fun parens (l, (x, _), r) = (x, join l r)

      fun sing_w_span (x, span) = ([x], span)
      fun pair_w_span ((x, l), (y, r)) = ([x, y], join l r)
      fun cons_w_span ((x, l), (xs, r)) = (x :: xs, join l r)

      fun sing1_w_pos (x as (_, (_, r))) = ([x], r)
      fun sing2_w_pos (x as (_, _, (_, r))) = ([x], r)
      fun sing3_w_pos (x as (_, _, _, (_, r))) = ([x], r)
      fun sing4_w_pos (x as (_, _, _, _, (_, r))) = ([x], r)
      fun cons_w_pos (x, (xs, r)) = (x :: xs, r)

      val cons = Symbol.fromValue "::"
      val equal = Symbol.fromValue "="
      val times = Symbol.fromValue "*"
      val refsym = Symbol.fromValue "ref"
      val lparen = Symbol.fromValue "("
      val rparen = Symbol.fromValue ")"

      type symbol = Symbol.symbol

      structure Arg =
         struct

            datatype terminal = datatype Token.token

            type identifier = identifier
            type identifiers = identifier list
            type int_span = int * span
            type intinf_span = IntInf.int * span
            type string_span = string * span
            type char_span = char * span
            type tnumber = int * symbol * span
            type span = span

            type nothing = unit
            type longid = symbol list * span
            type longtident = symbol list * symbol * span
            type ty = ty
            type tys_pos = ty list * pos
            type tys = ty list
            type tyfields = (identifier * ty) list
            type idents = identifier list
            type longids = longid list
            type tyvarseq = pos * idents
            type pjuxta = pat juxta
            type pjuxtas_pos = pat juxta list * pos
            type pat = pat
            type pats = pat list
            type patfields = (identifier * pat) list
            type exp = exp
            type exps = exp list
            type exps_pos = exp list * pos
            type expfields = (identifier * exp) list
            type ejuxta = exp juxta
            type ejuxtas_pos = exp juxta list * pos
            type element = element
            type elements = element list
            type clause = clause
            type clauses_pos = clause list * pos
            type dec = dec
            type decs = dec list
            type funclause = identifier * pat list * ty option * exp * span
            type funclauses = identifier * (pat list * ty option * exp * span) list * pos
            type funbind = identifier * (pat list * ty option * exp * span) list * span
            type funbinds_pos = funbind list * pos
            type dconbind = dconbind
            type dconbinds_pos = dconbind list * pos
            type tybind = tybind
            type tybinds_pos = tybind list * pos
            type module = module
            type spec = spec
            type specs = spec list
            type sg = sg
            type bool = bool
            type rhselem = rhselem
            type rhselems = rhselem list
            type identopts = identifier option list
            type gdef = gdef
            type gdefs = gdef list
            type directive = directive
            type directives = directive list
            type program = program

            
            fun form_nothing () = ()
            
            val id_span = identity

            val id_ident = identity
            fun cons_ident span = (cons, span)
            fun times_ident span = (times, span)
            fun equal_ident span = (equal, span)
            fun ref_ident span = (refsym, span)
            val sing_longid = sing_w_span
            val cons_longid = cons_w_span
            val pair_longid = pair_w_span
            val id_longid = identity
            val sing_idents = sing
            val cons_idents = op ::
            val sing_longids = sing
            val cons_longids = op ::


            fun ident_ty x = (Tident x, snd x)
            fun tyvar_ty x = (Ttyvar x, snd x)
            val paren_ty = parens
            val id_ty = identity
            fun app1_ty (t, longid) = (Tapp ([t], longid), join (snd t) (snd longid))
            fun appn_ty (l, ts, longid) = (Tapp (ts, longid), join l (snd longid))

            val sing_ty_prod = sing1_w_pos
            val cons_ty_prod = cons_w_pos

            val pair_tys = pair
            val cons_tys = op ::
            val nil_tyfields = null
            fun sing_tyfields (x, t) = [(x, t)]
            fun cons_tyfields (x, t, rest) = (x, t) :: rest
            
            fun prod_ty (tys, r) =
               (case tys of
                   [] => raise (Fail "forbidden by grammar")
                 | [x] => x
                 | ((_, (l, _)) :: _) => (Tprod tys, (l, r)))

            fun arrow_ty (t1, t2) = (Tarrow (t1, t2), join (snd t1) (snd t2))


            val sing_tyvars = sing
            val cons_tyvars = op ::
            fun sing_tyvarseq (id as (_, (l, r))) = (l, [id])
            fun seq_tyvarseq ((l, _), ids) = (l, ids)


            fun wild_pat span = (Pwild, span)
            fun ident_pat x = (Pident x, snd x)
            fun constr_pat x = (Pconstr x, snd x)
            fun number_pat (n, span) = (Pnumber n, span)
            fun string_pat (str, span) = (Pstring str, span)
            fun char_pat (ch, span) = (Pchar ch, span)
            fun word_pat (n, span) = (Pword n, span)

            fun tuple_pat (l, pats, r) =
               (case pats of
                   [] => (Punit, join l r)
                 | [(x, _)] => (x, join l r)
                 | _ => (Ptuple pats, join l r))

            fun ltuple_pat (l as (_, l'), pats, r) =
               let
                  val (p, _) =
                     foldl
                        (fn (p2 as (_, (_, r')), p1) =>
                            (Ptuple [p1, p2], (l', r')))
                        (Punit, (l', l'))
                        pats
               in
                  (p, join l r)
               end

            fun list_pat (l, pats, r) = (Plist pats, join l r)
            fun atom_pjuxta (pat as (_, r)) = (Jatom pat, r)

            fun constr_pjuxta (longid, span) =
               let val e = (Pconstr (longid, span), span)
               in
                  (case longid of
                      [x] => (Jident ((x, span), e), span)
                    | _ => (Jatom e, span))
               end

            fun record_pjuxta (longid as (_, l), fields, r) = (Jatom (Papprecord (longid, fields), join l r), join l r)
            fun ref_pjuxta span = (Jatom (Pconstr ([refsym], span), span), span)

            val sing_pjuxtas = sing1_w_pos
            val cons_pjuxtas = cons_w_pos

            fun juxta_pat (juxs, r) =
               let
                  val (_, (l, _)) = hd juxs
               in
                  (Pjuxta juxs, (l, r))
               end

            fun as_pat (x as (_, l), pat) = (Pas (x, pat), join l (snd pat))
            fun annot_pat (pat, t) = (Pannot (pat, t), join (snd pat) (snd t))

            val id_pats = identity
            val nil_pats = null
            val sing_pats = sing
            val cons_pats = op ::

            fun nil_patfields () = []
            fun sing_patfields (x, pat) = [(x, pat)]
            fun ident_sing_patfields x = [(x, (Pident x, snd x))]
            fun cons_patfields (x, pat, rest) = ((x, pat) :: rest)
            fun ident_cons_patfields (x, rest) = ((x, (Pident x, snd x)) :: rest)

            fun number_exp (n, span) = (Enumber n, span)
            fun bignum_exp (n, span) = (Ebignum n, span)
            fun word_exp (n, span) = (Eword n, span)
            fun string_exp (str, span) = (Estring str, span)
            fun char_exp (ch, span) = (Echar ch, span)
            fun let_exp (l, decs, exp, r) = (Elet (decs, exp), join l r)
            fun let_seq_exp (l, decs, (exps, expsr), r) = (Elet (decs, (Eseq exps, (fst (snd (hd exps)), expsr))), join l r)

            fun tuple_exp (l, exps, r) =
               (case exps of
                   [] => (Eunit, join l r)
                 | [(x, _)] => (x, join l r)
                 | _ => (Etuple exps, join l r))

            fun list_exp (l, exps, r) = (Elist exps, join l r)
            fun seq_exp (exps, r) = (Eseq exps, (fst (snd (hd exps)), r))
            val id_exp = identity
            fun term_exp (l, elems, r) = (Eterm elems, join l r)
            fun ident_op_exp (id, span) = (Eident ([id], span), span)
            fun constr_op_exp (id, span) = (Econstr ([id], span), span)

            fun ident_ejuxta (longid, span) =
               let val e = (Eident (longid, span), span)
               in
                  (case longid of
                      [x] => (Jident ((x, span), e), span)
                    | _ => (Jatom e, span))
               end

            fun constr_ejuxta (longid, span) =
               let val e = (Econstr (longid, span), span)
               in
                  (case longid of
                      [x] => (Jident ((x, span), e), span)
                    | _ => (Jatom e, span))
               end

            fun atom_ejuxta (exp as (_, r)) = (Jatom exp, r)
            fun record_ejuxta (longid as (_, l), fields, r) = (Jatom (Eapprecord (longid, fields), join l r), join l r)
            val sing_ejuxtas = sing1_w_pos
            val cons_ejuxtas = cons_w_pos
            val term_ident = Lident
            val term_longid = Llongid
            val term_lexeme = Llexeme
            fun term_lparen sp = Llexeme (lparen, sp)
            fun term_rparen sp = Llexeme (rparen, sp)
            fun term_string x = Lstring x
            fun term_number x = Lnumber x
            val embed_element = Lembed
            val nil_elements = null
            val cons_elements = op ::

            fun juxta_exp (juxs, r) =
               let
                  val (_, (l, _)) = hd juxs
               in
                  (Ejuxta juxs, (l, r))
               end

            fun case_exp ((l, _), exp, (arms, r)) = (Ecase (exp, arms), (l, r))
            fun try_exp ((l, _), exp, (arms, r)) = (Etry (exp, arms), (l, r))
            fun handle_exp (exp, (arms, r)) = (Etry (exp, arms), (fst (snd exp), r))
            fun fn_exp ((l, _), (arms, r)) = (Elam arms, (l, r))
            fun mfn_exp (l, pats, exp) = (Elams (pats, NONE, exp), join l (snd exp))
            fun mfn_annot_exp (l, pats, ty, exp) = (Elams (pats, SOME ty, exp), join l (snd exp))

            fun cfn_exp (l as (_, l'), pats, exp as (_, r)) =
               let
                  val pat =
                     foldl
                        (fn (p2 as (_, (_, r')), p1) =>
                            (Ptuple [p1, p2], (l', r')))
                        (Punit, (l', l'))
                        pats
               in
                  (Elam [(pat, exp, (l', snd r))],
                   join l r)
               end

            fun cfn_exp_empty (l, exp) = cfn_exp (l, [], exp)

            fun annot_exp (exp, ty) = (Eannot (exp, ty), join (snd exp) (snd ty))
            fun if_exp (l, e1, e2, e3) = (Eif (e1, e2, e3), join l (snd e3))
            fun andalso_exp (e1, e2) = (Eandalso (e1, e2), join (snd e1) (snd e2))
            fun orelse_exp (e1, e2) = (Eorelse (e1, e2), join (snd e1) (snd e2))
            fun raise_exp (l, e) = (Eraise e, join l (snd e))
            val id_exps = identity
            val nil_exps = null
            val sing_exps = sing
            val cons_exps = op ::
            val nil_expfields = null
            fun sing_expfields (x, e) = [(x, e)]
            fun cons_expfields (x, e, rest) = (x, e) :: rest
            val sing_expsequence = sing1_w_pos
            val cons_expsequence = cons_w_pos


            fun form_clause (pat, exp) = (pat, exp, join (snd pat) (snd exp))
            val sing_clauses = sing2_w_pos
            val cons_clauses = cons_w_pos
            val id_match = identity


            fun val_dec (l, pat, exp) = (Dval ([], pat, exp), join l (snd exp))
            fun val_tyargs_dec (l, (_, tyargs), pat, exp) = (Dval (tyargs, pat, exp), join l (snd exp))
            fun fun_dec ((l, _), (funs, r)) = (Dfun ([], funs), (l, r))
            fun fun_tyargs_dec ((l, _), (_, tyargs), (funs, r)) = (Dfun (tyargs, funs), (l, r))
            fun do_dec (l, decs, exp) = (Ddo (decs, exp), join l (snd exp))
            fun type_dec (l, id, t) = (Dtype (nil, id, t), join l (snd t))
            fun type_args_dec (l, (_, args), id, t) = (Dtype (args, id, t), join l (snd t))
            fun datatype_dec ((l, _), (binds, r)) = (Ddatatype binds, (l, r))
            fun extension_noarg_dec (l, id) = (Dextension (id, NONE), join l (snd id))
            fun extension_dec (l, id, t) = (Dextension (id, SOME t), join l (snd t))
            fun extension_copy_dec (l, id, longid) = (Dextcopy (id, longid), join l (snd longid))
            fun open_dec (l, id) = (Dinclude id, join l (snd id))
            val nil_decs = null
            val cons_decs = op ::
            fun form_fundec (id, pats, e) = (id, pats, NONE, e, join (snd (hd pats)) (snd e))
            fun annot_fundec (id, pats, t, e) = (id, pats, SOME t, e, join (snd (hd pats)) (snd e))

            fun sing_funclauses (id, pats, t, e, span) = (id, [(pats, t, e, span)], snd span)
            
            fun cons_funclauses ((id, pats, t, e, span), (id' as (_, (namel, _)), clauses, r)) =
               if Symbol.eq (fst id, fst id') then
                  (id, (pats, t, e, span) :: clauses, r)
               else
                  raise (Error.SyntaxError ("inconsistent function name", namel))

            fun form_funbind (id as (_, (l, _)), clauses, r) = 
               (id, clauses, (l, r))

            val sing_funbinds = sing2_w_pos
            val cons_funbinds = cons_w_pos
            fun noty_dconbind id = Dcon (id, NONE, snd id)
            fun ty_dconbind (id, ty) = Dcon (id, SOME ty, join (snd id) (snd ty))
            fun record_dconbind (id, fields, r) = Record (id, fields, join (snd id) r)

            fun sing_dconbinds d =
               (case d of
                   Dcon (_, _, (_, r)) => ([d], r)
                 | Record (_, _, (_, r)) => ([d], r))

            val cons_dconbinds = cons_w_pos
            fun data_tybind (id as (_, (l, _)), (dcons, r)) = Data ([], id, dcons, (l, r))
            fun data_args_tybind ((l, args), id, (dcons, r)) = Data (args, id, dcons, (l, r))
            fun ty_tybind (id, t) = With ([], id, t, join (snd id) (snd t))
            fun ty_args_tybind ((l, args), id, t) = With (args, id, t, (l, snd (snd t)))

            fun sing_tybinds d =
               (case d of
                   Data (_, _, _, (_, r)) => ([d], r)
                 | With (_, _, _, (_, r)) => ([d], r))

            val cons_tybinds = cons_w_pos


            val identity_dec = identity
            fun structure_dec (l, id, m) = (Dmod (id, m, NONE), join l (snd m))
            fun structure_seal_dec (l, id, s, m) = (Dmod (id, m, SOME s), join l (snd m))


            fun ident_mod x = (Mident x, snd x)
            fun struct_mod (l, d, r) = (Mstruct d, join l r)
            fun app_mod (f, m, r) = (Mapp (f, m), join (snd f) r)
            fun app_alt_mod (f, dl, d, dr) = (Mappalt (f, d, join dl dr), join (snd f) dr)
            fun seal_mod (m, s) = (Mseal (m, s), join (snd m) (snd s))


            fun val_spec (l, id, t) = (Sval (id, t), join l (snd t))
            fun abstype_spec (l, id) = (Sabstype ([], id), join l (snd id))
            fun abstype_args_spec (l, (_, args), id) = (Sabstype (args, id), join l (snd id))
            fun type_spec (l, id, t) = (Stype (nil, id, t), join l (snd t))
            fun type_args_spec (l, (_, args), id, t) = (Stype (args, id, t), join l (snd t))
            fun datatype_spec ((l, _), (binds, r)) = (Sdatatype binds, (l, r))
            fun mod_spec (l, id, s) = (Smod (id, s), join l (snd s))
            fun extension_noarg_spec (l, id) = (Sextension (id, NONE), join l (snd id))
            fun extension_spec (l, id, t) = (Sextension (id, SOME t), join l (snd t))
            fun include_spec (l, id) = (Sinclude id, join l (snd id))
            val nil_specs = null
            val cons_specs = op ::


            fun ident_sig x = (Sident x, snd x)
            fun sig_sig (l, ss, r) = (Ssig ss, join l r)
            fun where_sig (s, id, t) = (Swhere (s, id, [], t), join (snd s) (snd t))
            fun where_args_sig (s, (_, args), id, t) = (Swhere (s, id, args, t), join (snd s) (snd t))

            
            fun signature_dec (l, id, s) = (Dsig (id, s), join l (snd s))
            fun functor_dec (l, id, arg, s, m) = (Dfunctor (id, arg, s, m, NONE), join l (snd m))
            fun functor_seal_dec (l, id, arg, s, s', m) = (Dfunctor (id, arg, s, m, SOME s'), join l (snd m))
            fun functor_alt_dec (l, id, sl, s, sr, m) = (Dfunctoralt (id, s, join sl sr, m, NONE), join l (snd m))
            fun functor_alt_seal_dec (l, id, sl, s, sr, s', m) = (Dfunctoralt (id, s, join sl sr, m, SOME s'), join l (snd m))


            fun bool_true () = true
            fun bool_false () = false
            fun nonterminal_rhselem id = Nonterminal (id, 0)
            fun nonterminal_level_rhselem (id, (n, _)) = Nonterminal (id, n)
            fun terminal_ident_rhselem (sym, sp) = TerminalIdent sym
            fun terminal_rhselem (sym, sp) = Terminal sym
            val nil_rhs = null
            val cons_rhs = op ::
            val nil_identopts = null
            fun cons_identopts (id, l) = SOME id :: l
            fun cons_empty_identopts l = NONE :: l
            val infix_gdef = Ginfix
            fun rule_gdef (l, id, rhs, action) = Grule (id, 0, rhs, action, join l (snd action))
            fun rule_level_gdef (l, id, (n, _), rhs, action) = Grule (id, n, rhs, action, join l (snd action))
            val reserved_gdef = Greserved
            fun start_gdef (id, l) = Gstart (id, l)
            fun default_gdef id = Gdefault id
            fun mod_gdef (id1, id2) = Gmod (id1, id2)
            fun open_gdef id = Gopen id
            fun include_gdef id = Ginclude id
            val nil_gdefs = null
            val cons_gdefs = op ::


            val id_directive = identity
            fun dec_directive d = (Vdec d, snd d)
            fun grammardef_directive (l, id, gdefs, r) = (Vgrammardef (id, gdefs), join l r)
            fun grammaron_directive (l, ids) = (Vgrammaron ids, join l (snd (List.last ids)))
            fun grammaroff_directive (l, ids) = (Vgrammaroff ids, join l (snd (List.last ids)))
            val nil_directives = null
            val cons_directives = op ::
            fun exp_directives (e as (_, sp), ds) = (Vexp e, sp) :: ds
            val id_directives = identity

            fun directives_program dirs =
               (case dirs of
                   [] =>
                      ([], (origin, origin))
   
                 | first :: _ =>
                      (dirs, join (snd first) (snd (List.last dirs))))

            fun exp_program e = ([(Vexp e, snd e)], snd e)


            (* parsing IPC *)

            structure C = PreContext
               
            type identarity = identifier * int
            type identarities = identarity list
            type item = identifier * C.class
            type items = item list
            type context = C.precontext
            type import = C.precontext

            fun eia_none id = (id, 0)
            fun eia_some (id, (arity, _)) = (id, arity)
            val sing_eias = sing
            val cons_eias = op ::

            fun list_item (id, ctx) = (id, C.LIST ctx)
            fun name_item (id, id') = (id, C.NAME id')
            val sing_items = sing
            val cons_items = op ::

            fun val_entry ids = map C.VAL ids
            fun type_entry ids = map C.TYPE ids
            fun sig_entry items = map C.SIG items
            fun struct_entry items = map C.MOD items
            fun fun_entry items = map C.FUN items

            val nil_context = null
            val cons_context = op @



            datatype parsed = 
               PROGRAM of program
             | IMPORT of import

            fun program_parsed p = PROGRAM p

            fun import_parsed imp = IMPORT imp
            

            fun tokspan tok =
               (case tok of
                   UIDENT (_, span) => span
                 | LIDENT (_, span) => span
                 | ULIDENT (_, span) => span
                 | SIDENT (_, span) => span
                 | USIDENT (_, span) => span
                 | TYVAR (_, span) => span
                 | NUMBER (_, span) => span
                 | BIGNUM (_, span) => span
                 | WORD (_, span) => span
                 | STRING (_, span) => span
                 | CHAR (_, span) => span
                 | LPAREN span => span
                 | RPAREN span => span
                 | LBRACKET span => span
                 | RBRACKET span => span
                 | LBRACE span => span
                 | RBRACE span => span
                 | NUMBER_LBRACE (_, span) => span
                 | ARROW span => span
                 | BAR span => span
                 | COLON span => span
                 | COMMA span => span
                 | DARROW span => span
                 | DOT span => span
                 | ELLIPSIS span => span
                 | EQUAL span => span
                 | PERIOD span => span
                 | PERIOD_SEP span => span
                 | SEAL span => span
                 | SEMICOLON span => span
                 | SEMICOLON_SEP span => span
                 | TIMES span => span
                 | UNDERSCORE span => span
                 | AND span => span
                 | ANDALSO span => span
                 | AS span => span
                 | BEGIN span => span
                 | CASE span => span
                 | DATATYPE span => span
                 | DO span => span
                 | ELSE span => span
                 | END span => span
                 | EXTENSION span => span
                 | FN span => span
                 | FNC span => span
                 | FNS span => span
                 | FUN span => span
                 | FUNCTOR span => span
                 | GRAMMARDEF span => span
                 | GRAMMAROFF span => span
                 | GRAMMARON span => span
                 | HANDLE span => span
                 | IF span => span
                 | IN span => span
                 | INCLUDE span => span
                 | LET span => span
                 | OF span => span
                 | OP span => span
                 | OPEN span => span
                 | ORELSE span => span
                 | RAISE span => span
                 | REF span => span
                 | SIG span => span
                 | SIGNATURE span => span
                 | STRUCT span => span
                 | STRUCTURE span => span
                 | THEN span => span
                 | TRY span => span
                 | TYPE span => span
                 | VAL span => span
                 | WHERE span => span
                 | WITH span => span
                 | WITHTYPE span => span
                 | PRODUCES span => span
                 | CURRIED span => span
                 | INFIX span => span
                 | START span => span
                 | DEFAULT span => span
                 | LEFT span => span
                 | RIGHT span => span
                 | RESERVED span => span
                 | RULE span => span
                 | TUPLED span => span
                 | ENTER_TERM span => span
                 | EXIT_TERM span => span
                 | ENTER_MAIN span => span
                 | EXIT_MAIN span => span
                 | TIDENT (_, span) => span
                 | TNUMBER (_, _, span) => span
                 | LEXEME (_, span) => span
                 | LONGTIDENT (_, span) => span
                 | EOF span => span
                 | FULL => (origin, origin)
                 | INCREMENTAL => (origin, origin)
                 | IPC => (origin, origin))

            fun error s =
               let
                  val pos =
                     (case S.front s of
                         S.Nil =>
                            (* impossible because you'll never shift past EOF *)
                            raise (Fail "impossible")

                       | S.Cons (tok, _) => fst (tokspan tok))
               in
                  raise (Error.SyntaxError ("syntax error", pos))
               end

         end

      structure ParseMain =
         ParseMainFun
         (structure Streamable = StreamStreamable
          structure Arg = Arg)

      (* CM-Yacc parsers don't have multiple entry points.  Instead, slap a
         token on the front of the stream to indicate to the parser
         what sort of code it's parsing.
      *)

      fun parseFull s =
         (case ParseMain.parse (S.eager (S.Cons (Token.FULL, Lexer.lexFull s))) of
             (Arg.PROGRAM p, s') =>
                (case S.front s' of
                    S.Cons (Token.EOF _, _) => p

                  | _ => Arg.error s')

           | _ => raise (Fail "impossible"))

      fun parseIncremental s =
         (case S.front s of
             S.Cons (Token.LBRACE span, s') => 
                (([Hardcode.enter span], span), s')

           | S.Cons (Token.RBRACE span, s') =>
                (([Hardcode.leave span], span), s')

           | S.Cons (Token.NUMBER_LBRACE (n, span), s') => 
                (([Hardcode.entern n span], span), s')

           | _ =>
                (* The normal case. *)
                (case ParseMain.parse (S.eager (S.Cons (Token.INCREMENTAL, s))) of
                    (Arg.PROGRAM (p, sp), s') =>
                       (case S.front s' of
                           S.Cons (Token.SEMICOLON_SEP sp', s'') => 
                              ((p, join sp sp'), s'')
       
                         | S.Cons (Token.PERIOD_SEP sp', s'') =>
                              (* An interaction ending with a period must be a single expression.
                                 Anything else is a syntax error.
                              *)
                              (case p of
                                  [(Vexp e, sp)] =>
                                     (([Hardcode.apply e], join sp sp'), s'')
       
                                | _ =>
                                     Arg.error s')
       
                         | S.Cons (Token.EOF _, s'') => 
                              ((p, sp), s'')

                         | _ => 
                              Arg.error s')
       
                  | _ => raise (Fail "impossible")))

      fun parseIpc s =
         (case ParseMain.parse (S.eager (S.Cons (Token.IPC, Lexer.lexIpc s))) of
             (Arg.IMPORT c, s') =>
                (case S.front s' of
                    S.Cons (Token.EOF _, _) => c

                  | _ => Arg.error s')

           | _ => raise (Fail "impossible"))

   end
