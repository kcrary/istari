
signature PARSER =
   sig
      
      exception SyntaxError of Token.pos

      val parse : char Stream.stream -> Syntax.clause list

   end


structure Parser :> PARSER =
   struct

      exception SyntaxError = Lexer.SyntaxError

      open Syntax

      fun identity x = x
      fun null () = []
      val cons = op ::
      fun sing x = [x]

      val tosym = Symbol.fromValue

      val eqConst = Const (tosym "eq")
      val eqtpConst = Const (tosym "eqtp")
      val istpConst = Const (tosym "istp")
      val ofConst = Const (tosym "of")
      val subtypeConst = Const (tosym "subtype")

      val ivar = Metavar (tosym "I", [])
      val ki = App (Const (tosym "kind"), ivar)
      val ui = App (Const (tosym "univ"), ivar)
      
      structure Arg =
         struct

            datatype terminal = datatype Token.token

            type symbol_pos = symbol * Token.pos
            type pos = Token.pos
            type idents = symbol list
            type sub = term * symbol
            type subs = sub list
            type term = term
            type class = class
            type hyp = hyp
            type hyps = hyp list
            type context = bool * hyps
            type ccontext = hyps
            type pcontext = bool * hyps * subs option
            type rhs = term * symbol option
            type premise = bool * hyp list * term * symbol option
            type lpremise = bool * hyp list * subs option * term * symbol option
            type premises = premise list
            type lpremises = lpremise list
            type concl = term * term
            type lconcl = hyps * term * term
            type rule = rule
            type lrule = lrule
            type clause = clause
            type clauses = clause list

            fun sing_idents (id, _) = [id]
            fun cons_idents ((id, _), l) = id :: l

            fun make_sub (m, (x, _)) = (m, x)

            val sing_subs = sing
            val cons_subs = cons
            
            val id_term = identity
            fun const_term (id, _) = Const id
            fun var_term (id, _) = Var id
            fun metavar_term (id, _) = Metavar (id, [])
            fun metavar_subs_term ((id, _), s) = Metavar (id, s)
            val pair_term = Pair
            fun triv_term () = Triv
            fun ki_term () = ki
            fun ui_term () = ui

            val app_term = App
            val pi1_term = Pi1
            val pi2_term = Pi2
            val prev_term = Prev
            val next_term = Next

            fun fn_term (ids, m) = List.foldr Lam m ids
            fun bind_term ((const, _), (var, _), a, b) = App (App (Const const, a), Lam (var, b))
            fun equal_term (m, n, a) = App (App (App (eqConst, a), m), n)
            fun of_term (m, a) = App (App (ofConst, a), m)
            fun eqtp_term (a, b) = App (App (eqtpConst, a), b)
            fun istp_term a = App (istpConst, a)
            fun subtype_term (a, b) = App (App (subtypeConst, a), b)

            val tm_class = Tm
            val tml_class = Tml
            val tmh_class = Tmh
            fun tp_class () = Tp
            fun tpl_class () = Tpl
            fun tph_class () = Tph

            fun make_hyp ((id, _), cl) = (id, cl)

            val nil_hyps = null
            val cons_hyps = cons
            val sing_hyps = sing
            val id_hyps = identity

            fun promote_context h = (true, h)
            fun ordinary_context h = (false, h)
            
            val make_ccontext = identity

            fun long_pcontext (p, hs) = (p, hs, SOME [])
            fun longsub_pcontext ((p, hs), s) = (p, hs, SOME s)
            fun short_pcontext (p, hs) = (p, hs, NONE)
            
            fun ext_rhs (m, (id, _)) = (m, SOME id)
            fun noext_rhs m = (m, NONE)

            fun make_premise ((p, hs), (m, ext)) = (p, hs, m, ext)

            fun make_lpremise ((p, hs, so), (m, ext)) = (p, hs, so, m, ext)

            val nil_premises = null
            val cons_premises = cons
            
            val nil_lpremises = null
            val cons_lpremises = cons
            
            fun ext_concl (m, n) = (m, n)
            fun noext_concl m = (m, Triv)

            fun ext_lconcl (hs, m, n) = (hs, m, n)
            fun noext_lconcl (hs, m) = (hs, m, Triv)

            fun make_rule ((m, ext), ps) = (ps, m, ext)

            fun make_lrule ((hs, m, ext), ps) = (ps, hs, m, ext)

            fun rule_clause ((name, _), rule) = Rule (name, rule)
            fun lrule_clause ((name, _), rule) = LRule (name, rule)

            val nil_clauses = null
            val cons_clauses = cons

            fun tokpos tok =
               (case tok of
                   UIDENT (_, pos) => pos
                 | LIDENT (_, pos) => pos
                 | PI1 pos => pos
                 | PI2 pos => pos
                 | PREV pos => pos
                 | LPAREN pos => pos
                 | RPAREN pos => pos
                 | LBRACKET pos => pos
                 | RBRACKET pos => pos
                 | LBRACE pos => pos
                 | RBRACE pos => pos
                 | COLON pos => pos
                 | COMMA pos => pos
                 | DOLLAR pos => pos
                 | DOT pos => pos
                 | ELLIPSIS pos => pos
                 | EQUAL pos => pos
                 | IF pos => pos
                 | SEMICOLON pos => pos
                 | SLASH pos => pos
                 | SUBTYPE pos => pos
                 | TURNSTILE pos => pos
                 | DEMOTE pos => pos
                 | EXT pos => pos
                 | FN pos => pos
                 | HIDE pos => pos
                 | LRULE pos => pos
                 | NEXT pos => pos
                 | PROMOTE pos => pos
                 | RULE pos => pos
                 | TYPE pos => pos
                 | KI pos => pos
                 | UI pos => pos
                 | EOF pos => pos)

            fun error s =
               let
                  val pos =
                     (case Stream.front s of
                         Stream.Nil =>
                            (* impossible because you'll never shift past EOF *)
                            raise (Fail "impossible")

                       | Stream.Cons (tok, _) => tokpos tok)
               in
                  raise (SyntaxError pos)
               end

         end

      structure ParseMain =
         ParseMainFun (structure Streamable = StreamStreamable
                       structure Arg = Arg)


      fun parse s =
         let
            val (clauses, _) = ParseMain.parse (Lexer.lex s)
         in
            clauses
         end

   end
