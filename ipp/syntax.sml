
structure Syntax =
   struct

      type symbol = Symbol.symbol
      type span = Span.span
      type identifier = symbol * span
      type longid = symbol list * span  (* nonnil *)

      datatype ty_ =
         Tident of longid
       | Ttyvar of identifier
       | Tapp of ty list * longid  (* nonnil *)
       | Tprod of ty list          (* length >= 2 *)
       | Tarrow of ty * ty

      withtype ty = ty_ * span

      datatype 'a juxta_ =
         Jident of identifier * 'a
       | Jatom of 'a

      type 'a juxta = 'a juxta_ * span

      datatype pat_ =
         Pwild
       | Punit
       | Pident of identifier
       | Pconstr of longid
       | Pnumber of int
       | Pstring of string
       | Pchar of char
       | Pword of int
       | Ptuple of pat list  (* length >= 2 *)
       | Plist of pat list
       | Papp of longid * pat
       | Papprecord of longid * (identifier * pat) list
       | Pref of pat
       | Pas of identifier * pat
       | Pannot of pat * ty

       | Pjuxta of pat juxta list

      withtype pat = pat_ * span

      datatype exp_ =
         Eunit
       | Eident of longid
       | Econstr of longid
       | Enumber of int
       | Ebignum of IntInf.int
       | Eword of int
       | Estring of string
       | Echar of char
       | Elet of dec list * exp
       | Etuple of exp list  (* length >= 2 *)
       | Elist of exp list
       | Eapp of exp * exp
       | Eapprecord of longid * (identifier * exp) list
       | Ecase of exp * clause list
       | Etry of exp * clause list
       | Elam of clause list
       | Elams of pat list * ty option * exp
       | Eannot of exp * ty
       | Eif of exp * exp * exp
       | Eseq of exp list  (* length => 2 *)
       | Eandalso of exp * exp
       | Eorelse of exp * exp
       | Eraise of exp

       | Ejuxta of exp juxta list
       | Eterm of element list

      (* Distinguish idents, longids, and lexemes because some built-ins distinguish them. *)
      and element =
         Lident of identifier
       | Llongid of longid
       | Llexeme of identifier
       | Lstring of string * span
       | Lnumber of int * symbol * span
       | Lembed of exp

      and dec_ =
         Dval of identifier list * pat * exp
       | Dfun of identifier list * (identifier * (pat list * ty option * exp * span) list * span) list
       | Ddo of pat * exp
       | Dtype of identifier list * identifier * ty
       | Ddatatype of tybind list
       | Dextension of identifier * ty option
       | Dextcopy of identifier * longid
       | Dinclude of longid
       | Dmod of identifier * module * sg option
       | Dfunctor of identifier * identifier * sg * module * sg option
       | Dfunctoralt of identifier * spec list * span * module * sg option
       | Dsig of identifier * sg

      and dconbind =
         Dcon of identifier * ty option * span
       | Record of identifier * (identifier * ty) list * span

      and tybind =
         Data of identifier list * identifier * dconbind list * span
       | With of identifier list * identifier * ty * span

      and module_ =
         Mident of longid
       | Mstruct of dec list
       | Mapp of identifier * module
       | Mappalt of identifier * dec list * span
       | Mseal of module * sg

      and spec_ =
         Sval of identifier * ty
       | Sabstype of identifier list * identifier
       | Stype of identifier list * identifier * ty
       | Sdatatype of tybind list
       | Smod of identifier * sg
       | Sextension of identifier * ty option
       | Sinclude of identifier

      and sg_ =
         Sident of identifier
       | Ssig of spec list
       | Swhere of sg * longid * identifier list * ty

      withtype exp = exp_ * span
      and clause = pat * exp * span
      and dec = dec_ * span
      and module = module_ * span
      and spec = spec_ * span
      and sg = sg_ * span

      datatype rhselem =
         Terminal of symbol  (* matches Llexemes *)
       | TerminalIdent of symbol  (* matches Lidents *)
       | Nonterminal of identifier * int

      datatype gdef =
         Ginfix of bool * bool * (int * span) * identifier list  (* 1st bool => left, 2nd bool => curried *)
       | Grule of identifier * int * rhselem list * longid * span
       | Greserved of identifier list * identifier
       | Gstart of identifier * identifier option list
       | Gdefault of identifier
       | Gmod of identifier * longid
       | Gopen of longid
       | Ginclude of identifier

      datatype directive_ =
         Vdec of dec
       | Vexp of exp
       | Vgrammardef of identifier * gdef list
       | Vgrammaron of identifier list
       | Vgrammaroff of identifier list
       | Vnull

      type directive = directive_ * span

      type program = directive list * span

   end
