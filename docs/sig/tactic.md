# Tactic

    signature TACTIC =
       sig
          
          type goal = Judgement.judgement * Directory.directory
          type validation = Refine.validation
          type validator = validation list -> validation * validation list
          type answer = exn
    
          (* The success continuation takes the failure continuation as an argument.
             It can be used to backtrack.
          *)
    
          type 'a tacticm = 
             goal
             -> (string -> answer)                                              (* failure continuation *)
             -> (('a * goal) list * validator * (string -> answer) -> answer)   (* success continuation *)
             -> answer
    
          type tactic = Message.label tacticm
    
          datatype priority = Primary | Secondary
    
    
    
          (* control flow *)
    
          val idtac : tactic
          val idtacM : 'a -> 'a tacticm
          val fail : string -> 'a tacticm
          val cut : 'a tacticm -> 'a tacticm
          val lift : (unit -> 'a tacticm) -> 'a tacticm
          val done : 'a tacticm  (* Like fail, but without the stigma. *)
    
    
          (* combination *)
    
          val andthen : 'a tacticm -> 'b tacticm -> 'b tacticm
          val andthenl : 'a tacticm -> 'b tacticm list -> 'b tacticm
          val andthenlPad : 'a tacticm -> 'b tacticm list -> 'b tacticm -> 'b tacticm
          val andthenOn : int -> 'a tacticm -> 'a tacticm -> 'a tacticm
          val andthen1 : 'a tacticm -> 'b tacticm -> 'b tacticm
    
          val andthenM : 'a tacticm -> ('a -> 'b tacticm) -> 'b tacticm
          val andthenlM : 'a tacticm -> ('a -> 'b tacticm) list -> 'b tacticm
          val andthenlPadM : 'a tacticm -> ('a -> 'b tacticm) list -> ('a -> 'b tacticm) -> 'b tacticm
          val andthenOnM : int -> 'a tacticm -> ('a -> 'a tacticm) -> 'a tacticm
    
          val andthenFoldM :
             'a tacticm 
             -> ('a -> 'b -> 'c tacticm * 'b)
             -> ('b -> string option)
             -> 'b
             -> 'c tacticm
    
          val andthenPri : priority tacticm -> priority tacticm -> priority tacticm
          val andthenlPri : priority tacticm -> priority tacticm list -> priority tacticm
          val andthenlPadPri : priority tacticm -> priority tacticm list -> priority tacticm -> priority tacticm
    
          val andthenSeq : tactic list -> tactic
    
          val attempt : tactic -> tactic
          val attemptPri : priority tacticm -> priority tacticm
          val first : 'a tacticm list -> 'a tacticm
          val repeat : tactic -> tactic
          val repeatPri : priority tacticm -> priority tacticm
          val repeatCount : tactic -> int tacticm
          val repeatn : int -> tactic -> tactic
          val repeatnPri : int -> priority tacticm -> priority tacticm
          val orthen : 'a tacticm -> (unit -> 'a tacticm) -> 'a tacticm
    
          val ifthen : 'a tacticm -> 'b tacticm -> 'b tacticm -> 'b tacticm
          val ifthenl : 'a tacticm -> 'b tacticm list -> 'b tacticm -> 'b tacticm
          val ifthenM : 'a tacticm -> ('a -> 'b tacticm) -> 'b tacticm -> 'b tacticm
    
    
          (* direct computation *)
    
          val replaceJudgement : Judgement.judgement -> tactic
          val replaceHyp : int -> Judgement.hyp -> tactic
          val replaceConcl : Term.term -> tactic
    
    
          (* miscellaneous *)
    
          val withgoal : (goal -> 'a tacticm) -> 'a tacticm
          val withdir : (Directory.directory -> 'a tacticm) -> 'a tacticm
          val withidir : (Directory.idirectory -> 'a tacticm) -> 'a tacticm
          val withterm : ETerm.eterm -> (Term.term -> 'a tacticm) -> 'a tacticm
          val withHeadConst : string -> (Constant.constant -> 'a tacticm) -> 'a tacticm
    
          val setFailure : string -> 'a tacticm -> 'a tacticm
          val transformFailure : (string -> string) -> 'a tacticm -> 'a tacticm
    
          exception Tryf of string
          val tryf : (unit -> 'a) -> ('a -> 'b tacticm) -> 'b tacticm
    
          val sideEffect : (unit -> unit) -> tactic
          val displayTac : string -> tactic
    
    
          (* primitive actions *)
    
          val chdir : Directory.directory -> tactic
          val cast : Judgement.judgement -> Refine.validation -> 'a tacticm
          val execute : goal -> tactic -> (Refine.validation, string) Sum.sum
    
    
          val >> : 'a tacticm -> 'b tacticm -> 'b tacticm                           (* andthen *)
          val >>> : 'a tacticm -> 'b tacticm list -> 'b tacticm                     (* andthenl *)
          val >>+ : 'a tacticm -> 'b tacticm -> 'b tacticm                          (* andthen1 *)
          val >>= : 'a tacticm -> ('a -> 'b tacticm) -> 'b tacticm                  (* andthenM *)
          val >>>= : 'a tacticm -> ('a -> 'b tacticm) list -> 'b tacticm            (* andthenlM *)
          val >>! : priority tacticm -> priority tacticm -> priority tacticm        (* andthenPri *)
          val >>>! : priority tacticm -> priority tacticm list -> priority tacticm  (* andthenlPri *)
    
       end
