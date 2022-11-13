# Directory

    signature DIRECTORY =
       sig

          type symbol = Symbol.symbol

          type directory   (* for input & output *)
          type idirectory  (* for input only *)
          type set         (* for tracking sets of variables in use and generating fresh ones *)

          exception Unbound of symbol
          exception Shadow of symbol


          (* Shadowing is permitted. *)
          val idir                : directory -> idirectory
          val iempty              : idirectory
          val ibind0              : idirectory -> idirectory
          val ibind               : idirectory -> symbol -> idirectory
          val ibindh              : idirectory -> symbol option -> idirectory
          val ibinds              : idirectory -> symbol list -> idirectory
          val ibindhs             : idirectory -> symbol option list -> idirectory

          (* Signals Shadow or returns NONE if an identifier is shadowed. *)
          val empty               : directory
          val bind0               : directory -> directory
          val bind0s              : directory -> int -> directory
          val bind                : directory -> symbol -> directory
          val bindOpt             : directory -> symbol -> directory option
          val bindh               : directory -> symbol option -> directory
          val insistAndBind       : directory -> symbol option -> symbol * directory
          val insistAndBindOpt    : directory -> symbol option -> (symbol * directory) option
          val binds               : directory -> symbol list -> directory
          val bindhs              : directory -> symbol option list -> directory
          val literal             : symbol list -> directory
          val literalStr          : string list -> directory

          (* If the binding would shadow an identifier, produces an alternate instead. *)
          val fresh               : directory -> symbol
          val vary                : directory -> symbol -> symbol
          val varyAndBind         : directory -> symbol option -> symbol * directory
          val freshAndBind        : directory -> symbol * directory
          val bindVary            : directory -> symbol option -> directory
          val bindsVary           : directory -> symbol option list -> directory



          (* Signals Unbound if identifier is not in the directory
             (and not a constant either, when appropriate).
          *)
          datatype head = Hvar of int | Hconst of Constant.constant
          val lookupVar           : idirectory -> symbol -> int
          val lookupVarOpt        : idirectory -> symbol -> int option
          val lookup              : idirectory -> symbol -> head
          val lookupOpt           : idirectory -> symbol -> head option
          val lookupLong          : idirectory -> symbol list -> head
          val lookupLongOpt       : idirectory -> symbol list -> head option

          (* raises Invalid or returns NONE if the index is out of range *)
          val name                : directory -> int -> symbol
          val nameOpt             : directory -> int -> symbol option

          val isize               : idirectory -> int
          val size                : directory -> int


          val expose              : directory -> symbol * directory
          val exposeOpt           : directory -> (symbol * directory) option
          val hd                  : directory -> symbol
          val tl                  : directory -> directory
          val toList              : directory -> symbol list

          (* the last n symbols in the directory, with the oldest first *)
          val suffix              : directory -> int -> symbol list
          val suffixOpt           : directory -> int -> symbol list option

          (* peels n bindings off the directory *)
          val shift               : directory -> int -> directory
          val shiftOpt            : directory -> int -> directory option

          (* suffix and shift combined *)
          val split               : directory -> int -> symbol list * directory
          val splitOpt            : directory -> int -> (symbol list * directory) option



          val set                 : directory -> set
          val freshSet            : set -> symbol
          val varySet             : set -> symbol -> symbol
          val bindVarySet         : set -> symbol option -> set
          val freshAndBindSet     : set -> symbol * set
          val varyAndBindSet      : set -> symbol option -> symbol * set
          val insistAndBindSet    : set -> symbol option -> symbol * set
          val insistAndBindSetOpt : set -> symbol option -> (symbol * set) option
          val removeSet           : set -> symbol -> set 

       end
