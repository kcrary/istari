# General

    signature GENERAL =
       sig
    
          datatype order = LESS | EQUAL | GREATER = Pervasive.order
          type exn = Pervasive.exn
          type unit = Pervasive.unit
       
          val ! : 'a ref -> 'a
          val (:=) : 'a ref -> 'a -> unit 
          val ($) : ('a -> 'b) -> 'a -> 'b
    
          val fst : 'a * 'b -> 'a
          val snd : 'a * 'b -> 'b
          val n1of3 : 'a * 'b * 'c -> 'a
          val n2of3 : 'a * 'b * 'c -> 'b
          val n3of3 : 'a * 'b * 'c -> 'c
    
          exception Div
          exception Fail of string
          exception Invalid of string
    
          exception Subscript
    
       end
    
    structure General : GENERAL
    
- `val ($) : ('a -> 'b) -> 'a -> 'b`

  Function application.

- `exception Invalid`

  The SML Basis's exceptions `Chr`, `Size`, and `Subscript` all are replaced by`Invalid`.
    
  The SML Basis's exceptions `Bind`, `Match`, and `Overflow` are still used, but cannot be handled.

- `exception Subscript`

  This is used only for interfacing with code using the SML basis.
  The IML basis does not raise `Subscript`.

