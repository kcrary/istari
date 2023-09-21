# IML Pervasives

    datatype bool = true | false
    type int
    type string
    type char
    datatype 'a list = nil | (::) of 'a * 'a list
    datatype 'a option = NONE | SOME of 'a
    type 'a ref
    type exn
    type unit
    datatype order = LESS | EQUAL | GREATER
    
    val not : bool -> bool
    val (~) : int -> int
    val (+) : int -> int -> int
    val (-) : int -> int -> int
    val (*) : int -> int -> int
    val div : int -> int -> int
    val rem : int -> int -> int
    val (=) : int -> int -> bool
    val (<>) : int -> int -> bool
    val (<) : int -> int -> bool
    val (>) : int -> int -> bool
    val (<=) : int -> int -> bool
    val (>=) : int -> int -> bool
    val (^) : string -> string -> string
    val (=$) : string -> string -> bool
    val (=#) : char -> char -> bool
    val (@) : 'a list -> 'a list -> 'a list
    val foldl : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
    val foldr : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
    val map : ('a -> 'b) -> 'a list -> 'b list
    val app : ('a -> unit) -> 'a list -> unit
    val ref : 'a -> 'a ref
    val (!) : 'a ref -> 'a
    val (:=) : 'a ref -> 'a -> unit
    val ($) : ('a -> 'b) -> 'a -> 'b
    val fst : 'a * 'b -> 'a
    val snd : 'a * 'b -> 'b
    val n1of3 : 'a * 'b * 'c -> 'a
    val n2of3 : 'a * 'b * 'c -> 'b
    val n3of3 : 'a * 'b * 'c -> 'c
    val print : string -> unit

    exception Div
    exception Fail of string
    exception Invalid of string

- `val ($) : ('a -> 'b) -> 'a -> 'b`

  A low-precedence infix operator for function application.

- `val (=) : int -> int -> bool`

  Equivalent to `Int.=`.

- `val (=$) : string -> string -> bool`

  Equivalent to `String.=`.

- `val (=#) : char -> char -> bool`

  Equivalent to `Char.=`.



#### Operator precedence

| operators                            | precedence | associativity | mode    |
| ------------------------------------ | ---------- | ------------- | ------- |
| `$`                                  | 0          | right         | curried |
| `:=`                                 | 3          | left          | curried |
| `=` `<>` `<=` `<` `>=` `>` `=$` `=#` | 4          | left          | curried |
| `@`                                  | 5          | right         | curried |
| `::`                                 | 5          | right         | tupled  |
| `+` `-` `^`                          | 6          | left          | curried |
| `*` `div` `rem`                      | 7          | left          | curried |

