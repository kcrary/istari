# Int

    signature INTEGER =
       sig

          type int
    
          val minInt : int option
          val maxInt : int option
    
          val ~ : int -> int
          val (+) : int -> int -> int
          val (-) : int -> int -> int
          val (*) : int -> int -> int
          val div : int -> int -> int
          val rem : int -> int -> int
          val min : int -> int -> int
          val max : int -> int -> int
          val abs : int -> int

          val divmod : int -> int -> int * int
    
          val (=) : int -> int -> bool
          val (<>) : int -> int -> bool
          val (<) : int -> int -> bool
          val (>) : int -> int -> bool
          val (<=) : int -> int -> bool
          val (>=) : int -> int -> bool
          val compare : int -> int -> order
    
          val toString : int -> string
          val toStringStd : int -> string
          val toInt : int -> Int.int
          val fromInt : Int.int -> int

          val natrecUp : (int -> 'a -> 'a) -> 'a -> int -> 'a
          val natrecDown : (int -> 'a -> 'a) -> 'a -> int -> 'a

       end
    
    structure Int : INTEGER where type int = Pervasive.int

- `minInt : int option`

  The lowest representable int, if such exists.

- `maxInt : int option`

  The highest representable int, if such exists.

- `div : int -> int -> int`

  Rounds toward zero (the usual behavior of hardware division).

- `rem : int -> int -> int`

  Given `x` and `y`, returns the value `r` such that `x div y * y + r = x`.

- `divmod : int -> int -> int * int`

  Given `x` and `y`, returns `(q, r)` such that `q * y + r = x` and 
  `0 <= r < abs(y)`.  Thus `q` is not necessarily `x div y` and `r` is
  not necessarily `x rem y`.

- `toString : int -> string`

  Prints negative numbers using IML notation (*e.g.,* `~12`).

- `toStringStd : int -> string`

  Prints negative numbers using standard notation (*e.g.,* `-12`).

- `natrecUp : (int -> 'a -> 'a) -> 'a -> int -> 'a`

  Iterates upward.  Given `f`, `x`, and nonnegative `n`, returns `f (n-1) (... f 0 x ...)`.

- `natrecDown : (int -> 'a -> 'a) -> 'a -> int -> 'a`

  Iterates downward.  Given `f`, `x`, and nonnegative `n`, returns `f 0 (... f (n-1) x ...)`.

