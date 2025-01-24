# Registry

The registry provides a mechanism for including Istari data structures
in an Istari file.  Most data types can be stored, but, significantly,
nothing involving ML code, which includes functions and tactics.

A value of type `t` is stored using a *key* with type `t key`.  Keys
are constructed using a collection of combinators, one for each type
operator.

To write a value `x` of type `int * term` into the registry using the
name `bar`, one would say:

    Registry.write 
       (Symbol.fromValue "bar") 
       (Registry.pair Registry.int Registry.term)
       x

With the customized parser, this can be rendered more conveniently:

    Registry.write (parseIdent /bar/) (parseRegistryKey /int * term/) x

Using the pervasive function `writeRegistry`, one can write it even
more briefly:

    writeRegistry /bar/ /int * term/ x

If the current module is `Foo` when an entry is written to `bar`, it
will appear in the registry under the name `Foo.bar`.  It will use
that name immediately, even before the `Foo` module is closed.

To read that same value, one would say:

    Registry.read
       (map Symbol.fromValue ["Foo", "bar"])
       (Registry.pair Registry.int Registry.term)

or:

    Registry.read (parseLongident /Foo.bar/) (parseRegistryKey /int * term/)

or just:

    readRegistry /Foo.bar/ /int * term/

As a practical example, the `notb_tru` reduction (with type
`Reduction.ureduction`) is obtained by:

    val notb_tru = readRegistry /Bool.notb_tru/ /ureduction/

Here, `Registry.ureduction` (the result of parsing `/ureduction/`)
has the type `Reduction.ureduction Registry.key`, so `notb_tru` will
have the type `Reduction.ureduction`.

The key parser has a special syntax for keys for [collapsed
tuples](iml.html#collapsed-tuples).  To construct the key for 
`((unit * bool) * int) * constant`, one can write 
`\[bool int constant]\`.

The full interface for the registry is:

    signature REGISTRY =
       sig
    
          type 'a key
    
          exception Registry of string
    
          val write  : Symbol.symbol -> 'a key -> 'a -> unit
          val read   : Symbol.symbol list -> 'a key -> 'a
          val delete : Symbol.symbol list -> unit
    
          val unit   : unit key
          val bool   : bool key
          val int    : int key
          val intInf : IntInf.int key
          val string : string key
    
          val symbol      : Symbol.symbol key
          val constant    : Constant.constant key
          val term        : Term.term key
          val reduction   : Reduction.reduction key
          val ureduction  : Reduction.ureduction key
    
          val list    : 'a key -> 'a list key
          val option  : 'a key -> 'a option key
          val vector  : 'a key -> 'a Vector.vector key
          val seq     : 'a key -> 'a Seq.seq key
    
          val pair    : 'a key -> 'b key -> ('a * 'b) key
          val tuple2  : 'a key -> 'b key -> ('a * 'b) key  (* alias for pair *)
          val tuple3  : 'a key -> 'b key -> 'c key -> ('a * 'b * 'c) key
          val tuple4  : 'a key -> 'b key -> 'c key -> 'd key -> ('a * 'b * 'c * 'd) key
          val tuple5  : 'a key -> 'b key -> 'c key -> 'd key -> 'e key -> ('a * 'b * 'c * 'd * 'e) key
          val tuple6  : 'a key -> 'b key -> 'c key -> 'd key -> 'e key -> 'f key -> ('a * 'b * 'c * 'd * 'e * 'f) key
          val tuple7  : 'a key -> 'b key -> 'c key -> 'd key -> 'e key -> 'f key -> 'g key -> ('a * 'b * 'c * 'd * 'e * 'f * 'g) key
          val tuple8  : 'a key -> 'b key -> 'c key -> 'd key -> 'e key -> 'f key -> 'g key -> 'h key -> ('a * 'b * 'c * 'd * 'e * 'f * 'g * 'h) key
          val tuple9  : 'a key -> 'b key -> 'c key -> 'd key -> 'e key -> 'f key -> 'g key -> 'h key -> 'i key -> ('a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i) key
          val tuple10 : 'a key -> 'b key -> 'c key -> 'd key -> 'e key -> 'f key -> 'g key -> 'h key -> 'i key -> 'j key -> ('a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j) key
    
       end

The `Registry` exception is raised in various error conditions, including:

- Reading or deleting an entry that is not present.

- Reading an entry with the wrong key.

- Writing to a name that is already present.
