
module type BOOL = Smlbasis_sig.BOOL
module type INTEGER = Smlbasis_sig.INTEGER
module type INT_INF = Smlbasis_sig.INT_INF
module type WORD = Smlbasis_sig.WORD
module type STRING = Smlbasis_sig.STRING
module type CHAR = Smlbasis_sig.CHAR
module type LIST = Smlbasis_sig.LIST
module type LIST_PAIR = Smlbasis_sig.LIST_PAIR
module type OPTION = Smlbasis_sig.OPTION
module type ARRAY = Smlbasis_sig.ARRAY
module type VECTOR = Smlbasis_sig.VECTOR
module type MONO_ARRAY = Smlbasis_sig.MONO_ARRAY
module type MONO_ARRAY_SLICE = Smlbasis_sig.MONO_ARRAY_SLICE
module type IO = Smlbasis_sig.IO
module type TEXT_IO = Smlbasis_sig.TEXT_IO
module type BIN_IO = Smlbasis_sig.BIN_IO
module type GENERAL = Smlbasis_sig.GENERAL

module Bool : BOOL with type bool = bool
module Int : INTEGER with type int = int
module IntInf : INT_INF with type int = Z.t
module Word : WORD with type word = Word62.word
module LargeWord : WORD with type word = Word64.word
module Word8 : WORD with type word = Word8.word
module Word32 : WORD with type word = Word32.word
module Word64 : WORD with type word = Word64.word
module String : STRING with type string = string
module Char : CHAR with type char = char
module List : LIST with type 'a list = 'a list
module ListPair : LIST_PAIR
module Option : OPTION with type 'a option = 'a option
module Array : ARRAY with type 'a array = 'a array
module Vector : VECTOR with type 'a vector = 'a Basis.Vector.vector
module Word8Array : MONO_ARRAY with type elem = Word8.word with type array = Word8.word array
module Word8ArraySlice : MONO_ARRAY_SLICE with type elem = Word8.word with type array = Word8.word array with type slice = (Word8.word array * int * int)
module IO : IO
module TextIO : TEXT_IO with type instream = Basis.TextIO.instream with type outstream = Basis.TextIO.outstream
module BinIO : BIN_IO with type instream = Basis.BinIO.instream with type outstream = Basis.BinIO.outstream
module General : GENERAL

val s__e : 'a * 'a -> bool
val s__LG : 'a * 'a -> bool
val eq : 'a -> 'a -> bool
val neq : 'a -> 'a -> bool
