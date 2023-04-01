
module type BOOL = Basis_sig.BOOL
module type INTEGER = Basis_sig.INTEGER
module type INT_INF = Basis_sig.INT_INF
module type WORD = Basis_sig.WORD
module type STRING = Basis_sig.STRING
module type CHAR = Basis_sig.CHAR
module type LIST = Basis_sig.LIST
module type LIST_PAIR = Basis_sig.LIST_PAIR
module type OPTION = Basis_sig.OPTION
module type ARRAY = Basis_sig.ARRAY
module type IO = Basis_sig.IO
module type TEXT_IO = Basis_sig.TEXT_IO
module type BIN_IO = Basis_sig.BIN_IO
module type GENERAL = Basis_sig.GENERAL
module type CONT = Basis_sig.CONT

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
module IO : IO
module TextIO : TEXT_IO

module BinIO :
   sig
      include BIN_IO

      (* exposed to linked code only, so that byte strings can be written efficiently *)
      val outputString : outstream -> string -> unit
   end

module General : GENERAL
module Cont : CONT
