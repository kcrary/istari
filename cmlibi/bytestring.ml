
open Bytestring_sig;;

module Bytestring : BYTESTRING =
   struct

      type nonrec string = string
      type byte = Word8.word
      type char = byte

      let maxSize = Sys.max_string_length

      let size = String.length

      let sub (str, n) = Word8.fromInt (Char.code (String.get str n))

      let extract (str, i, leno) =
         String.sub str i (match leno with None -> String.length str - i | Some len -> len)

      let substring (str, i, len) =
         String.sub str i len

      let isEmpty str = String.length str = 0

      let concat = String.concat ""

      let null = ""

      let str w = String.make 1 (Char.chr (Word8.toInt w))

      let toByte ch = Word8.fromInt (Char.code ch)
      let toChar w = Char.chr (Word8.toInt w)

      let implode l = Stringbasis.implode (List.map toChar l)

      let explode str = List.map toByte (Stringbasis.explode str)

      let map f str = String.map (fun ch -> toChar (f (toByte ch))) str

      let map2 f (str1, str2) =
         if String.length str1 <> String.length str2 then
            raise (Basis.General.Invalid "unequal lengths")
         else
            String.init
               (String.length str1)
               (fun i -> toChar (f (toByte (String.get str1 i), toByte (String.get str2 i))))

      let rev str =
         let len = String.length str
         in
            String.init len (fun i -> String.get str (len-1-i))

      let eq (str, str') = String.equal str str'

      let compare (str, str') =
         let z = String.compare str str'
         in
            if z = 0 then
               Order.EQUAL
            else if z < 0 then
               Order.LESS
            else
               Order.GREATER
            
      let fromString x = x

      let toString x = x
            
      exception HexDigit
         
      let hexdigit ch =
         let i = Char.code ch
         in
            if Char.code '0' <= i && i <= Char.code '9' then
               i - Char.code '0'
            else if Char.code 'A' <= i && i <= Char.code 'F' then
               i - Char.code 'A' + 10
            else if Char.code 'a' <= i && i <= Char.code 'f' then
               i - Char.code 'a' + 10
            else
               raise HexDigit

      let fromStringHex str =
         let len = String.length str
         in
         let rec loop acc i =
            if i = len then
               Some (Stringbasis.implode (List.rev acc))
            else if i + 2 > len then
               None
            else
               let b0 = hexdigit (String.get str i)
               in
               let b1 = hexdigit (String.get str (i+1))
               in
                  loop (Char.chr (b0 * 16 + b1) :: acc) (i+2)
         in
            try
               loop [] 0
            with
            HexDigit -> None

      let ch0 = Char.code '0'
      let cha = Char.code 'a'

      let nibblestr n =
         if n <= 9 then
            String.make 1 (Char.chr (n + ch0))
         else
            String.make 1 (Char.chr (n + cha))

      let toStringHex' sep s =
         String.concat sep
            (List.init 
                (String.length s)
                (fun i ->
                    let b = Char.code (String.get s i)
                    in
                       nibblestr (b lsr 4) ^ nibblestr (b land 15)))

      let toStringHex = toStringHex' ""

      let (^) (str1, str2) = str1 ^ str2

      let output = Basis.BinIO.outputString

   end
