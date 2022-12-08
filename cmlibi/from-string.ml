
open From_string_sig ;;

module FromString : FROM_STRING =
   struct

      let toIntM = int_of_string_opt

      let toInt str =
         let str' =
            if String.length str = 0 then
               ""
            else if String.get str 0 = '~' then
               "-" ^ String.sub str 1 (String.length str - 1)
            else
               str
         in
            int_of_string_opt str'
         
      let toIntInfM str = 
         try
            Some (Z.of_string str)
         with
            Invalid_argument _ -> None

      let toIntInf str =
         let str' =
            if String.length str = 0 then
               ""
            else if String.get str 0 = '~' then
               "-" ^ String.sub str 1 (String.length str - 1)
            else
               str
         in
            toIntInfM str'
         
      let toWord8 str =
         (match int_of_string_opt str with
             None -> None

           | Some n ->
                if n < 0 || n > 255 then
                   None
                else
                   Some (Word8.fromInt n))

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

      let rec stringToIntHex str i max acc =
         if i = max then
            acc
         else
            stringToIntHex str (i+1) max (acc * 16 + hexdigit (String.get str i))

      let toWord8Hex str =
         (try
             let n = stringToIntHex str 0 (String.length str) 0
             in
                if n < 0 || n > 255 then
                   None
                else
                   Some (Word8.fromInt n)
          with
             HexDigit -> None)

   end
