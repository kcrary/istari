
(* Ported from CMlib *)

include Path_sig


module Path : PATH =
   struct

      exception Path

      let explode = String.split_on_char '/' 
      
      let implode = String.concat "/"


      let rec canonizeLoop acc path =
         (match path with
             ".." :: rest ->
                (match acc with
                    [] ->
                       canonizeLoop (".." :: acc) rest

                  | ".." :: _ ->
                       canonizeLoop (".." :: acc) rest

                  | "" :: _ ->
                       (* can't back up past the root *)
                       raise Path

                  | _ :: restacc ->
                       canonizeLoop restacc rest)

           | [] -> List.rev acc
             
           | [""] ->
                (* trailing slash *)
                List.rev acc

           | "." :: _ -> 
                (* can't have . in the middle of a path *)
                raise Path

           | "" :: _ ->
                (* can't have an empty directory name *)
                raise Path

           | name :: rest ->
                canonizeLoop (name :: acc) rest)

      let canonizeArcs path =
         (match path with
             [] -> raise Path
             
           | ["."] -> ["."]
           | ["."; ""] -> ["."]

           | "." :: rest -> canonizeLoop [] rest

           | [""; ""] ->
                (* root *)
                [""; ""]

           | "" :: rest ->
                (* absolute path *)
                canonizeLoop [""] rest

           | path -> canonizeLoop [] path)

      let canonize pathstr = implode (canonizeArcs (explode pathstr))


      let isAbsolute path =
         (try
             String.get path 0 = '/'
          with 
             Invalid_argument _ -> raise Path)

      let isRelative path =
         (try
             String.get path 0 <> '/'
          with 
             Invalid_argument _ -> raise Path)

      let hasPath name =
         let len = String.length name
         in
         let rec loop i =
            if i = len then
               false
            else if String.get name i = '/' then
               true
            else
               loop (i+1)
         in
            loop 0

      let join path1 path2 =
         if isAbsolute path2 then
            raise Path
         else if 
            String.length path1 >= 1 
            &&
            String.get path1 (String.length path1 - 1) = '/'
         then
            path1 ^ path2
         else
            String.concat "" [path1; "/"; path2]

      let makeAbsolute path1 path2 =
         if isAbsolute path2 then
            path2
         else
            join path1 path2

      let split path =
         let rec loop acc l =
            (match l with
                [] -> raise Path

              | [""] ->
                   (* filename is empty *)
                   raise Path

              | [filename] ->
                   (match acc with
                       [] -> (".", filename)

                     | [""] -> ("/", filename)

                     | _ -> (implode (List.rev acc), filename))

              | h :: t ->
                   loop (h :: acc) t)
         in
            loop [] (explode path)

      let joinExt path1 path2 =
         String.concat "" [path1; "."; path2]

      let splitExt path =
         let len = String.length path
         in
         let rec loop i =
            if i < 0 then
               None
            else if String.get path i = '.' then
               Some (String.sub path 0 i, String.sub path (i+1) (len - i - 1))
            else
               loop (i-1)
         in
            loop (len - 1)

      
      let illegalOnWindows ch = String.contains "\\/:*?\"<>|" ch

      let rec illegalWindowsLoop str i len =
         if i >= len then
            false
         else if illegalOnWindows (String.get str i) then
            true
         else
            illegalWindowsLoop str (i+1) len

      let illegalWindows str = illegalWindowsLoop str 0 (String.length str)


      let volumeId str =
         if
            String.length str = 2
            &&
            String.get str 1 = ':'
         then
            let ch = String.get str 0 in
            let n = Char.code ch
            in
               if 65 <= n && n <= 90 then
                  Some (Char.chr (n + 97 - 65))
               else if 97 <= n && n <= 122 then
                  Some ch
               else
                  None
         else
            None


      let toWindowsPath pathstr =
         let path = canonizeArcs (explode pathstr)
         in
            (match path with
                [] ->
                   (* Empty path.  Canonization won't allow this, but we'll just handle it. *)
                   raise Path

              | [""] ->
                   (* Empty filename.  Canonization won't allow this, but we'll just handle it. *)
                   raise Path

              | "" :: first :: rest ->
                   (* prospective absolute path, check volume id *)
                   (match volumeId first with
                       Some ch ->
                          if List.exists illegalWindows rest then
                             raise Path
                          else
                             String.concat "\\"
                                ((String.make 1 ch ^ ":")
                                 ::
                                 (match rest with
                                     [] -> [""]
                                   | _ -> rest))

                     | None ->
                          (* absolute path without volume id *)
                          raise Path)

              | _ ->
                   (* relative or simple path *)
                   if List.exists illegalWindows path then
                      raise Path
                   else
                      String.concat "\\" path)


      let fromWindowsPath pathstr =
         let path = canonizeArcs (String.split_on_char '\\' pathstr)
         in
            (match path with
                [] ->
                   (* Empty path.  Canonization won't allow this, but we'll just handle it. *)
                   raise Path

              | [""] ->
                   (* Empty filename.  Canonization won't allow this, but we'll just handle it. *)
                   raise Path

              | "" :: _ ->
                   (* Absolute path without volume id. *)
                   raise Path

              | first :: rest ->
                   (match volumeId first with
                       Some ch ->
                          implode ("" :: (String.make 1 ch ^ ":") :: rest)

                     | None ->
                          (* relative or simple path *)
                          implode path))


      let toNativePath =
         if Sys.win32 then
            toWindowsPath
         else
            (function str -> str)

      let fromNativePath =
         if Sys.win32 then
            fromWindowsPath
         else
            canonize


      let rec splitOnSlashes str i j len acc =
         if j >= len then
            List.rev (String.sub str i (j-i) :: acc)
         else if String.get str j = '/' || String.get str j = '\\' then
            splitOnSlashes str (j+1) (j+1) len (String.sub str i (j-i) :: acc)
         else
            splitOnSlashes str i (j+1) len acc


      let fromHybridPath pathstr =
         let path =
            canonizeArcs
               (splitOnSlashes pathstr 0 0 (String.length pathstr) [])
         in
            (match path with
                [] ->
                   (* Empty path.  Canonization won't allow this. *)
                   raise (Failure "impossible")

              | [""] ->
                   (* Empty filename.  Canonization won't allow this, but we'll just handle it. *)
                   raise (Failure "impossible")

              | "" :: _ ->
                   (* Absolute path without volume id. *)
                   implode path

              | first :: rest ->
                   (match volumeId first with
                       Some ch ->
                          implode ("" :: (String.make 1 ch ^ ":") :: rest)

                     | None ->
                          (* relative or simple path *)
                          implode path))

   end
