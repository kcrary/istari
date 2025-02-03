
(* This code is copied from CMlib. *)

signature PATH =
   sig
   
      (* argument is not a good path *)
      exception Path

      val explode : string -> string list
      val implode : string list -> string

      (* A canonical path:
         (1) is nonempty
         (2) contains . only as the entire path
         (3) contains .. only at the beginning
         (4) contains no empty directories
         (5) filename is not empty (ie, no trailing /)

         Raises Path if the path cannot be canonized.
      *)
      val canonize : string -> string

      val isAbsolute : string -> bool
      val isRelative : string -> bool
      val hasPath : string -> bool

      (* makeAbsolute path1 path2
       
         if    path1 and path2 are canonical, and path1 is absolute
         then  returns an absolute path corresponding to path2, using path1 as the
               current directory
      *)
      val makeAbsolute : string -> string -> string

      (* joins a path to either a filename or a relative path *)
      val join : string -> string -> string

      (* separate the path from the filename *)
      val split : string -> string * string

      (* join a filename to an extension (filename can be a path) *)
      val joinExt : string -> string -> string

      (* separate the filename from its extension (filename can be a path) *)
      val splitExt : string -> (string * string) option


      (* The absolute Windows path c:\a\b is represented by the Unix path /c:/a/b

         (Apart from tweaking the notation for the volume id, there doesn't seem to
         be a better stateless way to represent Windows paths as Unix paths.)

         Raises Path if the path is unrepresentable on the destination platform:

         - An absolute Windows path without volume id is unrepresentable on Unix
           (since it is not a relative path nor a fully absolute path).

         - An absolute Unix path that does not begin with a volume id is not
           representable on Windows.

         - A Unix path using forbidden characters (that is, \ / : * ? " < > | )
           is unrepresentable on Windows.

         The behavior of toWindowsPath on illegal Unix paths and of fromWindowsPath
         on illegal Windows paths is undefined.
      *)
      val toWindowsPath : string -> string
      val fromWindowsPath : string -> string


      (* If Windows, toWindowsPath.  Otherwise the identity. *)
      val toNativePath : string -> string

      (* If Windows, fromWindowsPath.  Otherwise canonize. *)
      val fromNativePath : string -> string


      (* A hybrid path can use either separator (slash or backslash).  Backslash
         cannot be used except as a separator, even though Unix paths permit it.  The
         path may begin with a volume id or not; if it does, it is interpreted as
         in fromWindowsPath.

         Hybrid paths are designed to accept valid Unix paths (provided they do not
         use backslash, nor use colon in a way that looks like a volume id) and also
         valid Windows paths (provided they include a volume id if they are absolute).
      *)
      val fromHybridPath : string -> string

   end



structure Path :> PATH =
   struct

      exception Path

      val explode = String.fields (fn ch => ch = #"/")

      val implode = String.concatWith "/"


      fun canonizeLoop acc path =
         (case path of
             ".." :: rest =>
                (case acc of
                    nil =>
                       canonizeLoop (".." :: acc) rest

                  | ".." :: _ =>
                       canonizeLoop (".." :: acc) rest

                  | "" :: _ =>
                       (* can't back up past the root *)
                       raise Path

                  | _ :: restacc =>
                       canonizeLoop restacc rest)

           | [] => rev acc
             
           | [""] =>
                (* trailing slash *)
                rev acc

           | "." :: _ => 
                (* can't have . in the middle of a path *)
                raise Path

           | "" :: _ =>
                (* can't have an empty directory name *)
                raise Path

           | name :: rest =>
                canonizeLoop (name :: acc) rest)

      fun canonizeArcs path =
         (case path of
             [] => raise Path
             
           | ["."] => ["."]
           | [".", ""] => ["."]

           | "." :: rest => canonizeLoop [] rest

           | ["", ""] =>
                (* root *)
                ["", ""]

           | "" :: rest =>
                (* absolute path *)
                canonizeLoop [""] rest

           | path => canonizeLoop [] path)

      fun canonize pathstr = implode (canonizeArcs (explode pathstr))


      fun isAbsolute path =
         String.sub (path, 0) = #"/"
         handle Subscript => raise Path

      fun isRelative path =
         String.sub (path, 0) <> #"/"
         handle Subscript => raise Path

      fun hasPath name =
         let
            val len = String.size name
            
            fun loop i =
               if i = len then
                  false
               else if String.sub (name, i) = #"/" then
                  true
               else
                  loop (i+1)
         in
            loop 0
         end

      fun join path1 path2 =
         if isAbsolute path2 then
            raise Path
         else if 
            String.size path1 >= 1 
            andalso
            String.sub (path1, String.size path1 - 1) = #"/"
         then
            path1 ^ path2
         else
            String.concat [path1, "/", path2]

      fun makeAbsolute path1 path2 =
         if isAbsolute path2 then
            path2
         else
            join path1 path2

      fun split path =
         let
            fun loop acc l =
               (case l of
                   nil => raise Path

                 | [""] =>
                      (* filename is empty *)
                      raise Path

                 | [filename] =>
                      (case acc of
                          [] => (".", filename)

                        | [""] => ("/", filename)

                        | _ => (implode (rev acc), filename))

                 | h :: t =>
                      loop (h :: acc) t)
         in
            loop [] (explode path)
         end

      fun joinExt path1 path2 =
         String.concat [path1, ".", path2]

      fun splitExt path =
         let
            fun loop i =
               if i < 0 then
                  NONE
               else if String.sub (path, i) = #"." then
                  SOME (String.substring (path, 0, i), String.extract (path, i+1, NONE))
               else
                  loop (i-1)
         in
            loop (String.size path - 1)
         end



      val illegalOnWindows = Char.contains "\\/:*?\"<>|"

      fun illegalWindowsLoop str i len =
         if i >= len then
            false
         else if illegalOnWindows (String.sub (str, i)) then
            true
         else
            illegalWindowsLoop str (i+1) len

      fun illegalWindows str = illegalWindowsLoop str 0 (String.size str)


      fun volumeId str =
         if
            String.size str = 2
            andalso
            String.sub (str, 1) = #":"
         then
            let
               val ch = String.sub (str, 0)
            in
               if Char.isAlpha ch then
                  SOME (Char.toLower ch)
               else
                  NONE
            end
         else
            NONE
         

      fun toWindowsPath pathstr =
         let
            val path = canonizeArcs (explode pathstr)
         in
            (case path of
                [] =>
                   (* Empty path.  Canonization won't allow this, but we'll just handle it. *)
                   raise Path

              | [""] =>
                   (* Empty filename.  Canonization won't allow this, but we'll just handle it. *)
                   raise Path

              | "" :: first :: rest =>
                   (* prospective absolute path, check volume id *)
                   (case volumeId first of
                       SOME ch =>
                          if List.exists illegalWindows rest then
                             raise Path
                          else
                             String.concatWith "\\"
                                (String.str ch ^ ":"
                                 ::
                                 (case rest of
                                     nil => [""]
                                   | _ => rest))

                     | NONE =>
                          (* absolute path without volume id *)
                          raise Path)

              | _ =>
                   (* relative or simple path *)
                   if List.exists illegalWindows path then
                      raise Path
                   else
                      String.concatWith "\\" path)
         end

      fun fromWindowsPath pathstr =
         let
            val path = canonizeArcs (String.fields (fn ch => ch = #"\\") pathstr)
         in
            (case path of
                [] =>
                   (* Empty path.  Canonization won't allow this, but we'll just handle it. *)
                   raise Path

              | [""] =>
                   (* Empty filename.  Canonization won't allow this, but we'll just handle it. *)
                   raise Path

              | "" :: _ =>
                   (* Absolute path without volume id. *)
                   raise Path

              | first :: rest =>
                   (case volumeId first of
                       SOME ch =>
                          implode ("" :: String.str ch ^ ":" :: rest)

                     | NONE =>
                          (* relative or simple path *)
                          implode path))
         end


      val toNativePath =
         (case Pathsort.sort of
             Pathsort.UNIX => (fn str => str)
           | Pathsort.WINDOWS => toWindowsPath)

      val fromNativePath =
         (case Pathsort.sort of
             Pathsort.UNIX => canonize
           | Pathsort.WINDOWS => fromWindowsPath)


      fun fromHybridPath pathstr =
         let
            val path = canonizeArcs (String.fields (fn ch => ch = #"/" orelse ch = #"\\") pathstr)
         in
            (case path of
                [] =>
                   (* Empty path.  Canonization won't allow this. *)
                   raise (Fail "impossible")

              | [""] =>
                   (* Empty filename.  Canonization won't allow this. *)
                   raise (Fail "impossible")

              | "" :: _ =>
                   (* Absolute path without volume id. *)
                   implode path

              | first :: rest =>
                   (case volumeId first of
                       SOME ch =>
                          implode ("" :: String.str ch ^ ":" :: rest)

                     | NONE =>
                          (* relative or simple path *)
                          implode path))
         end

   end
