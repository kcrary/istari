# FileSystem

A threadbare set of file system primitives.

    signature FILE_SYSTEM =
       sig
    
          exception FileSystem of string
    
          val chDir : string -> unit
          val getDir : unit -> string
    
          val exists : string -> bool
          
          val isDir : string -> bool
    
          val remove : string -> unit
    
       end
    
    structure FileSystem : FILE_SYSTEM

File names are always represented as [Unix
paths](path.html#windows-paths-as-unix-paths), regardless of the
platform.

- `chDir : string -> unit`

  Sets the current working directory.

- `getDir : unit -> string`

  Returns the current working directory.

- `exists : string -> bool`

  Returns true if the indicated file exists.  Will not raise an exception.
