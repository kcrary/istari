# Path

Library for manipulating Unix paths.  Windows paths are not supported,
except for conversion to and from Unix paths.

    signature PATH =
       sig

          exception Path
    
          val explode : string -> string list
          val implode : string list -> string
    
          val canonize : string -> string
    
          val isAbsolute : string -> bool
          val isRelative : string -> bool
          val hasPath : string -> bool
    
          val makeAbsolute : string -> string -> string
          val join : string -> string -> string
          val split : string -> string * string
    
          val joinExt : string -> string -> string
          val splitExt : string -> (string * string) option
    
          val toWindowsPath : string -> string
          val fromWindowsPath : string -> string

          val toNativePath : string -> string
          val fromNativePath : string -> string

          val fromHybridPath : string -> string
    
       end
    
    structure Path : PATH

- `exception Path`

  Raised when an argument is not a good path.

- `explode : string -> string list`

  Breaks a path into its individual arcs (directories or file name).

- `implode : string list -> string`

  Constructs a path from its individual arcs.

- `canonize : string -> string`

  Puts a path in canonical form.  A canonical path:

  1. is nonempty
  2. contains `.` only as the entire path
  3. contains `..` only at the beginning
  4. contains no empty directories
  5. the filename is not empty (*i.e.,* no trailing `/`), unless it is
     the root directory

- `hasPath : string -> bool`

  Determines if the path contains any directory arcs.

- `makeAbsolute : string -> string -> string`

  Given `path1` and `path2`, if both are canonical and `path1` is
  absolute, then returns an absolute path corresponding to `path2`,
  using `path1` as the current directory.

- `join : string -> string -> string`

  Joins a path to either a filename or a relative path.

- `split : string -> string * string`

  Separate the directories portion of the path from the filename.
  Returns `.` as the directories if the path has none.

- `joinExt : string -> string -> string`

  Joins a filename to an extension.  The filename is permitted to be a
  path.

- `splitExt : string -> (string * string) option`

  Splits a filename into a base name and an extension.  Returns `None`
  if the filename has no extension.  The filename is permitted to be a
  path.

- `toWindowsPath : string -> string`

  Converts a Unix path into a Windows path.  ([See
  below.](#windows-paths-as-unix-paths)) Raises `Path` if the path is
  unrepresentable as a Windows path.  The behavior on illegal Unix
  paths is undefined.

- `fromWindowsPath : string -> string`

  Converts a Windows path into a Unix path.  ([See
  below.](#windows-paths-as-unix-paths)) Raises `Path` if the path is
  unrepresentable as a Unix path.  The behavior on illegal Windows
  paths is undefined.

- `toNativePath : string -> string`

  On Windows platforms, identical to `toWindowsPath`.  Otherwise the
  identity.

- `fromNativePath : string -> string`

  On Windows platforms, identical to `fromWindowsPath`.  Otherwise
  identical to `canonize`.

- `fromHybridPath : string -> string`

  Converts a hybrid path into a Unix path.  ([See
  below.](#hybrid-paths))


### Windows paths as Unix paths

For relative paths, the only difference between a Unix and Windows
path is the separator (`/` versus `\`).  For absolute paths, a Windows
path has a volume id (*e.g.* `c:`) whereas a Unix path does not.  We
view the Windows volume id as a subdirectory of the root.  Thus, the
Windows path `c:\a\b` is represented by the Unix path `/c:/a/b`.

- An absolute Windows path without a volume id is unrepresentable on
  Unix, since it is neither a relative path nor an absolute path.

- An absolute Unix path that does not begin with a volume id is not
  representable on Windows.

- A Unix path containing forbidden characters (that is, 
  `\ / : * ? " < > |`) is not representable on Windows.

Unix paths are used consistently throughout IML and Istari, except for
Istari's command-line arguments and environment variables, which
accept [hybrid paths](#hybrid-paths).


#### Hybrid paths

A hybrid path can use either separator, `/` or `\`.  The symbol `\`
cannot be used except as a separator, even though Unix paths permit
it.  The path may begin with a volume id or not; if it does, it is
interpreted as above.

Hybrid paths are designed to accept valid Unix paths (provided they do
not use `\`, nor use `:` in a way that looks like a volume id) and
also valid Windows paths (provided they include a volume id if they
are absolute).
