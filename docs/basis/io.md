# IO

    signature IO =
       sig

          type ioerr
          exception Io of ioerr
          val ioerrToString : ioerr -> string

       end
    
    structure IO : IO
    
- `type ioerr`

  The `ioerr` type is abstract, because we cannot reconcile the
  different data carried by I/O errors in the SML and OCaml bases.
  Consequently, the programmer must match `Io`'s argument using a
  variable or wildcard.
