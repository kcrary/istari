
signature POSTPROCESS =
   sig

      (* filename, span, message *)
      type errinfo = string * ((int * int) * (int * int)) * string

      (* Process the ML output into one of four classes:
         - error or warning message, which are then parsed and returned
         - boring messages that should not be displayed
         - ordinary output that should be displayed
      *)

      datatype class = Error of errinfo | Warning of errinfo | Boring | Neither

      val classify : char Stream.stream -> class

   end
