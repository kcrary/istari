
signature POSTPROCESS =
   sig

      (* filename, span, message *)
      type errinfo = string * ((int * int) * (int * int)) * string

      datatype class = Error of errinfo | Warning of errinfo | Boring | Neither

      val classify : char Stream.stream -> class

   end
