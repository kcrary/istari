
signature LANGUAGE =
   sig

      datatype language = SML | OCAML

      val target : language ref
      val smlCompatibility : bool ref

      val languageToString : language -> string

   end


structure Language =
   struct

      datatype language = SML | OCAML

      val target = ref SML
      val smlCompatibility = ref false

      fun languageToString lang =
         (case lang of
             SML => "SML"
           | OCAML => "OCaml")

   end
