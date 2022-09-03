
let rec listToSeq l () =
   (match l with
       [] -> Seq.Nil
     | h :: t -> Seq.Cons (h, listToSeq t))


let implode chars = String.of_seq (listToSeq chars)


let explode str =
   List.init (String.length str) (String.get str)

