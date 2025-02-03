
type order = LESS | EQUAL | GREATER

let intCompare x y =
   if x = y 
      then EQUAL 
   else if x < y then 
      LESS
   else
      GREATER

let intInfCompare x y =
   let z = Z.compare x y
   in
      if z = 0 then
         EQUAL
      else if z < 0 then
         LESS
      else
         GREATER

let stringCompare x y =
   let z = String.compare x y
   in
      if z = 0 then
         EQUAL
      else if z < 0 then
         LESS
      else
         GREATER

let charCompare x y =
   let z = Char.compare x y
   in
      if z = 0 then
         EQUAL
      else if z < 0 then
         LESS
      else
         GREATER
