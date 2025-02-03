# `Relations`

Reflexive-transitive closure of relations is defined:

    datatype
      intersect (i : level) .
      forall (a : U i) (R : a -> a -> U i) .
      U i
    of
      star : a -> a -> type =
      | star_refl :
          forall x .
            star x x
  
      | star_step :
          forall x y z .
            R x y
            -> star y z
            -> star x z

Producing:

    star : intersect (i : level) . forall (a : U i) (R : a -> a -> U i) . a -> a -> U i
         (1 implicit argument)

    star_refl : intersect (i : level) . forall (a : U i) (R : a -> a -> U i) (x : a) . star R x x
              (0 implicit arguments)

    star_step : intersect (i : level) .
                   forall (a : U i) (R : a -> a -> U i) (x y z : a) .
                     R x y -> star R y z -> star R x z
              (0 implicit arguments)

Transitive closure of relations is defined:

    datatype
      intersect (i : level) .
      forall (a : U i) (R : a -> a -> U i) .
      U i
    of
      plus : a -> a -> type =
      | plus_one :
          forall x y .
            R x y
            -> plus x y
  
      | plus_step :
          forall x y z .
            R x y
            -> plus y z
            -> plus x z

Producing:

    plus : intersect (i : level) . forall (a : U i) (R : a -> a -> U i) . a -> a -> U i
         (1 implicit argument)

    plus_one : intersect (i : level) .
                  forall (a : U i) (R : a -> a -> U i) (x y : a) . R x y -> plus R x y
              (0 implicit arguments)

    plus_step : intersect (i : level) .
                   forall (a : U i) (R : a -> a -> U i) (x y z : a) .
                     R x y -> plus R y z -> plus R x z
              (0 implicit arguments)

Lemmas:

    star_one : forall (i : level) (a : U i) (R : a -> a -> U i) (x y : a) . R x y -> star R x y

    star_trans : forall (i : level) (a : U i) (R : a -> a -> U i) (x y z : a) .
                    star R x y -> star R y z -> star R x z

    plus_trans : forall (i : level) (a : U i) (R : a -> a -> U i) (x y z : a) .
                    plus R x y -> plus R y z -> plus R x z

    star_plus_trans : forall (i : level) (a : U i) (R : a -> a -> U i) (x y z : a) .
                         star R x y -> plus R y z -> plus R x z

    star_plus_trans : forall (i : level) (a : U i) (R : a -> a -> U i) (x y z : a) .
                         star R x y -> plus R y z -> plus R x z

    plus_star_trans : forall (i : level) (a : U i) (R : a -> a -> U i) (x y z : a) .
                         plus R x y -> star R y z -> plus R x z

    plus_impl_star : forall (i : level) (a : U i) (R : a -> a -> U i) (x y : a) .
                        plus R x y -> star R x y

    plus_first : forall (i : level) (a : U i) (R : a -> a -> U i) (x z : a) .
                    plus R x z -> exists (y : a) . R x y & star R y z

    plus_first_iff : forall (i : level) (a : U i) (R : a -> a -> U i) (x z : a) .
                        plus R x z <-> (exists (y : a) . R x y & star R y z)

    plus_last : forall (i : level) (a : U i) (R : a -> a -> U i) (x z : a) .
                   plus R x z -> exists (y : a) . star R x y & R y z

    plus_last_iff : forall (i : level) (a : U i) (R : a -> a -> U i) (x z : a) .
                       plus R x z <-> (exists (y : a) . star R x y & R y z)

    star_impl_eq_or_plus : forall (i : level) (a : U i) (R : a -> a -> U i) (x y : a) .
                              star R x y -> x = y : a % plus R x y

    star_neq_impl_plus : forall (i : level) (a : U i) (R : a -> a -> U i) (x y : a) .
                            star R x y -> x != y : a -> plus R x y

    star_reverse : forall (i : level) (a : U i) (R R' : a -> a -> U i) .
                      (forall (x y : a) . R x y -> R' y x)
                      -> forall (x y : a) . star R x y -> star R' y x

    plus_reverse : forall (i : level) (a : U i) (R R' : a -> a -> U i) .
                      (forall (x y : a) . R x y -> R' y x)
                      -> forall (x y : a) . plus R x y -> plus R' y x

    plus_well_founded : forall (i : level) (a : U i) (R : a -> a -> U i) .
                           (forall (x : a) . Acc.Acc a R x)
                           -> forall (x : a) . Acc.Acc a (plus R) x

Lexicographic order on pairs.

    lexpair : intersect (i : level) .
                 forall (a b : U i) . (a -> a -> U i) -> (b -> b -> U i) -> a & b -> a & b -> U i
            = fn a b Q R x y . Q (x #1) (y #1) % x #1 = y #1 : a & R (x #2) (y #2)

    lexpair_well_founded : forall
                              (i : level)
                              (a b : U i)
                              (Q : a -> a -> U i)
                              (R : b -> b -> U i) .
                              (forall (x : a) . Acc.Acc a Q x)
                              -> (forall (x : b) . Acc.Acc b R x)
                              -> forall (x : a & b) . Acc.Acc (a & b) (lexpair Q R) x

    transpose : intersect (i : level) (a : U i) . (a -> a -> U i) -> a -> a -> U i
              = fn R x y . R y x

    transpose_invol : forall (i : level) (a : U i) (R : a -> a -> U i) .
                         transpose (transpose R) = R : (a -> a -> U i)

    star_reverse_transpose : forall (i : level) (a : U i) (R : a -> a -> U i) (x y : a) .
                                star R x y <-> star (transpose R) y x

    plus_reverse_transpose : forall (i : level) (a : U i) (R : a -> a -> U i) (x y : a) .
                                plus R x y <-> plus (transpose R) y x

The transitive closure of a relation is decidable, provided the
relation is decidable, well-founded, and finitely branching.

    decidable_plus : forall (i : level) (a : U i) (R : a -> a -> U i) .
                        (forall (x y : a) . Decidable.decidable (R x y))
                        -> (forall (x : a) . Acc.Acc a R x)
                        -> (forall (y : a) . Finite.finite (fn x . R x y))
                        -> forall (x y : a) . Decidable.decidable (plus R x y)

The reflexive-transitive closure is decidable if additionally the
equality on the underlying type is decidable.

    decidable_star : forall (i : level) (a : U i) (R : a -> a -> U i) .
                        (forall (x y : a) . Decidable.decidable (x = y : a))
                        -> (forall (x y : a) . Decidable.decidable (R x y))
                        -> (forall (x : a) . Acc.Acc a R x)
                        -> (forall (y : a) . Finite.finite (fn x . R x y))
                        -> forall (x y : a) . Decidable.decidable (star R x y)

