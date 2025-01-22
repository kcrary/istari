open:Relations
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

    star : type:star
         imp:star

    star_refl : type:star_refl
              imp:star_refl

    star_step : type:star_step
              imp:star_step

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

    plus : type:plus
         imp:plus

    plus_one : type:plus_one
              imp:plus_one

    plus_step : type:plus_step
              imp:plus_step

Lemmas:

    star_one : type:star_one

    star_trans : type:star_trans

    plus_trans : type:plus_trans

    star_plus_trans : type:star_plus_trans

    star_plus_trans : type:star_plus_trans

    plus_star_trans : type:plus_star_trans

    plus_impl_star : type:plus_impl_star

    plus_first : type:plus_first

    plus_first_iff : type:plus_first_iff

    plus_last : type:plus_last

    plus_last_iff : type:plus_last_iff

    star_impl_eq_or_plus : type:star_impl_eq_or_plus

    star_neq_impl_plus : type:star_neq_impl_plus

    star_reverse : type:star_reverse

    plus_reverse : type:plus_reverse

    plus_well_founded : type:plus_well_founded

Lexicographic order on pairs.

    lexpair : type:lexpair
            = def:lexpair

    lexpair_well_founded : type:lexpair_well_founded

    transpose : type:transpose
              = def:transpose

    transpose_invol : type:transpose_invol

    star_reverse_transpose : type:star_reverse_transpose

    plus_reverse_transpose : type:plus_reverse_transpose

The transitive closure of a relation is decidable, provided the
relation is decidable, well-founded, and finitely branching.

    decidable_plus : type:decidable_plus

The reflexive-transitive closure is decidable if additionally the
equality on the underlying type is decidable.

    decidable_star : type:decidable_star

