
Require Import Coq.Init.Prelude.

(* Basically sigT from Specif, but with better notation. *)

Inductive exT (A : Type) (P : A -> Type) : Type :=
| expair : forall x, P x -> exT A P.

Arguments expair {A} {P} x y.

Notation "'existsT' x , p" := (exT _ (fun x => p))
  (at level 200, x ident, p at level 200, right associativity)
  : type_scope.


Notation "'existsT' ( x : A ) , p" := (exT A (fun x => p))
  (at level 200, x ident, A at level 200, p at level 200, right associativity)
  : type_scope.

Definition uniqueT {A : Type} (P : A -> Type) (x:A) :=
  prod (P x) (forall (y:A), P y -> x = y).

Notation "'existsT' ! ( x : A ) , p" := (exT A (uniqueT (fun x => p) ))
  (at level 200, x ident, A at level 200, p at level 200, right associativity)
  : type_scope.


Definition pi1 {A : Type} {B : A -> Type} (p : exT A B) : A :=
  (match p with
   | expair x y => x
   end).

Definition pi2 {A : Type} {B : A -> Type} (p : exT A B) : B (pi1 p) :=
  (match p with
   | expair x y => y
   end).

Notation "P /t\ Q" := (prod P Q)
  (at level 80, right associativity).

Notation "P \t/ Q" := (sum P Q)
  (at level 85, right associativity).
