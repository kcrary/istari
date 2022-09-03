
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.PropExtensionality.
Require Coq.Logic.Description.
Require Coq.Logic.Classical_Prop.


Require Import Tactics.
Require Import Sigma.


Ltac fextensionality :=
  fun n =>
    (match n with
     | 0 => idtac
     | S ?n' =>
         let x := fresh "x"
         in
           apply FunctionalExtensionality.functional_extensionality_dep;
           intro x;
           fextensionality n';
           revert x
     end).

Ltac pextensionality := apply propositional_extensionality; split.


Lemma UIP :
  forall (A : Type) (x y : A) (p1 p2 : x = y),
    p1 = p2.
Proof.
intros A x y p1 p2.
apply proof_irrelevance.
Qed.


Hint Resolve UIP : uip.


Lemma description :
  forall (A : Type) (P : A -> Prop),
    (exists! x, P x)
    -> exT A P.
Proof.
intros A P H.
pose proof (Coq.Logic.Description.constructive_definite_description P H) as (x & Hx).
exists x.
auto.
Qed.


Lemma choice :
  forall (A B : Type) (P : A -> B -> Prop),
    (forall x, exists! y, P x y)
    -> existsT (f : A -> B), forall x, P x (f x).
Proof.
intros A B P Hex.
exists (fun x => pi1 (description _ (P x) (Hex x))).
intro x.
exact (pi2 (description _ (P x) (Hex x))).
Qed.


Lemma description_beta :
  forall A (P : A -> Prop) (x : A) (H : unique P x),
    pi1 (description A P (ex_intro _ x H)) = x.
Proof.
intros A P x Huniq.
symmetry.
pose proof Huniq as (_ & Honly).
apply Honly.
exact (pi2 (description A P (ex_intro (unique P) x Huniq))).
Qed.


(* used in SemanticsGuard and Lattice *)
Definition excluded_middle := Coq.Logic.Classical_Prop.classic.
Definition proof_by_contradiction := Coq.Logic.Classical_Prop.NNPP.
