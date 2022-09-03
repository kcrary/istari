
Require Export Coq.omega.Omega.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Logic.Eqdep_dec.
Require Import Sigma.


(* Misc *)

Ltac evargen T k
  :=
  let X := fresh "XYZZY"
  in
    evar (X : T);
    let E := eval unf in X in
      clear X;
      k E.


(* Failure without the negative connotation, for marking completions. *)
Ltac done := fail 0 "goal incomplete".


Ltac do2_main n tac :=
  (lazymatch n with
   | 0 => idtac
   | S ?n' => tac; [| do2_main n' tac]
   end).


Tactic Notation "do2" constr(n) tactic3(tac)
  :=
  do2_main n tac.


Ltac repeat2_main tac :=
  try (tac; [| repeat2_main tac]).


Tactic Notation "repeat2" tactic3(tac)
  :=
  repeat2_main tac.


Ltac splitall := repeat2 split.


Tactic Notation "splithyp" ident(H) := destruct H as [H | H].


Ltac under_intros_main tac revtac :=
  first
  [
    intro;
    lazymatch goal with
    | H : _ |- _ =>
      under_intros_main ltac:(tac) ltac:(revert H; revtac)
    end
  |
    tac; revtac
  ].

Tactic Notation "under_intros" tactic(tac) := under_intros_main ltac:(tac) ltac:(idtac).


Ltac findcontra :=
  (match goal with
   | H1:?T, H2:(not ?T) |- _ => destruct H2; exact H1
   | H1:(@eq _ ?x ?y), H2:(not (@eq _ ?y ?x)) |- _ => destruct H2; symmetry; exact H1
   | H:(not (@eq _ ?x ?x)) |- _ => destruct H; reflexivity
   | H:False |- _ => destruct H
   end).


Ltac revert_last
  :=
  (lazymatch goal with
     H:_ |- _ => revert H
   end).


Ltac revert_all := repeat revert_last.


Ltac clear_all := repeat (match goal with H:_ |- _ => clear H end).


Ltac destruct_all_main H :=
  (lazymatch type of H with
   | exists _:_, _ => 
               let H' := fresh "x"
               in
                 destruct H as [H' H]; destruct_all_main H'; destruct_all_main H

   | _ /\ _ => let H' := fresh "H"
               in
                 destruct H as [H' H]; destruct_all_main H'; destruct_all_main H

   | prod _ _ =>
               let H' := fresh "x"
               in
                 destruct H as [H' H]; destruct_all_main H'; destruct_all_main H

   | exT _ _ =>
       let H' := fresh "x"
       in
         destruct H as [H' H]; destruct_all_main H'; destruct_all_main H

   | _ => idtac
   end).


Ltac destruct_all t :=
  first [
        destruct_all_main t
        |
        let H := fresh
        in
          pose proof t as H;
          destruct_all_main H
        ].


Ltac destruct_everywhere :=
  repeat
    (match goal with
     | H : exists _,_ |- _ => destruct H
     | H : _ /\ _ |- _ => destruct H
     | H : prod _ _ |- _ => destruct H
     end).


Tactic Notation "substeq" "->" hyp(H) :=
  (match type of H with
   | ?t = _ => subst t
   end).


Tactic Notation "substeq" "<-" hyp(H) :=
  (match type of H with
   | ?t = _ => subst t
   end).


Tactic Notation "f_apply" constr(f) "in" hyp(H) "as" ident(H') :=
  (match type of H with
   | @eq _ ?t1 ?t2 =>
       assert (f t1 = f t2) as H' by (f_equal; exact H);
       cbv beta in H'
   end).


Tactic Notation "f_apply" constr(f) "in" hyp(H) :=
  let H' := fresh "H" in f_apply f in H as H'.


(* Works better than f_apply. *)
Lemma eq_fn_apply :
  forall {T U : Type} {x y : T} (f : T -> U),
    x = y
    -> f x = f y.
Proof.
intros; f_equal; auto.
Qed.


Tactic Notation "forget" constr(t) "as" ident(x) :=
  remember t as x eqn:HHxyzzy; clear HHxyzzy.


Ltac force_exact H :=
  (match goal with
   | |- ?C => 
     let D := type of H
     in
       replace C with D; [exact H |]
   end).


Ltac cut_discriminate t1 t2
  :=
  let H := fresh
  in
    cut (t1 = t2); [intro H; discriminate H |].


Tactic Notation "renameover" hyp(H1) "into" hyp(H2) :=
  clear H2; rename H1 into H2.


Tactic Notation "injectionc" hyp(H) :=
  injection H; clear H.


(* Make tactics not generate hypotheses *)

Definition Marker_revertnew := True.

Tactic Notation "revertnew" tactic3(tac) :=
  let Hmark := fresh
  in
    assert Marker_revertnew as Hmark; [exact I | idtac];
    tac;
    repeat
      (lazymatch goal with
       | H : ?T |- _ =>
           (lazymatch T with
            | Marker_revertnew => fail
            | _ => revert H
            end)
       end);
    clear Hmark.


(* Decomposition of a definition *)

Ltac headvar t :=
  (lazymatch t with
   | ?f _ => headvar f
   | _ => t
   end).

Tactic Notation "unfoldtop" :=
  match goal with
  | |- ?P =>
     let t := headvar P
     in
       unfold t
  end.

Tactic Notation "unfoldtop" hyp(H) :=
  let t := headvar ltac:(type of H)
  in
    unfold t in H.

Definition Marker_decompose := True.

Tactic Notation "decompose" hyp(H) :=
  let t := headvar ltac:(type of H)
  in let Hmark := fresh
  in
    unfold t in H;
    assert Marker_decompose as Hmark; [exact I | idtac];
    move H after Hmark;
    destruct_all H; [];
    repeat
      (lazymatch goal with
       | H : ?T |- _ =>
           (lazymatch T with
            | Marker_decompose => fail
            | _ => revert H
            end)
       end);
    clear Hmark.


(* Simpler induction. *)

Tactic Notation "clear" "codependent" hyp(H)
  :=
  let T := type of H
  in
    clear H;
    repeat
      (match goal with
         x:_ |- _ =>
           (match T with
              context [x] => 
                (* This might fail because:
                   * x is mentioned in a hyp that should have been reverted but wasn't,
                     so leaving it is necessary; or
                   * x is fixed (ie, non-inductive) argument to H,
                     so leaving it is actually desired.
                *)
                clear x
            end)
       end).


Tactic Notation "induct" hyp(H)
  :=
  elim H;
  clear codependent H.


Tactic Notation "induct" hyp(H) "using" constr(ind)
  :=
  elim H using ind;
  clear codependent H.


Tactic Notation "wfinduct" hyp(H) "using" constr(T) :=
  revert H;
  match goal with
  | |- forall x, @?P x => apply (well_founded_induction_type T P)
  end.



(* Eqdec *)

Definition eqdec_nat :
  forall (x x' : nat), {x = x'} + {x <> x'}.
Proof.
intros x1.
induct x1.

(* 0 *)
intro x2.
destruct x2 as [| x2'].
  left; reflexivity.

  right; intro H; discriminate H.

(* S *)
intros x1' IH x2.
destruct x2 as [| x2'].
  right; intro H; discriminate H.

  destruct (IH x2') as [H | H].
    subst x2'.
    left; reflexivity.
    
    right; intro H'.
    destruct H; [].
    injection H'; auto; done.
Qed.


Definition eqdec_list :
  forall (A : Type),
    (forall (x x' : A), {x = x'} + {x <> x'})
    -> forall (l l' : list A), {l = l'} + {l <> l'}.
Proof.
intros A Heq l1.
induct l1.

(* nil *)
{
intro l2.
destruct l2 as [| x' l2'].
- left; reflexivity.

- right; intro H; discriminate H.
}

(* cons *)
{
intros x l1' IH l2.
destruct l2 as [| x' l2'].
- right; intro H; discriminate H.

- destruct (IH l2') as [H | H].
  + subst l2'.
    destruct (Heq x x') as [H' | H'].
    * subst x'.
      left; reflexivity.

    * right; intro H.
      destruct H'.
      injection H; auto; done.

  + right; intro H'.
    destruct H.
    injection H'; auto; done.
}
Qed.


Hint Resolve eqdec_nat eqdec_list : eqdec.


(* UIP *)

Lemma existT_eq_impl_eq_dep :
  forall (A : Type) (B : A -> Type) (a a' : A) (b : B a) (b' : B a'),
    existT B a b = existT B a' b'
    -> eq_dep A B a b a' b'.
Proof.
intros A B a a' b b' Heq.
pose proof (f_equal (@projT1 A B) Heq) as H.
cbn in H.
subst a'.
cut (forall (x y : sigT B), x = y -> eq_dep A B (projT1 x) (projT2 x) (projT1 y) (projT2 y)).
  {
  intro H.
  pose proof (H _ _ Heq) as H'.
  cbn in H'.
  exact H'.
  }
intros x y <-.
apply eq_dep_refl.
Qed.


Lemma eq_dep_impl_eq_UIP :
  forall (A : Type),
    (forall (x y : A) (p1 p2 : x = y), p1 = p2)
    -> forall (B : A -> Type) (a : A) (x y : B a),
         eq_dep A B a x a y
         -> x = y.
Proof.
intros A Huip B a x y Heq.
apply eq_rect_eq__eq_dep_eq; auto.
apply Streicher_K__eq_rect_eq; [].
apply UIP_refl__Streicher_K; [].
apply UIP__UIP_refl; auto.
Qed.


Lemma inj_pair2_UIP :
  forall (A : Type),
    (forall (x y : A) (p1 p2 : x = y), p1 = p2)
    -> forall (P : A -> Type) (p : A) (x y: P p),
         existT P p x = existT P p y
         -> x = y.
Proof.
intros A Huip P p x y Heq.
apply eq_dep_eq__inj_pair2; auto; [].
apply eq_rect_eq__eq_dep_eq; [].
apply Streicher_K__eq_rect_eq; [].
apply UIP_refl__Streicher_K; [].
apply UIP__UIP_refl; auto.
Qed.


Hint Resolve UIP_dec : uip.


(* Better inversion *)

Definition Marker_invert := True.

(* Intro down to marker, split equalities, subst redundant variables, and revert back. *)
Ltac invproc stac rtac :=
  (lazymatch goal with
   | |- Marker_invert -> _ => intros _; stac; rtac

   | |- ?x = ?x -> _ => intros _; invproc stac rtac

   | |- existT ?B _ _ = existT ?B _ _ -> _ =>
       let H := fresh "Heq" in
       let H' := fresh
       in
         intro H;
         pose proof (existT_eq_impl_eq_dep _ B _ _ _ _ H) as H';
         clear H;
         revert H';
         invproc stac rtac

   | |- eq_dep _ _ ?x ?y ?x ?z -> _ =>
       let H := fresh "Heq" in
       let H' := fresh
       in
         intro H;
         first
           [
             assert (y = z) as H';
             [ refine (eq_dep_impl_eq_UIP _ _ _ _ _ _ H); auto with uip eqdec; done
             | clear H; revert H'; invproc stac rtac
             ]
           |
             invproc stac ltac:(try (revert H); rtac)
           ]

   | |- _ = _ -> _ =>
       let H := fresh "Heq"
       in
         intro H;
         first
         [
           injection H;
           clear H;
           invproc stac rtac
         |
           invproc stac ltac:(try (revert H); rtac)
         ]

   | |- forall (x : _), _ =>
       let y := fresh x
       in
         intro y;
         invproc ltac:(try (subst y); stac) ltac:(try (revert y); rtac)
   end).


Tactic Notation "invert" constr(t) :=
  let Hinv := fresh in
  let Hgoal := fresh in
  let Hmark1 := fresh in
  let Hmark2 := fresh
  in
    (* Keep inversion from messing with the goal. *)
    (lazymatch goal with
     | |- ?T => change (let Hgoal := T in Hgoal); intro Hgoal
     end);
    pose proof t as Hinv;
    assert Marker_invert as Hmark1; [exact I | pose proof Hmark1 as Hmark2; revert Hmark2];
    inversion Hinv;
    clear Hinv;
    subst Hgoal;  (* Put the goal back. *)
    repeat
      (lazymatch goal with
       | H : ?T |- _ =>
           (lazymatch T with
            | Marker_invert => fail
            | _ => revert H
            end)
       end);
    clear Hmark1;
    invproc idtac idtac.


Tactic Notation "invertc" hyp(H) :=
  invert H; clear H.


(* Case analysis *)

Ltac substreflmain h :=
  let Huip := fresh
  in
    (match type of h with
     | @eq ?A ?x ?x =>
         assert (forall (y z : A) (p1 p2 : y = z), p1 = p2) as Huip by (auto with uip eqdec);
         pose proof (Huip x x h (eq_refl x));
         clear Huip;
         subst h
     end).


Definition Marker_substrefl := True.
Ltac substrefl h :=
  let Hmarker := fresh
  in
    substreflmain h;
    assert Marker_substrefl as Hmarker; [exact I |];
    revert_all;
    simpl eq_rect;
    repeat
      (lazymatch goal with
       | |- Marker_substrefl -> _ => fail
       | |- forall _,_ => intro
       end);
    intros _.


Ltac substrefls :=
  repeat
    (match goal with
     | E : ?x = ?x |- _ => substrefl E
     end).


Tactic Notation "casesdep" hyp(e) :=
pattern e;
let H := fresh in
let y := fresh "y" in
let e' := fresh "e"  in
let h := fresh "h"
in
compute in e;
(match type of e with
 | ?A ?x =>
   let U := type of x
   in
     (match goal with
      | |- ?P e =>
        cut (forall y (e' : A y) (h : y = x), P (eq_rect y A e' x h));
        [
          intro H;
          exact (H x e (eq_refl _))
        |
          clear e;
          intros y e';
          case e';
          clear y e';
          revertnew
            (intros;
             try discriminate;
             repeat
               (match goal with
                | h : @eq U ?w ?w |- _ => substreflmain h
                end))
        ]
      end)
 end); 
simpl eq_rect.


Tactic Notation "cases" hyp(H) :=
  first
  [
    case H;
    clear codependent H
  |
    casesdep H
  ].


(* Use a hypothesis/lemma. *)

Ltac exploit_main t T pat cleanup
  :=
  (lazymatch T with
   | ?U1 -> ?U2 =>
       let H := fresh "QWERTY"
       in
         assert U1 as H;
         [cleanup () | exploit_main (t H) U2 pat ltac:(fun _ => clear H; cleanup ())]
   | _ =>
       pose proof t as pat;
       cleanup ()
   end).


Tactic Notation "exploit" constr(t) "as" simple_intropattern(pat)
  :=
  exploit_main t ltac:(type of t) pat ltac:(fun _ => idtac).


Tactic Notation "exploit" constr(t)
  :=
  let H := fresh "H"
  in
    exploit_main t ltac:(type of t) H ltac:(fun _ => idtac).


Ltac eexploit_main t T pat cleanup
  :=
  (lazymatch T with
   | ?U1 -> ?U2 =>
       let H := fresh "QWERTY"
       in
         assert U1 as H;
         [cleanup () | eexploit_main (t H) U2 pat ltac:(fun t' => clear H; cleanup ())]
   | forall x : ?S, @?P x =>
       evargen S ltac:(fun x' => eexploit_main (t x') ltac:(eval hnf in (P x')) pat cleanup)
   | _ =>
       pose proof t as pat;
       cleanup ()
   end).


Tactic Notation "eexploit" constr(t) "as" simple_intropattern(pat)
  :=
  eexploit_main t ltac:(type of t) pat ltac:(fun _ => idtac).


Tactic Notation "eexploit" constr(t)
  :=
  let H := fresh "H"
  in
    eexploit_main t ltac:(type of t) H ltac:(fun _ => idtac).


Ltac eapplyall
  :=
  (match goal with
     H:_ |- _ => eapply H
   end).


Ltac tryall tac
  :=
  try (match goal with H:_ |- _ => tac H end).


Ltac repeatall tac
  :=
  repeat (match goal with H:_ |- _ => tac H end).


Tactic Notation "thus" constr(P) "as" ident(H) "by" constr(T)
  :=
  assert P as H by (eapply T; eauto).


Tactic Notation "thus" constr(P) "by" constr(T)
  :=
  assert P by (eapply T; eauto).


Tactic Notation "so" constr(T) "as" simple_intropattern(pat)
  :=
  pose proof T as pat.


Tactic Notation "so" constr(T)
  :=
  pose proof T.


(* Misc *)

Lemma rel_quest :
  forall (A : Type) (P : A -> Prop) (x y : A),
    P x
    -> x = y
    -> P y.
Proof.
intros; subst; auto.
Qed.

Lemma rel_quest_1 :
  forall (A B : Type) (P : A -> B -> Prop) (x y : A) (z : B),
    P x z
    -> x = y
    -> P y z.
Proof.
intros; subst; auto.
Qed.

Lemma rel_quest_2 :
  forall (A B C : Type) (P : A -> B -> C -> Prop) (x y : A) (z : B) (z' : C),
    P x z z'
    -> x = y
    -> P y z z'.
Proof.
intros; subst; auto.
Qed.

Ltac relquest := eapply rel_quest; [|].


(* Notation *)

Definition eintro {A : Type} {P : A -> Prop} (x : A) (H : P x) : (exists x, P x).
Proof.
eauto.
Qed.


Definition car {A B : Set} (p : A * B) := let (x, _) := p in x.
Definition cdr {A B : Set} (p : A * B) := let (_, y) := p in y.

Definition caar {A B C : Set} (p : A * B * C) := (car (car p)).
Definition caaar {A B C D : Set} (p : A * B * C * D) := (car (car (car p))).
Definition cdaar {A B C D : Set} (p : A * B * C * D) := (cdr (car (car p))).
Definition cdar {A B C : Set} (p : A * B * C) := (cdr (car p)).
Definition cadr {A B C : Set} (p : A * (B * C)) := (car (cdr p)).
Definition cddr {A B C : Set} (p : A * (B * C)) := (cdr (cdr p)).


Definition carp {P Q : Prop} (x : P /\ Q) : P.
elim x.
exact (fun p q => p).
Defined.

Definition cdrp {P Q : Prop} (x : P /\ Q) : Q.
elim x.
exact (fun p q => q).
Defined.

Definition cadrp {P Q R : Prop} (x : P /\ Q /\ R) := carp (cdrp x).
Definition cddrp {P Q R : Prop} (x : P /\ Q /\ R) := cdrp (cdrp x).


Notation "a 'andel'" := (carp a)
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'ander'" := (cdrp a)
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'anderl'" := (carp (cdrp a))
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'anderr'" := (cddrp a)
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'anderrl'" := (carp (cdrp (cdrp a)))
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'anderrr'" := (cdrp (cddrp a))
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'anderrrl'" := (carp (cdrp (cdrp (cdrp a))))
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'anderrrr'" := (cddrp (cddrp a))
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'anderrrrl'" := (carp (cddrp (cddrp a)))
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'anderrrrr'" := (cdrp (cddrp (cddrp a)))
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'anderrrrrl'" := (cadrp (cddrp (cddrp a)))
  (at level 11, left associativity, only parsing) : tactics_scope.

Notation "a 'anderrrrrr'" := (cddrp (cddrp (cddrp a)))
  (at level 11, left associativity, only parsing) : tactics_scope.


Notation " x _#2 " := (x _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#3 " := (x _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#4 " := (x _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#5 " := (x _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#6 " := (x _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#7 " := (x _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#8 " := (x _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#9 " := (x _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#10 " := (x _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#11 " := (x _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#12 " := (x _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#13 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#14 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#15 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#16 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#17 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#18 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#19 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.
Notation " x _#20 " := (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (at level 11, left associativity, only parsing) : tactics_scope.

Tactic Notation "#" "1" tactic(tac) := tac; [].
Tactic Notation "#" "2" tactic(tac) := tac; [|].
Tactic Notation "#" "3" tactic(tac) := tac; [| |].
Tactic Notation "#" "4" tactic(tac) := tac; [| | |].
Tactic Notation "#" "5" tactic(tac) := tac; [| | | |].
Tactic Notation "#" "6" tactic(tac) := tac; [| | | | |].
Tactic Notation "#" "7" tactic(tac) := tac; [| | | | | |].
Tactic Notation "#" "8" tactic(tac) := tac; [| | | | | | |].
Tactic Notation "#" "9" tactic(tac) := tac; [| | | | | | | |].
Tactic Notation "#" "10" tactic(tac) := tac; [| | | | | | | | |].
Tactic Notation "#" "11" tactic(tac) := tac; [| | | | | | | | | |].
Tactic Notation "#" "12" tactic(tac) := tac; [| | | | | | | | | | |].
Tactic Notation "#" "13" tactic(tac) := tac; [| | | | | | | | | | | |].
Tactic Notation "#" "14" tactic(tac) := tac; [| | | | | | | | | | | | |].
Tactic Notation "#" "15" tactic(tac) := tac; [| | | | | | | | | | | | | |].
Tactic Notation "#" "16" tactic(tac) := tac; [| | | | | | | | | | | | | | |].
Tactic Notation "#" "17" tactic(tac) := tac; [| | | | | | | | | | | | | | | |].
Tactic Notation "#" "18" tactic(tac) := tac; [| | | | | | | | | | | | | | | | |].
Tactic Notation "#" "19" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "20" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "21" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "22" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "23" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "24" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "25" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "26" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "27" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "28" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "29" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "30" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "31" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "32" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "33" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "34" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "35" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "36" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "37" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "38" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "39" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | |].
Tactic Notation "#" "40" tactic(tac) := tac; [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | |].

Open Scope tactics_scope.
