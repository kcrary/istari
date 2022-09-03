
Require Import Tactics.
Require Import Sigma.
Require Import Ofe.



(* We want to define a version of meta_rect (eventually called
   meta_nerect) in which the meta_fn case's induction hypothesis is
   given as a nonexpansive function (as opposed to the ordinary
   function used in meta_rect).  We also use the same technique
   to take the limit of a chain of type systems.

   This requires us to prove some properties about meta_nerect at the 
   same time as we are defining it, which cannot be done directly.

   Instead, we define a monad "poss A" (read "possibly A"), which is
   an A subject to proof obligations.  We define a helper function
   iurel_nerect_poss which (assuming C is the goal) returns poss C,
   instead of C.  Once it is defined, we can then prove things about
   it.  In particular, we can go back and show that the proof
   obligations are satisfied.  We can then apply the result of
   meta_nerect_poss to that proof, thereby obtaining a C.
*)


Definition poss (A : Type) : Type :=
  existsT (P : Prop), P -> A.


Definition poss_unit {A : Type} (x : A) : poss A :=
  expair True (fun _ => x).


Definition ex_pi1 {A : Prop} {B : A -> Prop} (p : exists (a : A), B a) : A
  :=
  match p with
  | ex_intro _ x _ => x
  end.


Definition ex_pi2 {A : Prop} {B : A -> Prop} (p : exists (a : A), B a) : B (ex_pi1 p)
  :=
  match p
    as e
    return B (ex_pi1 e)
  with
  | ex_intro _ x y => y
  end.


Definition poss_bind {A : Type} {B : Type} (x : poss A) (f : A -> poss B) : poss B
  :=
  @expair Prop (fun P => P -> B)
    (exists (px : pi1 x), pi1 (f (pi2 x px)))
    (fun p => pi2 (f (pi2 x (ex_pi1 p))) (ex_pi2 p)).


Definition poss_lift {A : Type} {B : Type} (f : A -> poss B) : poss (A -> B)
  :=
  @expair Prop (fun P => P -> A -> B)
    (forall (a : A), pi1 (f a))
    (fun p a => pi2 (f a) (p a)).


Definition poss_assume {A : Type} (P : Prop) (f : P -> poss A) : poss A
  :=
  @expair Prop (fun P => P -> A)
    (exists (px : P), pi1 (f px))
    (fun p => pi2 (f (ex_pi1 p)) (ex_pi2 p)).


Lemma poss_unit_true :
  forall A (x : A), pi1 (poss_unit x).
Proof.
intros A x.
cbn.
trivial.
Qed.


Lemma poss_bind_true :
  forall A B (x : poss A) (f : A -> poss B),
    forall (px : pi1 x),
      pi1 (f (pi2 x px))
      -> pi1 (poss_bind x f).
Proof.
intros A B x f Hx Hf.
cbn.
exists Hx.
exact Hf.
Qed.


Lemma poss_lift_true :
  forall A B (f : A -> poss B),
    (forall (a : A), pi1 (f a))
    -> pi1 (poss_lift f).
Proof.
intros A B f H.
cbn.
exact H.
Defined.


Lemma poss_assume_true :
  forall A (P : Prop) (f : P -> poss A),
    forall (p : P),
      pi1 (f p)
      -> pi1 (poss_assume P f).
Proof.
intros A P f p Hf.
cbn.
exists p.
exact Hf.
Qed.


Definition poss_dist {A : ofe} (n : nat) (x y : poss (car A)) : Prop
  :=
  forall (p : pi1 x) (q : pi1 y),
    dist n (pi2 x p) (pi2 y q).


Lemma poss_dist_if_pos :
  forall A n (x y : poss (car A)),
    (n > 0 -> poss_dist n x y)
    -> poss_dist n x y.
Proof.
intros A n x y Hdist p q.
apply dist_if_pos.
intro Hpos.
apply Hdist; auto.
Qed.


Lemma poss_dist_unit :
  forall A n (x y : car A),
    dist n x y
    -> poss_dist n (poss_unit x) (poss_unit y).
Proof.
intros A n x y Hdist.
intros p q.
cbn.
exact Hdist.
Qed.


Lemma poss_dist_bind :
  forall A B m n (x y : poss (car A)) (f g : car A -> poss (car B)),
    poss_dist m x y
    -> (forall x' y',
          dist m x' y'
          -> poss_dist n (f x') (g y'))
    -> poss_dist n (poss_bind x f) (poss_bind y g).
Proof.
intros A B m n x y f g Hxy Hfg.
intros p q.
apply Hfg.
apply Hxy.
Qed.


Lemma poss_dist_assume :
  forall (P Q : Prop) (A : ofe) n (f : P -> poss (car A)) (g : Q -> poss (car A)),
    (forall h h', poss_dist n (f h) (g h'))
    -> poss_dist n (poss_assume P f) (poss_assume Q g).
Proof.
intros P Q A n f g Hdist.
intros h h'.
apply Hdist.
Qed.


Definition poss_hyp {A : Type} (P : A -> Prop) (x : poss A) : Prop
  :=
  forall (p : pi1 x),
    P (pi2 x p).


Lemma poss_unit_hyp :
  forall A (P : A -> Prop) (x : A),
    P x
    -> poss_hyp P (poss_unit x).
Proof.
intros A P x H.
intros p.
cbn.
exact H.
Qed.


Lemma poss_bind_hyp :
  forall A B (P : A -> Prop) (Q : B -> Prop) (x : poss A) (f : A -> poss B),
    poss_hyp P x
    -> (forall (a : A), P a -> poss_hyp Q (f a))
    -> poss_hyp Q (poss_bind x f).
Proof.
intros A B P Q x f Hx Hf.
intro H.
cbn.
apply Hf.
apply Hx.
Qed.


Lemma poss_lift_hyp :
  forall A B (P : A -> B -> Prop) (f : A -> poss B),
    (forall a, poss_hyp (P a) (f a))
    -> poss_hyp (fun g => forall a, P a (g a)) (poss_lift f).
Proof.
intros A B P f Hf.
intros H a.
cbn.
apply Hf.
Qed.


Lemma poss_assume_hyp :
  forall A (P : Prop) (Q : A -> Prop) (f : P -> poss A),
    (forall (p : P), poss_hyp Q (f p))
      -> poss_hyp Q (poss_assume P f).
Proof.
intros A P Q f Hf.
intros H.
cbn.
apply Hf.
Qed.
