
Require Import Tactics.
Require Import Sigma.
Require Export Coq.Logic.EqdepFacts.

Require Import Axioms.


(* Equality *)

Definition transport {A : Type} {x x'} (e : @eq A x x') (P : A -> Type) (y : P x) : P x' :=
  eq_rect x P y x' e.

Definition eqsymm {A : Type} {x x'} (e : @eq A x x') : eq x' x :=
  eq_rect _ (fun y => eq y x) (eq_refl x) _ e.


Definition eqtrans {A : Type} {x y z : A} (e : x = y) (e' : y = z) : x = z :=
  eq_rect _ (fun w => w = z) e' _ (eqsymm e).


Definition eqcompat {A B : Type} {x y : A} (f : A -> B) (e : x = y) : f x = f y :=
  eq_rect _ (fun z => f x = f z) (eq_refl (f x)) _ e.


Lemma transport_left_inv :
  forall (A : Type) (B : A -> Type) (a a' : A) (x : B a) (e : a = a'),
    transport (eqsymm e) B (transport e B x) = x.
Proof.
intros A B a a' x e.
subst a'.
reflexivity.
Qed.


Lemma transport_right_inv :
  forall (A : Type) (B : A -> Type) (a a' : A) (x : B a') (e : a = a'),
    transport e B (transport (eqsymm e) B x) = x.
Proof.
intros A B a a' x e.
subst a'.
reflexivity.
Qed.


Lemma transport_compose :
  forall (A : Type) (B : A -> Type) (a1 a2 a3 : A) (x : B a1) (e1 : a1 = a2) (e2 : a2 = a3),
    transport e2 B (transport e1 B x) = transport (eqtrans e1 e2) B x.
Proof.
intros A B a1 a2 a3 x e1 e2.
subst a2 a3.
cbn.
reflexivity.
Qed.


Lemma transport_compat :
  forall A B (f : A -> B) (C : B -> Type) (a a' : A) (x : C (f a)) (h : a = a'),
    transport (eqcompat f h) C x
    =
    transport h (fun z => C (f z)) x.
Proof.
intros A B f C a a' x h.
subst a'.
cbn.
reflexivity.
Qed.


Lemma transport_back :
  forall A (B : A -> Type) a a' (h : a = a') (h' : a' = a) (x : B a),
    transport h' B (transport h B x) = x.
Proof.
intros A B a a' h h' x.
subst a'.
substrefl h'.
cbn.
reflexivity.
Qed.


Lemma transport_self :
  forall (A : Type) (B : A -> Type) (a : A) (h : a = a) x,
    transport h B x = x.
Proof.
intros A a a' h.
substrefl h.
auto.
Qed.


Lemma transport_symm :
  forall A (B : A -> Type) (a a' : A) (h : a = a') (x : B a) (y : B a'),
    transport h B x = y
    -> x = transport (eqsymm h) B y.
Proof.
intros A B a a' h x y Heq.
subst a'.
exact Heq.
Qed.


Lemma transport_symm' :
  forall A (B : A -> Type) (a a' : A) (h : a' = a) (x : B a) (y : B a'),
    transport (eqsymm h) B x = y
    -> x = transport h B y.
Proof.
intros A B a a' h x y Heq.
subst a'.
exact Heq.
Qed.


Lemma transport_const :
  forall A B (a a' : A) (h : a = a') (b : B),
    transport h (fun _ => B) b = b.
Proof.
intros A B a a' h b.
subst a'.
reflexivity.
Qed.


(* Usually need to fill in C and h. *)
Lemma pi1_transport_lift :
  forall (A : Type) (B : Type) (C : A -> B -> Type) 
    (a a' : A) (h : a = a') (x : exT B (C a)),
      pi1 (transport h (fun a'' => exT B (C a'')) x)
      = pi1 x.
Proof.
intros A B C a a' h x.
subst a'.
reflexivity.
Qed.


Lemma pi1_transport_dep_lift :
  forall (A : Type) (B : A -> Type) (C : forall (a:A), B a -> Type)
    (a a' : A) (h : a = a') (x : exT (B a) (C a)),
      pi1 (transport h (fun z => exT (B z) (C z)) x)
      =
      transport h B (pi1 x).
Proof.
intros A B C a a' h x.
subst a'.
cbn.
reflexivity.
Qed.


Lemma app_transport_dom :
  forall (A : Type) (B : A -> Type) (C : Type) (a a' : A) (h : a = a') 
    (f : B a -> C) (x : B a'),
      transport h (fun z => B z -> C) f x
      =
      f (transport (eqsymm h) B x).
Proof.
intros A B C a a' h f x.
subst a'.
cbn.
reflexivity.
Qed.


Lemma app_transport_cod_dep :
  forall (A : Type) (B : Type) (C : A -> B -> Type) (a a' : A) (h : a = a') 
    (f : forall (b:B), C a b) (x : B),
      transport h (fun z => forall (b:B), C z b) f x
      =
      transport h (fun z => C z x) (f x).
Proof.
intros A B C a a' h f x.
subst a'.
reflexivity.
Qed.


Lemma transport_commute :
  forall A B (f : A -> B) (C : B -> Type) a a' (h : a = a') (x : C (f a)),
    transport h (fun z => C (f z)) x
    =
    transport (f_equal f h) C x.
Proof.
intros A B f C a a' h x.
subst a'.
reflexivity.
Qed.    


Lemma transport_f_equal :
  forall A B (C : B -> Type) (f : A -> B) (a a' : A) (h : a = a') (x : C (f a)),
    transport (f_equal f h) C x
    =
    transport h (fun z => C (f z)) x.
Proof.
intros A B C f a a' h x.
subst a'.
cbn.
reflexivity.
Qed.


Lemma prod_extensionality :
  forall A B (p q : A * B),
    fst p = fst q
    -> snd p = snd q
    -> p = q.
Proof.
intros A B p q Hfst Hsnd.
destruct p as (a, b).
destruct q as (c, d).
f_equal; auto.
Qed.


(* Dependent equality *)

Definition transportdep {A:Type} {B : A -> Type} {a a' : A} {b : B a} {b' : B a'}
  (e : eq_dep A B a b a' b')
  (P : forall a, B a -> Type)
  (x : P a b)
  : P a' b'
  :=
  eq_dep_rect A B a b P x a' b' e.


Lemma eq_impl_eq_dep_snd :
  forall A (B : A -> Type) a (b b' : B a), 
    b = b'
    -> eq_dep _ _ a b a b'.
Proof.
intros A B a b b' H.
subst b'.
apply eq_dep_refl.
Qed.    


Lemma eq_impl_eq_dep_fst :
  forall A (B : A -> Type) (a a' : A) (b : forall a, B a),
    a = a'
    -> eq_dep _ _ a (b a) a' (b a').
Proof.
intros A B a a' b H.
subst a'.
apply eq_dep_refl.
Qed.


Lemma eq_impl_eq_dep :
  forall A (B : A -> Type) (a a' : A) (b : B a) (b' : B a') (h : a = a'),
    transport h B b = b'
    -> eq_dep A B a b a' b'.
Proof.
intros A B a a' b b' h H.
subst a'.
subst b'.
cbn.
apply eq_dep_refl.
Qed.    


Lemma eq_impl_eq_dep_free :
  forall A B (a a' : A) (b b' : B),
    a = a'
    -> b = b'
    -> eq_dep _ (fun _ => B) a b a' b'.
Proof.
intros A B a a' b b' Heq Heq'.
subst a' b'.
reflexivity.
Qed.


Lemma transport_eq_transportdep_snd :
  forall A (B : A -> Type) (C : forall a, B a -> Type) a (b b' : B a) (h : b = b') (x : C a b),
    transport h (C a) x
    =
    transportdep (eq_impl_eq_dep_snd A B a b b' h) C x.
Proof.
intros A B C a b b' h x.
subst b'.
replace (eq_impl_eq_dep_snd A B a b b eq_refl) with (eq_dep_intro A B a b) by (apply proof_irrelevance).
cbn.
reflexivity.
Qed.


Lemma transport_eq_transportdep_fst :
  forall A (B : A -> Type) (C : forall a, B a -> Type) (a a' : A) (b : forall a, B a) 
    (h : a = a') (x : C a (b a)),
      transport h (fun z => C z (b z)) x
      =
      transportdep (eq_impl_eq_dep_fst A B a a' b h) C x.
Proof.
intros A B C a a' b h x.
subst a'.
replace (eq_impl_eq_dep_fst A B a a b eq_refl) with (eq_dep_intro A B a (b a)) by (apply proof_irrelevance).
cbn.
reflexivity.
Qed.


Lemma transportdep_compose :
  forall (A : Type) (B : A -> Type) (C : forall a, B a -> Type) 
    (a1 a2 a3 : A) (b1 : B a1) (b2 : B a2) (b3 : B a3) (x : C a1 b1)
    (e1 : eq_dep _ _ a1 b1 a2 b2) (e2 : eq_dep _ _ a2 b2 a3 b3),
      transportdep e2 C (transportdep e1 C x)
      =
      transportdep (eq_dep_trans _#8 e1 e2) C x.
Proof.
intros A B C a1 a2 a3 b1 b2 b3 x e1 e2.
case e2.
case e1.
cbn.
(* This next step shouldn't be necessary, but since eq_dep_trans is opaque, it doesn't reduce. *)
replace (eq_dep_trans A B a1 a1 a1 b1 b1 b1 (eq_dep_intro A B a1 b1) (eq_dep_intro A B a1 b1)) with (eq_dep_intro A B a1 b1) by (apply proof_irrelevance).
cbn.
reflexivity.
Qed.


Lemma eq_dep_impl_eq :
  forall A (B : A -> Type) (a a' : A) (b : B a) (b' : B a'),
    eq_dep _ _ a b a' b'
    -> exists (h : a = a'), transport h B b = b'.
Proof.
intros A B a a' b b' H.
induct H.
exists (eq_refl _).
cbn.
reflexivity.
Qed.


Lemma eq_dep_impl_eq_fst :
  forall A (B : A -> Type) (a a' : A) (b : B a) (b' : B a'),
    eq_dep _ _ a b a' b'
    -> a = a'.
Proof.
intros A B a a' b b' H.
so (eq_dep_impl_eq _#6 H) as (h & _).
exact h.
Qed.


Lemma eq_dep_impl_eq_snd :
  forall A (B : A -> Type) (a : A) (b : B a) (b' : B a),
    eq_dep _ _ a b a b'
    -> b = b'.
Proof.
intros A B a b b' H.
so (eq_dep_impl_eq _#6 H) as (h & H').
substrefl h.
exact H'.
Qed.


Lemma eq_dep_impl_eq_snd_free :
  forall A (B : Type) (a a' : A) (b b' : B),
    eq_dep _ _ a b a' b'
    -> b = b'.
Proof.
intros A B a a' b b' Heq.
so (eq_dep_impl_eq_fst _#6 Heq); subst a'.
exact (eq_dep_impl_eq_snd _#5 Heq).
Qed.


Lemma eq_dep_pi1 :
  forall (A : Type) (B : A -> Type) (C : forall a, B a -> Type) (a a' : A)
    (x : exT (B a) (C a)) (y : exT (B a') (C a')),
      eq_dep _ (fun a => exT (B a) (C a)) a x a' y
      -> eq_dep _ B a (pi1 x) a' (pi1 y).
Proof.
intros A B C a a' x y Heq.
so (eq_dep_impl_eq_fst _#6 Heq); subst a'.
so (eq_dep_impl_eq_snd _#5 Heq); subst y.
reflexivity.
Qed.


Lemma eq_dep_prod_fst :
  forall A B (C : A -> Type) (x x' : A * B) (y : C (fst x)) (y' : C (fst x')),
    snd x = snd x'
    -> eq_dep A C (fst x) y (fst x') y'
    -> eq_dep (A * B) (fun z => C (fst z)) x y x' y'.
Proof.
intros A B C x x' y y' Hsnd Heq.
destruct x as (a, b).
destruct x' as (a', b').
cbn in y, y', Hsnd, Heq.
subst b'.
so (eq_dep_impl_eq_fst _#6 Heq).
subst a'.
so (eq_dep_impl_eq_snd _#5 Heq).
subst y'.
apply eq_dep_refl.
Qed.


Lemma functional_extensionality_eq_dep_dom :
  forall A (B : A -> Type) C (a a' : A) (f : B a -> C) (f' : B a' -> C),
    a = a'
    -> (forall (x : B a) (x' : B a'),
          eq_dep A B a x a' x' -> f x = f' x')
    -> eq_dep A (fun z => B z -> C) a f a' f'.
Proof.
intros A B C a a' f f' Heqa H.
subst a'.
apply eq_impl_eq_dep_snd.
fextensionality 1.
intro x.
apply H.
apply eq_dep_refl.
Qed.


Lemma functional_extensionality_eq_dep_cod :
  forall A B (C : A -> Type) (a a' : A) (f : B -> C a) (f' : B -> C a'),
    a = a'
    -> (forall (x : B), eq_dep A C a (f x) a' (f' x))
    -> eq_dep A (fun z => B -> C z) a f a' f'.
Proof.
intros A B C a a' f f' Heqa H.
subst a'.
apply eq_impl_eq_dep_snd.
fextensionality 1.
intro y.
apply eq_dep_impl_eq_snd; auto.
Qed.


Lemma functional_extensionality_eq_dep_cod' :
  forall A B (C : A -> Type) (a a' : A) (f : B -> C a) (f' : B -> C a'),
    B
    -> (forall (x : B), eq_dep A C a (f x) a' (f' x))
    -> eq_dep A (fun z => B -> C z) a f a' f'.
Proof.
intros A B C a a' f f' x H.
so (eq_dep_impl_eq_fst _#6 (H x)); subst a'.
apply eq_impl_eq_dep_snd.
fextensionality 1.
intro y.
apply eq_dep_impl_eq_snd; auto.
Qed.


(* Heterogeneous (so-called "John Major") equality.

   Exists in the standard library as JMeq.  Redefine it here
   because the Coq tactic library silently uses axioms when
   you use JMeq.
*)

Inductive heq {A : Type} (x : A) : forall {B : Type}, B -> Prop :=
| heq_refl : heq x x.


Hint Resolve heq_refl.


Lemma heq_trans :
  forall A B C (a : A) (b : B) (c : C),
    heq a b
    -> heq b c
    -> heq a c.
Proof.
intros A B C a b c Hab Hbc.
revert Hbc.
induct Hab.
auto.
Qed.


Lemma heq_symm :
  forall A B (a : A) (b : B), heq a b -> heq b a.
Proof.
intros A B a b H.
induct H.
apply heq_refl.
Qed.    


Lemma heq_transport :
  forall A (B : A -> Type) a a' (h : a = a') (x : B a),
    heq (transport h B x) x.
Proof.
intros A B a a' h x.
subst a'.
cbn.
apply heq_refl.
Qed.


Lemma eq_impl_heq :
  forall A (x y : A),
    x = y
    -> heq x y.
Proof.
intros A x y H.
subst y.
apply heq_refl.
Qed.


Lemma heq_impl_eq :
  forall (A : Type) (x y : A),
    heq x y 
    -> x = y.
Proof.
cut (forall (A B : Type) (x : A) (y : B) (e : A = B),
       heq x y
       -> eq_rect _ (fun z => z) x _ e = y).
  {
  intros H A x y Heq.
  exact (H A A x y (eq_refl _) Heq).
  }
intros A B x y e H.
revert e.
destruct H.
intro e.
pose proof (proof_irrelevance _ e (eq_refl _)).
subst e.
simpl.
reflexivity.
Qed.


Lemma eq_heq_impl_eq_dep :
  forall A (B : A -> Type) (a a' : A) (b : B a) (b' : B a'),
    a = a'
    -> heq b b'
    -> eq_dep A B a b a' b'.
Proof.
intros A B a a' b b' Heqa Heqb.
subst a'.
apply eq_impl_eq_dep_snd.
apply heq_impl_eq; auto.
Qed.


Lemma heq_pair :
  forall A A' B B' (a : A) (a' : A') (b : B) (b' : B'),
    heq a a'
    -> heq b b'
    -> heq (a, b) (a', b').
Proof.
intros A A' B B' a a' b b' Ha.
cases Ha.
intro Hb.
cases Hb.
apply heq_refl.
Qed.


Lemma heq_prop :
  forall (A B : Prop) (a : A) (b : B), heq a b.
Proof.
intros A B a b.
assert (A = B).
  {
  pextensionality; auto.
  }
subst B.
apply eq_impl_heq.
apply proof_irrelevance.
Qed.


(* SigT *)

(* For use with the built-in injection tactic. *)
Lemma existT_injection_2 :
  forall (T : Type) (P : T -> Type) (x : T) (y y' : P x),
    existT _ x y = existT _ x y'
    -> y = y'.
Proof.
intros T P x y y' Heq.
assert (heq (projT2 (existT _ x y)) (projT2 (existT _ x y'))) as Heq'.
  {
  rewrite -> Heq; [].
  apply heq_refl.
  }
simpl in Heq'.
apply heq_impl_eq; auto.
Qed.


(* Sigma *)

Lemma exT_extensionality :
  forall (A : Type) (P : A -> Type) (x y : exT A P),
    forall (h : pi1 x = pi1 y),
      transport h P (pi2 x) = pi2 y
      -> x = y.
Proof.
intros A P x y Heq1 Heq2.
destruct x as [x1 x2].
destruct y as [y1 y2].
simpl in Heq1.
subst y1.
simpl in Heq2.
subst y2.
reflexivity.
Qed.


Lemma existsT_unique_equal :
  forall (A : Type) (P : A -> Type),
    (existsT! (x : A), P x)
    -> forall x y, P x -> P y -> x = y.
Proof.
intros A P H x y Hx Hy.
destruct H as (z & _ & Hunique).
transitivity z.
- symmetry; apply Hunique; auto.

- apply Hunique; auto.
Qed.


Lemma expair_injection_1 :
  forall (T : Type) (P : T -> Type) (x x' : T) (y : P x) (y' : P x'),
    expair x y = expair x' y'
    -> x = x'.
Proof.
intros T P x x' y y' Heq.
assert (pi1 (expair x y) = pi1 (expair x' y')) as Heq'.
  {
  rewrite -> Heq.
  reflexivity.
  }
simpl in Heq'.
exact Heq'.
Qed.


Lemma expair_eta :
  forall S (T : S -> Type) (x : exT S T),
    expair (pi1 x) (pi2 x) = x.
Proof.
intros S T x.
destruct x.
simpl; reflexivity.
Qed.


Lemma exT_extensionality_prop :
  forall (A : Type) (P : A -> Prop) (x y : exT A P),
    pi1 x = pi1 y
    -> x = y.
Proof.
intros A P x y Heq.
apply (exT_extensionality _ _ _ _ Heq); [].
apply proof_irrelevance.
Qed.


Lemma exT_extensionality_prop_eq_dep :
  forall A (B : A -> Type) (P : forall a, B a -> Prop) (a a' : A) (x : exT (B a) (P a)) (x' : exT (B a') (P a')),
    eq_dep A B a (pi1 x) a' (pi1 x')
    -> eq_dep A (fun z => exT (B z) (P z)) a x a' x'.
Proof.
intros A B P a a' x x' H.
so (eq_dep_impl_eq_fst _#6 H); subst a'.
apply eq_impl_eq_dep_snd.
apply exT_extensionality_prop.
apply eq_dep_impl_eq_snd; auto.
Qed.


Lemma expair_injection_2 :
  forall (T : Type) (P : T -> Type) (x : T) (y y' : P x),
    expair x y = expair x y'
    -> y = y'.
Proof.
intros T P x y y' Heq.
assert (heq (pi2 (expair x y)) (pi2 (expair x y'))) as Heq'.
  {
  rewrite -> Heq; [].
  apply heq_refl.
  }
simpl in Heq'.
apply heq_impl_eq; auto.
Qed.


Lemma expair_injection_transport :
  forall (T : Type) (P : T -> Type) (x x' : T) (y : P x) (y' : P x'),
    expair x y = expair x' y'
    -> exists (h : x = x'), transport h P y = y'.
Proof.
intros T P x x' y y' Heq.
so (expair_injection_1 _#6 Heq).
subst x'.
exists (eq_refl _).
cbn.
exact (expair_injection_2 _#5 Heq).
Qed.


Lemma expair_injection_dep :
  forall A (B : A -> Type) a a' (b : B a) (b' : B a'),
    expair a b = expair a' b'
    -> eq_dep A B a b a' b'.
Proof.
intros A B a a' b b' H.
so (expair_injection_1 _#6 H); subst a'.
so (expair_injection_2 _#5 H); subst b'.
reflexivity.
Qed.


Lemma expair_compat_dep :
  forall A (B : A -> Type) a a' (b : B a) (b' : B a'),
    eq_dep A B a b a' b'
    -> expair a b = expair a' b'.
Proof.
intros A B a a' b b' H.
so (eq_dep_impl_eq_fst _#6 H); subst a'.
so (eq_dep_impl_eq_snd _#5 H); subst b'.
reflexivity.
Qed.


Lemma expair_compat_heq :
  forall A (B : A -> Type) a a' (b : B a) (b' : B a'),
    a = a'
    -> heq b b'
    -> expair a b = expair a' b'.
Proof.
intros A B a a' b b' ? Heq.
subst a'.
so (heq_impl_eq _#3 Heq).
subst b'.
reflexivity.
Qed.


Lemma expair_compat_transport :
  forall A (B : A -> Type) a a' (b : B a) (b' : B a') (h : a = a'),
    transport h B b = b'
    -> expair a b = expair a' b'.
Proof.
intros A B a a' b b' h H.
subst a'.
cbn in H.
subst b'.
reflexivity.
Qed.


Lemma exT_equal :
  forall (A : Type) (B : A -> Type) (C C' : forall a, B a -> Type) (a a' : A),
    eq_dep A (fun a => B a -> Type) a (C a) a' (C' a')
    -> exT (B a) (C a) = exT (B a') (C' a').
Proof.
intros A B C C' a a' Heq.
so (eq_dep_impl_eq_fst _#6 Heq).
subst a'.
f_equal.
exact (eq_dep_impl_eq_snd _#5 Heq).
Qed.


Ltac injectionT H :=
  let H' := fresh H
  in
    match type of H with
    | existT _ ?x _ = existT _ ?x _ =>
        so (existT_injection_2 _#5 H) as H';
        clear H;
        revert H'

    | expair ?x _ = expair ?x _ =>
        so (expair_injection_2 _#5 H) as H';
        clear H;
        revert H'

    | eq_dep _ _ ?x _ ?x _ =>
        so (eq_dep_impl_eq_snd _#5 H) as H';
        clear H;
        revert H'

    | eq_dep _ _ ?x _ ?y _ =>
        so (eq_dep_impl_eq_fst _#6 H) as H';
        revert H'
    end.


Lemma f_equal_dep :
  forall A (B : A -> Type) (C : Type) (a a' : A) (b : B a) (b' : B a') (f : forall a, B a -> C),
    eq_dep A B a b a' b'
    -> f a b = f a' b'.
Proof.
intros A B C a a' b b' f Heq.
injectionT Heq.
intros <-.
injectionT Heq.
intros <-.
reflexivity.
Qed.
