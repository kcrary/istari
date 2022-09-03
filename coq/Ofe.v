
Require Import Coq.Relations.Relation_Definitions.

Require Import Axioms.

Require Import Tactics.
Require Import Equality.
Require Import Sigma.


Local Open Scope type_scope.



(* Ordered families of equivalences *)

Record ofe : Type :=
mk_ofe
  { car : Type;
    dist : nat -> (relation car);
    dist_eqrel : forall n, equiv car (dist n);
    dist_limeq : forall x y, (forall n, dist n x y) -> x = y;
    dist_downward : forall n x y, dist (S n) x y -> dist n x y;
    dist_zero : forall x y, dist 0 x y }.

Arguments dist {o} n x y.


Definition dist_refl (A : ofe) n := dist_eqrel A n andel.
Definition dist_trans (A : ofe) n := dist_eqrel A n anderl.
Definition dist_symm (A : ofe) n := dist_eqrel A n anderr.


Lemma dist_refl' :
  forall A n (x y : car A),
    x = y
    -> dist n x y.
Proof.
intros A n x y H.
subst y.
apply dist_refl.
Qed.


Lemma downward_leq :
  forall (A : Type) (R : nat -> relation A) m n (x y : A),
    (forall n x y, R (S n) x y -> R n x y)
    -> m <= n
    -> R n x y
    -> R m x y.
Proof.
intros A R m n x y Hdownward Hleq Hdist.
revert Hdist.
induct Hleq; auto.
Qed.


Lemma dist_downward_leq :
  forall (A : ofe) m n (x y : car A),
    m <= n
    -> dist n x y
    -> dist m x y.
Proof.
intros A m n x y Hleq Hdist.
eapply downward_leq; eauto; [].
intros; apply dist_downward; auto.
Qed.


Lemma dist_downward_pred :
  forall (A : ofe) n (x y : car A),
    dist n x y
    -> dist (pred n) x y.
Proof.
intros A n x y H.
destruct n as [| n'].
- simpl.
  apply dist_zero.

- simpl.
  apply dist_downward; auto.
Qed.


Lemma dist_if_pos :
  forall (A : ofe) n (x y : car A),
    (n > 0 -> dist n x y)
    -> dist n x y.
Proof.
intros A n x y Hdist.
destruct n as [| n].
  {
  apply dist_zero.
  }
apply Hdist.
omega.
Qed.


(* Nonexpansiveness/Contractiveness *)

Definition nonexpansive {A B : ofe} (f : car A -> car B) :=
  forall n x y, dist n x y -> dist n (f x) (f y).

Definition contractive {A B : ofe} (f : car A -> car B) :=
  forall n x y, dist n x y -> dist (S n) (f x) (f y).


Lemma ident_nonexpansive :
  forall (A : ofe),
    @nonexpansive A A (fun x => x).
Proof.
intros A n x y Hxy.
assumption.
Qed.


Lemma const_nonexpansive :
  forall (A B : ofe) (x : car B),
    @nonexpansive A B (fun _ => x).
Proof.
intros A B x.
intros n _ _ _.
apply dist_refl.
Qed.


Lemma transport_nonexpansive :
  forall A (B : A -> ofe) i a a' (x y : car (B a)) (h : a = a'),
    @dist (B a) i x y
    -> @dist (B a') i (transport h (fun z => car (B z)) x) (transport h (fun z => car (B z)) y).
Proof.
intros A B i a a' x y h Hdist.
subst a'.
cbn.
exact Hdist.
Qed.


(* not used anywhere *)
Lemma transport_noncontractive :
  forall A (B : A -> ofe) i a a' (x y : car (B a)) (h : a = a'),
    dist i (transport h (fun z => car (B z)) x) (transport h (fun z => car (B z)) y)
    -> dist i x y.
Proof.
intros A B i a a' x y h H.
subst a'.
auto.
Qed.


Lemma compose_ne_ne :
  forall (A B C : ofe) f g,
    @nonexpansive B C f
    -> @nonexpansive A B g
    -> nonexpansive (fun x => f (g x)).
Proof.
intros A B C f g Hnef Hneg.
intros n x y Hxy.
so (Hneg _#3 Hxy) as Hgxy.
so (Hnef _#3 Hgxy) as Hfgxy.
exact Hfgxy.
Qed.


(* Convergence *)

Definition convergent {A : Type} (d : nat -> relation A) (f : nat -> A) :=
  forall n, d n (f n) (f (S n)).

Lemma convergent_leq_gen :
  forall A (R : nat -> relation A) f,
    (forall n, equiv _ (R n))
    -> (forall n x y, R (S n) x y -> R n x y)
    -> convergent R f
    -> forall m n, m <= n -> R m (f m) (f n).
Proof.
intros A R f Hequiv Hdownward Hconv m n Hleq.
induct Hleq.

(* eq *)
{
apply (Hequiv _ andel).
}

(* S *)
{
intros n Hleq IH.
apply (Hequiv m anderl _ (f n)); auto; [].
eapply downward_leq; eauto.
}
Qed.


Lemma convergent_leq :
  forall A f,
    convergent (@dist A) f
    -> forall m n, m <= n -> dist m (f m) (f n).
Proof.
intros A f Hconv m n Hleq.
apply convergent_leq_gen; auto.
- auto using dist_eqrel.

- auto using dist_downward.
Qed.


Lemma const_convergent :
  forall A x,
    convergent (@dist A) (fun _ => x).
Proof.
intros A x.
intros n.
apply dist_refl; done.
Qed.


Lemma map_convergent_prim :
  forall (A B : Type) (d : nat -> relation A) (d' : nat -> relation B) (ch : nat -> A) (f : A -> B),
    (forall n x y, d n x y -> d' n (f x) (f y))
    -> convergent d ch
    -> convergent d' (fun i => f (ch i)).
Proof.
intros A B d d' ch f Hne Hconv.
intro i.
apply Hne; [].
apply Hconv.
Qed.


Lemma map_convergent :
  forall (A B : ofe) (ch : nat -> car A) (f : car A -> car B),
    nonexpansive f
    -> convergent (@dist A) ch
    -> convergent (@dist B) (fun i => f (ch i)).
Proof.
intros A B ch f Hne Hconv.
eapply map_convergent_prim; eauto.
Qed.


(* Limits *)

(* It's convenient to require that cofes be nonempty, since they are easier
   to work with, and all the cofes we consider are nonempty anyway.

   Now that I've embraced the description axiom, I would probably state
   completeness more conveniently, as an existence statement in Prop.
   Maybe change it if I ever make serious use of completeness.
*)
Record complete (A : ofe) : Type :=
mk_complete
  { limit : forall ch, convergent dist ch -> car A;
    inhabitant : car A;

    complete_dist : forall ch n (p : convergent dist ch), dist n (limit ch p) (ch n) }.

Arguments limit {A} c.
Arguments inhabitant {A} c.


(* Give limit a less-awful interface. *)
Definition limits {A : ofe} (ch : nat -> car A) (x : car A) :=
  forall n,
    dist n (ch n) x.


Lemma limits_to_limit :
  forall (A : ofe) (C : complete A) (ch : nat -> car A) (x : car A),
    limits ch x
    -> forall p, limit C ch p = x.
Proof.
intros A C ch x Hlimits Hconv.
apply dist_limeq; [].
intro n.
eapply dist_trans.
  - apply complete_dist.

  - apply Hlimits.
Qed.


Lemma limit_to_limits :
  forall (A : ofe) (C : complete A) (ch : nat -> car A) (p : convergent (@dist A) ch),
    limits ch (limit C ch p).
Proof.
intros A C ch p.
intro n.
apply dist_symm; [].
apply complete_dist.
Qed.


Lemma limits_unique :
  forall (A : ofe) (ch : nat -> car A) (x y : car A),
    limits ch x
    -> limits ch y
    -> x = y.
Proof.
intros A ch x y Hlimx Hlimy.
apply dist_limeq; [].
intro n.
eapply dist_trans.
- apply dist_symm; [].
  apply Hlimx.

- apply Hlimy.
Qed.


Lemma limits_const :
  forall (A : ofe) (x : car A),
    limits (fun i => x) x.
Proof.
intros A x.
intro n.
apply dist_refl.
Qed.


Lemma limits_truncate :
  forall (A : ofe) (ch : nat -> car A) (x : car A) n,
    limits ch x
    -> limits (fun i => ch (Nat.add n i)) x.
Proof.
intros A ch x n Hlim.
intro i.
apply (dist_downward_leq _ i (n+i)).
- omega.

- apply Hlim.
Qed.


(* We could strengthen this lemma (eliminate the convergent requirement)
   if we weakened the definition of limits to permit slower convergence.
   But the stronger convergence is awfully convenient, and this isn't unworkable.
*)
Lemma limits_prepend :
  forall (A : ofe) (C : complete A) (ch : nat -> car A) (x : car A) n,
    convergent (@dist A) ch
    -> limits (fun i => ch (n + i)%nat) x
    -> limits ch x.
Proof.
intros A C ch x n Hconv Hlim.
so (limit_to_limits _ C _ Hconv) as Hlim'.
so (limits_truncate _#3 n Hlim') as Hlim''.
so (limits_unique _#4 Hlim Hlim'').
subst x.
exact Hlim'.
Qed.


Lemma limits_convergent :
  forall (A : ofe) (ch : nat -> car A) (x : car A),
    limits ch x
    -> convergent (@dist A) ch.
Proof.
intros A ch x Hlim.
intro i.
apply (dist_trans _ _ _ x).
- apply Hlim.

- apply dist_symm; [].
  apply dist_downward; [].
  apply Hlim.
Qed.


Lemma ofe_fixpoint :
  forall (A : ofe) (C : complete A) (f : car A -> car A),
    contractive f
    -> existsT! (x : car A), f x = x.
Proof.
intros A C f Hcontract.
set (ch := @nat_rect (fun _ => car A) (inhabitant C) (fun _ x => f x)).
assert (convergent (@dist A) ch) as p.
  {
  intros i.
  induct i.
  - apply dist_zero.

  - intros i IH.
    simpl.
    apply Hcontract; [].
    exact IH.
  }
exists (limit C ch p).
assert (f (limit C ch p) = limit C ch p) as Hfix.
  {
  so (limit_to_limits A C ch p) as Hlimits.
  apply (limits_unique _ ch); auto; [].
  apply (limits_prepend _ C _ _ 1); auto; [].
  simpl.
  intro i.
  apply dist_downward; [].
  apply Hcontract; [].
  apply Hlimits.
  }
split; auto; [].
intros y Hfix'.
apply dist_limeq; [].
intro i.
induct i.
- apply dist_zero.

- intros i IH.
  rewrite <- Hfix; [].
  rewrite <- Hfix'; [].
  apply Hcontract.
  assumption.
Qed.


(* Nonexpansive function space *)

Definition nearrow (A B : ofe) : Type := exT (car A -> car B) (@nonexpansive A B).


Notation "A -n> B" := (nearrow A B)
  (at level 99, right associativity) : ofe_scope.


Open Scope ofe_scope.


Definition nearrow_const (A : ofe) (B : ofe) (x : car B) : A -n> B :=
  expair (fun _ => x) (const_nonexpansive A B x).


Definition idne {A : ofe} : A -n> A := expair _ (ident_nonexpansive A).


Definition dist_ne {A B : ofe} n (f g : A -n> B) := forall x, dist n (pi1 f x) (pi1 g x).


Definition limit_ne {A B : ofe} (C : complete B) :
  forall ch, convergent (@dist_ne A B) ch -> A -n> B.
Proof.
intros f Hconv.
exists (fun x : car A => limit C (fun i => pi1 (f i) x) (fun n => Hconv n x)).
intros n x y Hdist.
apply (dist_trans B n _ (pi1 (f n) x)).
- so (complete_dist B C _ n (fun n => Hconv n x)) as H.
  simpl in H.
  exact H.

- apply (dist_trans B n _ (pi1 (f n) y)).
  + so (pi2 (f n)) as Hne.
    exact (Hne n x y Hdist).

  + apply (dist_symm B n); [].
    so (complete_dist B C _ n (fun n => Hconv n y)) as H.
    simpl in H.
    exact H.
Defined.


Lemma nearrow_extensionality :
  forall A B (f g : A -n> B),
    (forall x, pi1 f x = pi1 g x)
    -> f = g.
Proof.
intros A B f g H.
apply exT_extensionality_prop.
fextensionality 1.
exact H.
Qed.


Lemma nearrow_extensionality_dep :
  forall A (B : A -> ofe) (C : ofe) (a a' : A) (f : B a -n> C) (g : B a' -n> C),
    eq_dep A (fun a => car (B a) -> car C) a (pi1 f) a' (pi1 g)
    -> eq_dep A (fun a => B a -n> C) a f a' g.
Proof.
intros A B C a a' f g Heq.
so (eq_dep_impl_eq_fst _#6 Heq); subst a'.
so (eq_dep_impl_eq_snd _#5 Heq) as Heq'.
apply eq_impl_eq_dep_snd.
apply exT_extensionality_prop; auto.
Qed.


Definition nearrow_ofe (A B : ofe) : ofe.
Proof.
apply 
  (mk_ofe 
     (A -n> B)
     (@dist_ne A B)).

(* eqrel *)
{
intro n.
do2 2 split.
+ intros f x.
  apply (dist_refl B n).

+ intros f g h Hfg Hgh x.
  eapply (dist_trans B n); eauto.

+ intros f g H x.
  apply (dist_symm B n); [].
  apply H.
}

(* limeq *)
{
intros f g Hsim.
destruct f as [f Hnef].
destruct g as [g Hneg].
cut (f = g).
  {
  intro.
  subst g.
  f_equal; [].
  apply proof_irrelevance.
  }
apply functional_extensionality; [].
intro x.
apply (dist_limeq B); [].
intro n.
exact (Hsim n x).
}

(* downward *)
{
intros n f g Hdist.
intro x.
apply (dist_downward B); [].
exact (Hdist x).
}

(* zero *)
{
intros f g x.
apply dist_zero.
}
Defined.


Definition nearrow_complete (A : ofe) (B : ofe) (C : complete B) : complete (nearrow_ofe A B).
Proof.
apply 
  (mk_complete (nearrow_ofe A B)
     (@limit_ne A B C)
     (expair (fun _ => inhabitant C) (const_nonexpansive _ _ _))).
intros f n Hconv.
intro x.
cbn.
apply (complete_dist B).
Defined.


Definition nearrow_id (A : ofe) : A -n> A :=
  expair _ (ident_nonexpansive A).

Definition nearrow_compose {A B C : ofe} (f : B -n> C) (g : A -n> B) : A -n> C :=
  expair _ (compose_ne_ne A B C (pi1 f) (pi1 g) (pi2 f) (pi2 g)).


Lemma nearrow_compose_id_left :
  forall A B (f : A -n> B),
    nearrow_compose (nearrow_id B) f = f.
Proof.
intros A B f.
destruct f as [f Hne].
unfold nearrow_compose.
f_equal; [].
apply proof_irrelevance; done.
Qed.


Lemma nearrow_compose_id_right :
  forall A B (f : A -n> B),
    nearrow_compose f (nearrow_id A) = f.
Proof.
intros A B f.
destruct f as [f Hne].
unfold nearrow_compose.
f_equal; [].
apply proof_irrelevance; done.
Qed.


Lemma nearrow_compose_assoc :
  forall A B C D (f : C -n> D) (g : B -n> C) (h : A -n> B),
    nearrow_compose (nearrow_compose f g) h = nearrow_compose f (nearrow_compose g h).
Proof.
intros A B C D f g h.
destruct f as [f Hnef].
destruct g as [g Hneg].
destruct h as [h Hneh].
unfold nearrow_compose; simpl.
f_equal; [].
apply proof_irrelevance.
Qed.


Lemma nearrow_compose_nonexpansive :
  forall A B C n (f f' : B -n> C) (g g' : A -n> B),
    dist_ne n f f'
    -> dist_ne n g g'
    -> dist_ne n (nearrow_compose f g) (nearrow_compose f' g').
Proof.
intros A B C n f f' g g' Hdistf Hdistg.
intro x.
simpl.
destruct f as [f Hnef].
destruct f' as [f' Hnef'].
destruct g as [g Hneg].
destruct g' as [g' Hneg'].
simpl.
apply (dist_trans C n _ (f' (g x))).
- apply Hdistf; done.

- apply Hnef'; [].
  apply Hdistg; done.
Qed.


Definition composer (A B C : ofe) (f : B -n> C) : nearrow_ofe A B -n> nearrow_ofe A C.
Proof.
exists (fun g => nearrow_compose f g).
intros n g g' Hg.
refine (nearrow_compose_nonexpansive _#8 _ Hg).
apply (@dist_refl (nearrow_ofe B C)).
Defined.


Lemma eq_nearrow_ne :
  forall (A B : ofe) (h : A = B),
    nonexpansive (fun x => transport h car x).
Proof.
intros A B h.
subst B.
apply ident_nonexpansive.
Qed.


Definition eq_nearrow {A B : ofe} (h : A = B) : A -n> B
  :=
  expair (fun x => transport h car x) (eq_nearrow_ne A B h).


Definition transport_ne {A} {a a' : A} (h : a = a') (B : A -> ofe)
  : B a -n> B a'
  :=
  @expair
    _ (@nonexpansive (B a) (B a'))
    (fun x => transport h (fun z => car (B z)) x)
    (fun i m n Hdist => transport_nonexpansive A B i a a' m n h Hdist).


Definition dep_transport_ne {A} {a a' : A} (h : a = a')
  (B : A -> Type)
  (C : forall a, B a -> ofe)
  (b : B a)
  : C a b -n> C a' (transport h B b)
  :=
  match h
    as h
    in _ = a'
    return C a b -n> C a' (transport h B b)
  with
  | eq_refl _ => idne
  end.


Definition dep_transport_ne' {A} {a a' : A} (h : a = a')
  (B : A -> Type)
  (C : forall a, B a -> ofe)
  (b : B a)
  : C a' (transport h B b) -n> C a b
  :=
  match h
    as h
    in _ = a'
    return C a' (transport h B b) -n> C a b
  with
  | eq_refl _ => idne
  end.


(* We could reuse nearrow_compose, but it seems cleaner to do it directly. *)
Definition nearrow_compose2 {A B C D : ofe} (f : A -n> B) (h : C -n> D)
  (g : B -n> C) : A -n> D.
Proof.
refine (expair (fun x => pi1 h (pi1 g (pi1 f x))) _).
intros n x y Hxy.
apply (pi2 h).
apply (pi2 g).
apply (pi2 f); auto.
Defined.


Lemma nearrow_compose2_nonexpansive :
  forall A B C D (f : A -n> B) (h : C -n> D),
    @nonexpansive (nearrow_ofe B C) (nearrow_ofe A D) (nearrow_compose2 f h).
Proof.
intros A B C D f h.
intros n g g' Hg.
cbn.
intros x.
cbn.
apply (pi2 h).
apply Hg.
Qed.


Definition nearrow_compose2_ne {A B C D : ofe} (f : A -n> B) (h : C -n> D) 
  : nearrow_ofe B C -n> nearrow_ofe A D
  :=
  expair (nearrow_compose2 f h) (nearrow_compose2_nonexpansive _#4 f h).


Lemma nearrow_compose2_compose :
  forall (A B C D E F : ofe) 
    (f1 : A -n> B) (f2 : B -n> C) (g : C -n> D) (h2 : D -n> E) (h1 : E -n> F),
      nearrow_compose2 f1 h1 (nearrow_compose2 f2 h2 g)
      =
      nearrow_compose2 (nearrow_compose f2 f1) (nearrow_compose h1 h2) g.
Proof.
intros A B C D E F f1 f2 g h2 h1.
apply nearrow_extensionality.
intro x.
cbn.
reflexivity.
Qed.


Lemma nearrow_compose2_split :
  forall A B C D (f : C -n> D) (g : B -n> C) (h : A -n> B),
    nearrow_compose2 h f g
    =
    nearrow_compose f (nearrow_compose g h).
Proof.
intros A B C D f g h.
apply nearrow_extensionality.
intro x.
cbn.
reflexivity.
Qed.


(* Product spaces *)

Definition dist_prod {A B : ofe} n (p q : car A * car B) :=
  dist n (fst p) (fst q) /\ dist n (snd p) (snd q).


Definition prod_ofe (A B : ofe) : ofe.
Proof.
apply (mk_ofe (car A * car B) (@dist_prod A B)).

(* eqrel *)
{
intro n.
do2 2 split.
+ intros (x, y).
  split; apply dist_refl.

+ intros (x1, y1) (x2, y2) (x3, y3) H12 H23.
  destruct H12 as (H12x, H12y).
  destruct H23 as (H23x, H23y).
  split; eapply dist_trans; eauto.

+ intros (x1, y1) (x2, y2) H.
  destruct H as (Hx, Hy).
  split; eapply dist_symm; eauto.
}

(* limeq *)
{
intros (x, y) (x', y') Hsim.
f_equal.
+ apply dist_limeq; [].
  intro n.
  destruct (Hsim n); auto.

+ apply dist_limeq; [].
  intro n.
  destruct (Hsim n); auto.
}

(* downward *)
{
intros n (x, y) (x', y') Hdist.
destruct Hdist.
split; apply dist_downward; eauto.
}

(* zero *)
{
intros (x, y) (x', y').
split; apply dist_zero.
}
Defined.


Definition pair_ne {A B C : ofe} (f : A -n> B) (g : A -n> C)
  : A -n> prod_ofe B C.
Proof.
exists (fun x => (pi1 f x, pi1 g x)).
exact (fun n x y H => conj (pi2 f n x y H) (pi2 g n x y H)).
Defined.


Definition fst_ne {A B : ofe} : prod_ofe A B -n> A.
Proof.
exists fst.
intros n x y Hxy.
exact (Hxy andel).
Defined.


Definition snd_ne {A B : ofe} : prod_ofe A B -n> B.
Proof.
exists snd.
intros n x y Hxy.
exact (Hxy ander).
Defined.


Definition mpair_ne {A B C D : ofe} (f : A -n> C) (g : B -n> D)
  : prod_ofe A B -n> prod_ofe C D.
Proof.
exists (fun x => (pi1 f (fst x), pi1 g (snd x))).
exact (fun n x y H => conj (pi2 f n _ _ (carp H)) (pi2 g n _ _ (cdrp H))).
Defined.


Lemma dist_prod_fst :
  forall A B n (p q : car (prod_ofe A B)),
    dist n p q
    -> dist n (fst p) (fst q).
Proof.
intros A B n p q Hdist.
destruct Hdist.
auto.
Qed.


Lemma dist_prod_snd :
  forall A B n (p q : car (prod_ofe A B)),
    dist n p q
    -> dist n (snd p) (snd q).
Proof.
intros A B n p q Hdist.
destruct Hdist.
auto.
Qed.


Definition limit_prod (A B : ofe) (C : complete A) (D : complete B) :
  forall ch, convergent (@dist_prod A B) ch -> car A * car B.
Proof.
intros ch Hconv.
split.
  {
  refine (limit C (fun i => fst (ch i)) _); [].
  eapply map_convergent_prim; eauto; [].
  intros n p q Hdist.
  destruct Hdist; auto.
  }
  
  {
  refine (limit D (fun i => snd (ch i)) _); [].
  eapply map_convergent_prim; eauto; [].
  intros n p q Hdist.
  destruct Hdist; auto.
  }
Defined.


Definition prod_complete (A B : ofe) (C : complete A) (D : complete B) : complete (prod_ofe A B).
Proof.
apply (mk_complete (prod_ofe A B) (limit_prod A B C D) (inhabitant C, inhabitant D)).
intros ch n Hconv.
so (Hconv n) as (H1 & H2).
split.
+ apply complete_dist.

+ apply complete_dist.
Defined.


Definition unit_ofe : ofe.
Proof.
apply
  (mk_ofe
     unit
     (fun _ _ _ => True)).

- do2 2 split; intro; auto.

- intros x y _.
  destruct x; destruct y.
  reflexivity.

- auto.

- auto.
Defined.


Definition unit_complete : complete unit_ofe.
Proof.
apply
  (mk_complete unit_ofe
     (fun _ _ => tt)
     tt).
intros ch n _.
set (x := ch n).
destruct x.
apply dist_refl.
Defined.
