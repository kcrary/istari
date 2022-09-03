
Require Import Tactics.
Require Import Relation.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.
Require Export Reduction.
Require Import Standardization.


Section object.


Arguments operator {object}.
Arguments term {object}.
Arguments row {object}.
Arguments rw_cons {object i a}.


Variable object : Type.


Definition equiv : @term object -> @term object -> Prop :=
  star (fun m n => reduce m n \/ reduce n m).


Lemma equiv_refl : forall m, equiv m m.
Proof.
intro m.
apply star_refl.
Qed.


Lemma equiv_symm :
  forall m n,
    equiv m n
    -> equiv n m.
Proof.
intros m n H.
induct H.

(* refl *)
{
intro m.
apply star_refl.
}

(* step *)
{
intros m p n Hmp _ IH.
eapply star_trans; eauto.
apply star_one.
destruct Hmp; auto.
}
Qed.


Lemma equiv_trans :
  forall m1 m2 m3,
    equiv m1 m2
    -> equiv m2 m3
    -> equiv m1 m3.
Proof.
intros m1 m2 m3 H12 H23.
eapply star_trans; eauto.
Qed.


Lemma reduce_equiv :
  forall (m m' : @term object),
    reduce m m'
    -> equiv m m'.
Proof.
intros m m' H.
apply star_one.
left; auto.
Qed.


Lemma reduces_equiv :
  forall (m m' : @term object),
    star reduce m m'
    -> equiv m m'.
Proof.
intros m m' H.
eapply star_mono; eauto.
Qed.


Hint Resolve equiv_refl equiv_symm equiv_trans : equiv.


Lemma equiv_refl' :
  forall m m',
    m = m'
    -> equiv m m'.
Proof.
intros m m' H.
subst m'.
apply equiv_refl.
Qed.


Lemma steps_equiv :
  forall (m m' : @term object),
    star step m m'
    -> equiv m m'.
Proof.
intros m m' H.
apply (star_mono _ step); eauto.
intros.
left.
apply step_reduce; auto.
Qed.


Hint Resolve steps_equiv : equiv.


Lemma church_rosser :
  forall m n,
    equiv m n
    -> exists p,
         star reduce m p
         /\ star reduce n p.
Proof.
intros m n H.
induct H.

(* refl *)
{
intros m.
exists m.
split; apply star_refl.
}

(* step *)
{
intros m n p Hmn _ IH.
assert (exists q, star reduce m q /\ star reduce n q) as (q & Hmq & Hnq).
  {
  destruct Hmn; [exists n | exists m]; split; apply star_one; auto using reduce_id.
  }
destruct IH as (r & Hnr & Hpr).
so (confluence _#4 Hnr Hnq) as (s & Hrs & Hqs).
exists s.
split; eapply star_trans; eauto.
}
Qed.


Lemma equiv_compat :
  forall m n,
    mc equiv m n
    -> equiv m n.
Proof.
intros m n H.
cases H; eauto using equiv_refl.
intros a th r s Hr.
cut (exists t, star reducer r t /\ star reducer s t).
  {
  intros (t & Hrt & Hst).
  apply (star_trans _#3 (oper a th t)).
    {
    apply (star_map _ _ reducer _ (oper a th)); auto.
    intros x y Hxy.
    left.
    apply reduce_oper; eauto.
    }
  apply (star_reverse _ (fun x y => reduce y x \/ reduce x y)).
    {
    intros x y H.
    destruct H; auto.
    }
  apply (star_map _ _ reducer _ (oper a th)); auto.
  intros x y H.
  right.
  apply reduce_oper; auto.
  }
clear th.
induct Hr.

(* nil *)
{
exists rw_nil.
split; apply star_refl.
}

(* cons *)
{
intros i a m n r s Hmn _ IH.
so (church_rosser _ _ Hmn) as (p & Hmp & Hnp).
destruct IH as (t & Hrt & Hst).
exists (rw_cons p t).
split.
  {
  eapply star_trans.
    {
    apply (star_map _ _ reduce _ (fun z => rw_cons z r)); eauto.
    intros x y Hxy.
    apply reducer_cons; auto.
    apply reducer_id.
    }

    {
    apply (star_map _ _ reducer _ (rw_cons p)); auto.
    intros x y Hxy.
    apply reducer_cons; auto.
    apply reduce_id.
    }
  }

  {
  eapply star_trans.
    {
    apply (star_map _ _ reduce _ (fun z => rw_cons z s)); eauto.
    intros x y Hxy.
    apply reducer_cons; auto.
    apply reducer_id.
    }

    {
    apply (star_map _ _ reducer _ (rw_cons p)); auto.
    intros x y Hxy.
    apply reducer_cons; auto.
    apply reduce_id.
    }
  }
}
Qed.


Lemma equiv_subst :
  forall s m m',
    equiv m m'
    -> equiv (subst s m) (subst s m').
Proof.
intros s m m' H.
eapply (star_map _#4 (fun z => subst s z)); eauto.
intros x y Hxy.
destruct Hxy; [left | right]; auto using reduce_subst.
Qed.


Lemma equiv_subst1 :
  forall n m m',
    equiv m m'
    -> equiv (subst1 n m) (subst1 n m').
Proof.
intros n m m' H.
apply equiv_subst; auto.
Qed.


Definition equivsub s s' : Prop :=
  forall i, equiv (project s i) (project s' i).


Lemma equivsub_refl :
  forall s, equivsub s s.
Proof.
intros s i.
apply equiv_refl.
Qed.


Lemma equivsub_symm :
  forall (s s' : @sub object), equivsub s s' -> equivsub s' s.
Proof.
intros s s' H i.
apply equiv_symm; auto.
Qed.


Lemma equivsub_trans :
  forall (s1 s2 s3 : @sub object), equivsub s1 s2 -> equivsub s2 s3 -> equivsub s1 s3.
Proof.
intros s1 s2 s3 H12 H23 i.
eapply equiv_trans; auto.
Qed.


Lemma equivsub_dot :
  forall m m' s s',
    equiv m m'
    -> equivsub s s'
    -> equivsub (dot m s) (dot m' s').
Proof.
intros m m' s s' Hm Hs.
intro i.
destruct i as [| i].
  {
  simpsub; auto.
  }

  {
  simpsub.
  apply Hs.
  }
Qed.


Lemma equivsub_compose_simple :
  forall s1 s1' s2,
    equivsub s1 s1'
    -> equivsub (compose s1 s2) (compose s1' s2).
Proof.
intros s1 s1' s2 Hs.
intros i.
simpsub.
apply equiv_subst.
apply Hs.
Qed.


Lemma equivsub_under :
  forall s s' i,
    equivsub s s'
    -> equivsub (under i s) (under i s').
Proof.
intros s s' i.
revert s s'.
induct i.

(* 0 *)
{
intros s s' Hs.
exact Hs.
}

(* S *)
{
intros i IH s s' Hs.
rewrite -> !under_succ.
apply equivsub_dot; auto using equiv_refl.
apply equivsub_compose_simple; auto.
}
Qed.


(* Could replace the proof of equiv_funct1 with this. *)
Lemma equiv_funct :
  forall s s' m m',
    equivsub s s'
    -> equiv m m'
    -> equiv (subst s m) (subst s' m').
Proof.
intros s s' m m' Hs Hm.
cut (equiv (subst s m) (subst s' m)).
  {
  intro H.
  eapply equiv_trans; eauto.
  apply equiv_subst; auto.
  }
clear m' Hm.
revert s s' Hs.
induct m using
  (fun Z => term_mut_ind object Z
     (fun a r => forall s s', equivsub s s' -> mcr equiv _ (substr s r) (substr s' r))).

(* var *)
{
intros n s s' Hs.
simpsub.
apply Hs.
}

(* oper *)
{
intros a th r IH s s' Hs.
simpsub.
apply equiv_compat.
apply mc_oper; auto.
}

(* nil *)
{
intros s s' H.
apply mcr_nil.
}

(* cons *)
{
intros i a m IH1 r IH2 s s' Hs.
simpsub.
apply mcr_cons; auto.
apply IH1.
apply equivsub_under; auto.
}
Qed.


Lemma equivsub_compose :
  forall s1 s1' s2 s2',
    equivsub s1 s1'
    -> equivsub s2 s2'
    -> equivsub (compose s1 s2) (compose s1' s2').
Proof.
intros s1 s1' s2 s2' Hs1 Hs2.
intros i.
simpsub.
apply equiv_funct; auto.
Qed.


Lemma equiv_funct1_under :
  forall i n n' m m',
    equiv n n'
    -> equiv m m'
    -> equiv (subst (under i (dot n id)) m) (subst (under i (dot n' id)) m').
Proof.
intros i n n' m m' Hn Hm.
apply (star_trans _#3 (subst (under i (dot n id)) m')).
  {
  apply equiv_subst; auto.
  }
eapply (star_map _#4 (fun z => subst (under i (dot z id)) m')); eauto.
intros x y H.
destruct H as [H|H].
  {
  left.
  apply reduce_funct1_under; auto using reduce_id.
  }

  {
  right.
  apply reduce_funct1_under; auto using reduce_id.
  }
Qed.


Lemma equiv_funct1 :
  forall n n' m m',
    equiv n n'
    -> equiv m m'
    -> equiv (subst1 n m) (subst1 n' m').
Proof.
intros n n' m m' Heqn Heqm.
unfold subst1.
rewrite <- (under_zero _ (dot n id)).
rewrite <- (under_zero _ (dot n' id)).
apply equiv_funct1_under; auto.
Qed.


Lemma common_mc_reduce_impl_mc_equiv :
  forall m n p,
    star (mc reduce) m p
    -> star (mc reduce) n p
    -> mc equiv m n.
Proof.
intros m n p Hmp Hnp.
assert (reflexive _ (mc equiv)) as Hrefl.
  {
  apply mc_refl.
  intro.
  apply equiv_refl.
  }
assert (transitive _ (mc equiv)) as Htrans.
  {
  apply mc_trans.
  intro.
  apply equiv_trans.
  }
apply (Htrans _ p).
  {
  assert (forall x y, mc reduce x y -> mc equiv x y) as Hmono.
    {
    apply mc_mono.
    intros x y H.
    apply star_one.
    left; auto.
    }
  induct Hmp; eauto.
  }

  {
  assert (forall x y, mc reduce y x -> mc equiv x y) as Hmono.
    {
    intros x y Hxy.
    eapply mc_reverse; eauto.
    clear x y Hxy.
    intros x y H.
    apply star_one.
    right; auto.
    }
  so (star_starr _#4 Hnp) as H.
  clear Hnp.
  induct H; eauto.
  }
Qed.


Lemma equiv_eval :
  forall m m' n,
    equiv m m'
    -> eval m n
    -> exists n',
         eval m' n'
         /\ mc equiv n n'.
Proof.
intros m n p Hmn Hmp.
destruct Hmp as (Hmp & Hval).
assert (equiv p n) as Hpn.
  {
  apply (equiv_trans _ m); auto.
  apply equiv_symm.
  apply steps_equiv; auto.
  }
so (church_rosser _ _ Hpn) as (q & Hpq & Hnq).
so (standardization _#3 Hpq) as (r & Hpr & Hrq).
assert (p = r).
  {
  invert Hpr; auto.
  intros s Hps _.
  destruct (determinism_value _#3 Hval Hps).
  }
subst r.
so (standardization _#3 Hnq) as (s & Hns & Hsq).
exists s.
assert (mc equiv p s) as Hps.
  {
  eapply common_mc_reduce_impl_mc_equiv; eauto.
  }
split; auto.
split; auto.
eapply mc_value; eauto.
Qed.


Lemma equiv_normal :
  forall n n',
    normal n
    -> normal n'
    -> equiv n n'
    -> mc equiv n n'.
Proof.
intros m n Hm Hn Hmn.
so (church_rosser _ _ Hmn) as (p & Hmp & Hnp).
so (standardization _#3 Hmp) as (q & Hmq & Hqp).
so (standardization _#3 Hnp) as (r & Hnr & Hrp).
invert Hmq.
2:{
  intros s Hms _.
  destruct (Hm _ Hms).
  }
intros <-.
invert Hnr.
2:{
  intros s Hns _.
  destruct (Hn _ Hns).
  }
intros <-.
eapply common_mc_reduce_impl_mc_equiv; eauto.
Qed.


Lemma equiv_value :
  forall v v',
    value v
    -> value v'
    -> equiv v v'
    -> mc equiv v v'.
Proof.
intros v v' Hval Hval' Hequiv.
eauto using equiv_normal, value_normal.
Qed.


Lemma lam_equiv_inj :
  forall (m n : @term object),
    equiv (lam m) (lam n)
    -> equiv m n.
Proof.
intros m n Hequiv.
so (church_rosser _ _ Hequiv) as (p & Hleft & Hright).
so (reduces_canon_form _#5 (canon_lam _) Hleft) as (r & -> & Hleft').
so (reduces_canon_form _#5 (canon_lam _) Hright) as (s & Heq & Hright').
clear Hleft Hright.
so (row_invert_auto _ _ r) as H; cbn in H.
destruct H as (p & ->).
so (row_invert_auto _ _ s) as H; cbn in H.
destruct H as (q & ->).
injection Heq.
intros <-.
so (star_mcr _#5 (star_mono _#3 (reducer_mcr _ _) _ _ Hleft')) as H.
invertc H.
intros Hmp _.
so (star_mcr _#5 (star_mono _#3 (reducer_mcr _ _) _ _ Hright')) as H.
invertc H.
intros Hnp _.
eapply equiv_trans; eauto using reduces_equiv, equiv_symm.
Qed.


Lemma app_equiv_inj :
  forall (m n p q : @term object),
    rigid m
    -> rigid n
    -> equiv (app m p) (app n q)
    -> equiv m n /\ equiv p q.
Proof.
intros m n p q Hrigidm Hrigidn Hequiv.
so (church_rosser _ _ Hequiv) as (t & Hleft & Hright).
so (reduces_app_form _#4 Hrigidm Hleft) as (m' & p' & -> & Hm & Hp).
so (reduces_app_form _#4 Hrigidn Hright) as (m'' & p'' & Heq & Hm' & Hp').
injectionc Heq.
intros <- <-.
split; eauto using reduces_equiv, equiv_trans, equiv_symm.
Qed.


End object.


Arguments equiv {object}.
Arguments equivsub {object}.


Inductive equivh {object} : @hyp object -> hyp -> Prop :=
| equivh_tpl :
    equivh hyp_tpl hyp_tpl

| equivh_tp :
    equivh hyp_tp hyp_tp

| equivh_tml :
    forall a a',
      equiv a a'
      -> equivh (hyp_tml a) (hyp_tml a')

| equivh_tm :
    forall a a',
      equiv a a'
      -> equivh (hyp_tm a) (hyp_tm a')

| equivh_emp :
    equivh hyp_emp hyp_emp
.


Lemma equivh_refl :
  forall object (h : @hyp object), equivh h h.
Proof.
intros object h.
cases h; intros; [apply equivh_tpl | apply equivh_tp | apply equivh_tml | apply equivh_tm | apply equivh_emp]; auto using equiv_refl.
Qed.


Lemma equivh_symm :
  forall object (h h' : @hyp object), equivh h h' -> equivh h' h.
Proof.
intros object h h' H.
cases H; intros; [apply equivh_tpl | apply equivh_tp | apply equivh_tml | apply equivh_tm | apply equivh_emp]; auto using equiv_symm.
Qed.


Lemma equivh_trans :
  forall object (h1 h2 h3 : @hyp object), equivh h1 h2 -> equivh h2 h3 -> equivh h1 h3.
Proof.
intros object h1 h2 h3 H12 H23.
revert h3 H23.
cases H12; auto.
  {
  intros a1 a2 H12 h3 H23.
  invertc H23.
  intros a3 H23 <-.
  apply equivh_tml; eauto using equiv_trans.
  }

  {
  intros a1 a2 H12 h3 H23.
  invertc H23.
  intros a3 H23 <-.
  apply equivh_tm; eauto using equiv_trans.
  }
Qed.


Lemma equivh_subst :
  forall object s (h h' : @hyp object),
    equivh h h'
    -> equivh (substh s h) (substh s h').
Proof.
intros object s h h' H.
cases H; intros; simpsub;
[apply equivh_tpl | apply equivh_tp | apply equivh_tml | apply equivh_tm | apply equivh_emp];
auto using equiv_funct, equiv_refl, equiv_subst.
Qed.
