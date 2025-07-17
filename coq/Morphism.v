
Require Import Coq.Setoids.Setoid.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.List.

Require Import Tactics.
Require Import Relation.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Equivalence.
Require Import Equivalences.
Require Import Rules.
Require Import Defined.


Definition equivr {object a} (r r' : @row object a) : Prop :=
  mcr equiv a r r'.

Definition equivctx {object} (G G' : @context object) : Prop :=
  Forall2 equivh G G'.

Inductive equivj {object} : @judgement object -> @judgement object -> Prop :=
| equivj_i :
    forall m m' n n' a a',
      equiv m m'
      -> equiv n n'
      -> equiv a a'
      -> equivj (deq m n a) (deq m' n' a').


Lemma equivr_refl :
  forall object a (r : @row object a),
    equivr r r.
Proof.
unfold equivr.
intros object a r.
induct r; auto using mcr_nil.
intros i a t r H.
apply mcr_cons; auto using equiv_refl.
Qed.


Lemma equivr_symm :
  forall object a (r r' : @row object a),
    equivr r r'
    -> equivr r' r.
Proof.
unfold equivr.
intros object a r r' Heq.
induct Heq; eauto using mcr_nil.
intros i a m m' r r' Heqm _ IH.
apply mcr_cons; auto using equiv_symm.
Qed.


Lemma equivr_trans :
  forall object a (r1 r2 r3 : @row object a),
    equivr r1 r2
    -> equivr r2 r3
    -> equivr r1 r3.
Proof.
unfold equivr.
intros object a r1 r2 r3 H12 H23.
revert r3 H23.
induct H12.

(* nil *)
{
intros r3 H23.
invertc H23.
intros <-.
apply mcr_nil.
}

(* cons *)
{
intros i a m1 m2 r1 r2 Heqm _ IH rr H23.
invertc H23.
intros m3 r3 Hm23 H23 <-.
apply mcr_cons; eauto using equiv_trans.
}  
Qed.


Lemma equiv_oper :
  forall object a (t : operator object a) (r r' : row object a),
    equivr r r'
    -> equiv (oper a t r) (oper a t r').
Proof.
intros object a t r r' Heqr.
apply equiv_compat.
apply mc_oper.
clear t.
induct Heqr; auto using mcr_nil.
(* cons *)
intros i a m m' r r' Heqm _ IH.
apply mcr_cons; auto.
Qed.


Lemma equivh_funct :
  forall object s s' (h h' : @hyp object),
    equivsub s s'
    -> equivh h h'
    -> equivh (substh s h) (substh s' h').
Proof.
intros object s s' h h' Hs Hh.
induct Hh; intros; simpsub; eauto using equivh_tpl, equivh_tp, equivh_emp, equivh_tm, equivh_tml, equiv_funct.
Qed.


Lemma equivctx_refl :
  forall object (G : @context object),
    equivctx G G.
Proof.
intros object G.
unfold equivctx.
induct G; eauto using Forall2, equivh_refl.
Qed.


Lemma equivctx_symm :
  forall object (G G' : @context object),
    equivctx G G'
    -> equivctx G' G.
Proof.
unfold equivctx.
intros object G G' H.
induct H; eauto using Forall2, equivh_symm.
Qed.


Lemma equivctx_trans :
  forall object (G1 G2 G3 : @context object),
    equivctx G1 G2
    -> equivctx G2 G3
    -> equivctx G1 G3.
Proof.
unfold equivctx.
intros object G1 G2 G3 H12 H23.
revert G3 H23.
induct H12.

(* nil *)
{
intros G3 H23.
invertc H23.
intros <-.
apply Forall2_nil.
}

(* cons *)
{
intros h1 h2 G1 G2 H12 _ IH GG H23.
invertc H23.
intros h3 G3 Hh23 H23 <-.
apply Forall2_cons; eauto using equivh_trans.
}
Qed.


Lemma equivctx_length :
  forall object (G G' : @context object),
    equivctx G G'
    -> length G = length G'.
Proof.
intros object G G' Hequiv.
induct Hequiv; intros; cbn; auto.
Qed.


Lemma equivctx_funct :
  forall object s s' (G G' : @context object),
    equivsub s s'
    -> equivctx G G'
    -> equivctx (substctx s G) (substctx s' G').
Proof.
intros object s s' G G' Hs HG.
induct HG.

(* nil *)
{
simpsub.
apply equivctx_refl.
}

(* cons *)
{
intros h h' G G' Hh _ IH.
simpsub.
apply Forall2_cons; auto.
apply equivh_funct; auto.
replace (length G') with (length G).
2:{
  so (equivctx_length _#3 IH) as H.
  rewrite -> !length_substctx in H.
  auto.
  }
apply equivsub_under; auto.
}
Qed.


Lemma equivj_refl :
  forall object (J : @judgement object),
    equivj J J.
Proof.
intros object J.
destruct J as [m n a].
apply equivj_i; auto using equiv_refl.
Qed.


Lemma equivj_symm :
  forall object (J J' : @judgement object),
    equivj J J'
    -> equivj J' J.
Proof.
intros object J J' Heq.
invertc Heq.
intros m m' n n' a a' Heqm Heqn Heqa <- <-.
apply equivj_i; auto using equiv_symm.
Qed.


Lemma equivj_trans :
  forall object (J1 J2 J3 : @judgement object),
    equivj J1 J2
    -> equivj J2 J3
    -> equivj J1 J3.
Proof.
intros object J1 J2 J3 H12 H23.
invertc H12.
intros m1 m2 n1 n2 a1 a2 Hm12 Hn12 Ha12 <- <-.
invertc H23.
intros m3 n3 a3 Hm23 Hn23 Ha23 <-.
apply equivj_i; eauto using equiv_trans.
Qed.


Lemma equiv_deq :
  forall object (m1 m1' m2 m2' a a' : @term object),
    equiv m1 m1'
    -> equiv m2 m2'
    -> equiv a a'
    -> equivj (deq m1 m2 a) (deq m1' m2' a').
Proof.
intro.
exact equivj_i.
Qed.


Lemma equiv_tr :
  forall (G G' : @context obj) (J J' : @judgement obj),
    equivctx G G'
    -> equivj J J'
    -> tr G J <-> tr G' J'.
Proof.
intros G G' J J' HeqG HeqJ.
transitivity (tr G J').
  {
  destruct J as [m n a].
  destruct J' as [m' n' a'].
  invertc HeqJ.
  intros Heqm Heqn Heqa.
  split.
    {
    intro Htr.
    refine (tr_compute _#7 _ _ _ Htr); eauto using equiv_symm.
    }

    {
    intro Htr.
    refine (tr_compute _#7 _ _ _ Htr); auto.
    }
  }
clear J HeqJ.
rename J' into J.
cut (forall G2, tr (G2 ++ G) J <-> tr (G2 ++ G') J).
  {
  intro Hcond.
  apply (Hcond nil).
  }
unfold equivctx in HeqG.
induct HeqG.

(* nil *)
{
intros G2.
rewrite -> app_nil_r.
reflexivity.
}

(* cons *)
{
intros h h' G G' Heqh _ IH G2.
transitivity (tr (G2 ++ h :: G') J).
  {
  change (tr (G2 ++ (h :: nil) ++ G) J <-> tr (G2 ++ (h :: nil) ++ G') J).
  rewrite -> !app_assoc.
  apply IH.
  }
split; intro Htr.
  {
  refine (tr_compute_hyp _#5 _ Htr); auto.
  apply equivh_symm; auto.
  }

  {
  refine (tr_compute_hyp _#5 _ Htr); auto.
  }
}
Qed.


Add Parametric Relation object : (@term object) (@equiv object)
  reflexivity proved by (equiv_refl object)
  symmetry proved by (equiv_symm object)
  transitivity proved by (equiv_trans object)
  as equiv_rel.

Add Parametric Relation object a : (@row object a) (@equivr object a)
  reflexivity proved by (equivr_refl object a)
  symmetry proved by (equivr_symm object a)
  transitivity proved by (equivr_trans object a)
  as equivr_rel.

Add Parametric Relation object : (@hyp object) (@equivh object)
  reflexivity proved by (equivh_refl object)
  symmetry proved by (equivh_symm object)
  transitivity proved by (equivh_trans object)
  as equivh_rel.

Add Parametric Relation object : (@context object) (@equivctx object)
  reflexivity proved by (equivctx_refl object)
  symmetry proved by (equivctx_symm object)
  transitivity proved by (equivctx_trans object)
  as equivctx_rel.

Add Parametric Relation object : (@judgement object) (@equivj object)
  reflexivity proved by (equivj_refl object)
  symmetry proved by (equivj_symm object)
  transitivity proved by (equivj_trans object)
  as equivj_rel.

Add Parametric Relation object : (@sub object) (@equivsub object)
  reflexivity proved by (equivsub_refl object)
  symmetry proved by (equivsub_symm object)
  transitivity proved by (equivsub_trans object)
  as equivsub_rel.


Add Parametric Morphism object a : (@oper object a)
  with signature eq ==> (@equivr object a) ==> (@equiv object)
  as oper_mor.
Proof.
intros t r r' Hr.
apply equiv_oper; auto.
Qed.


Add Parametric Morphism object i a : (@rw_cons object i a)
  with signature (@equiv object) ==> (@equivr object a) ==> (@equivr object (cons i a))
  as rw_cons_mor.
Proof.
intros m m' Hm r r' Hr.
unfold equivr.
apply mcr_cons; auto.
Qed.


Add Parametric Morphism object : (@deq object)
  with signature (@equiv object) ==> (@equiv object) ==> (@equiv object) ==> (@equivj object)
  as deq_mor.
Proof.
intros m1 m1' H1 m2 m2' H2 a a' Ha.
apply equiv_deq; auto.
Qed.


Add Parametric Morphism object : (@hyp_tm object)
  with signature Equivalence.equiv ==> equivh
  as tm_mor.
Proof.
intros h h' Hequiv.
apply equivh_tm; auto.
Qed.


Add Parametric Morphism object : (@hyp_tml object)
  with signature Equivalence.equiv ==> equivh
  as tml_mor.
Proof.
intros h h' Hequiv.
apply equivh_tml; auto.
Qed.


Add Parametric Morphism object : (@cons (@hyp object))
  with signature equivh ==> equivctx ==> equivctx
  as cons_mor.
Proof.
intros h h' Hh G G' HG.
apply Forall2_cons; auto.
Qed.


Add Morphism tr
  with signature equivctx ==> equivj ==> iff
  as tr_mor.
Proof.
intros G G' HG J J' HJ.
apply equiv_tr; auto.
Qed.



Add Parametric Morphism object : (@admiss object)
  with signature equiv ==> equiv
  as equiv_admiss.
Proof.
intros m1 m1' H1.
unfold admiss.
rewrite H1.
reflexivity.
Qed.


Add Parametric Morphism object : (@app object)
  with signature equiv ==> equiv ==> equiv
  as equiv_app.
Proof.
intros m1 m1' H1 m2 m2' H2.
unfold app.
rewrite H1, H2.
reflexivity.
Qed.


Add Parametric Morphism object : (@bite object)
  with signature equiv ==> equiv ==> equiv ==> equiv
  as equiv_bite.
Proof.
intros m1 m1' H1 m2 m2' H2 m3 m3' H3.
unfold bite.
rewrite H1, H2, H3.
reflexivity.
Qed.


Add Parametric Morphism object : (@equal object)
  with signature equiv ==> equiv ==> equiv ==> equiv
  as equiv_equal.
Proof.
intros m1 m1' H1 m2 m2' H2 m3 m3' H3.
unfold equal.
rewrite H1, H2, H3.
reflexivity.
Qed.


Add Parametric Morphism object : (@eqtype object)
  with signature equiv ==> equiv ==> equiv
  as equiv_eqtype.
Proof.
intros m1 m1' H1 m2 m2' H2.
unfold eqtype.
rewrite H1, H2.
reflexivity.
Qed.


Add Parametric Morphism object : (@fut object)
  with signature equiv ==> equiv
  as equiv_fut.
Proof.
intros m1 m1' H1.
apply equiv_fut; auto.
Qed.


Add Parametric Morphism object : (@sequal object)
  with signature equiv ==> equiv ==> equiv
  as equiv_sequal.
Proof.
intros m1 m1' H1 m2 m2' H2.
unfold sequal.
rewrite H1, H2.
reflexivity.
Qed.


Lemma equiv_deqtype :
  forall object (a a' b b' : @term object),
    equiv a a'
    -> equiv b b'
    -> equivj (deqtype a b) (deqtype a' b').
Proof.
intros.
unfold deqtype.
apply equiv_deq; auto using equiv_refl.
apply equiv_eqtype; auto.
Qed.


Add Parametric Morphism object : (@deqtype object)
  with signature (@equiv object) ==> (@equiv object) ==> (@equivj object)
  as deqtype_mor.
Proof.
intros a a' Ha b b' Hb.
apply equiv_deqtype; auto.
Qed.


Add Parametric Morphism object : (@halts object)
  with signature equiv ==> equiv
  as equiv_halts.
Proof.
intros m1 m1' H1.
unfold halts.
rewrite H1.
reflexivity.
Qed.


Add Parametric Morphism object : (@intersect object)
  with signature equiv ==> equiv ==> equiv
  as equiv_intersect.
Proof.
intros m1 m1' H1 m2 m2' H2.
unfold intersect.
rewrite H1, H2.
reflexivity.
Qed.


Add Parametric Morphism object : (@padmiss object)
  with signature equiv ==> equiv ==> equiv
  as equiv_padmiss.
Proof.
intros m1 m1' H1 m2 m2' H2.
unfold padmiss.
rewrite H1, H2.
reflexivity.
Qed.


Add Parametric Morphism object : (@partial object)
  with signature equiv ==> equiv
  as equiv_partial.
Proof.
intros m1 m1' H1.
apply equiv_partial; auto.
Qed.


Add Parametric Morphism object : (@pi object)
  with signature equiv ==> equiv ==> equiv
  as equiv_pi.
Proof.
intros m1 m1' H1 m2 m2' H2.
unfold pi.
rewrite H1, H2.
reflexivity.
Qed.


Add Parametric Morphism object : (@ppair object)
  with signature equiv ==> equiv ==> equiv
  as equiv_pair.
Proof.
intros m1 m1' H1 m2 m2' H2.
apply equiv_ppair; auto.
Qed.


Add Parametric Morphism object : (@prod object)
  with signature equiv ==> equiv ==> equiv
  as equiv_prod.
Proof.
intros m1 m1' H1 m2 m2' H2.
unfold prod.
rewrite H1, H2.
reflexivity.
Qed.


Add Parametric Morphism object : (@seq object)
  with signature equiv ==> equiv ==> equiv
  as equiv_seq.
Proof.
intros m1 m1' H1 m2 m2' H2.
unfold seq.
rewrite H1, H2.
reflexivity.
Qed.


Add Parametric Morphism object : (@set object)
  with signature equiv ==> equiv ==> equiv
  as equiv_set.
Proof.
intros m1 m1' H1 m2 m2' H2.
unfold set.
rewrite H1, H2.
reflexivity.
Qed.


Add Parametric Morphism object : (@sigma object)
  with signature equiv ==> equiv ==> equiv
  as equiv_sigma.
Proof.
intros m1 m1' H1 m2 m2' H2.
unfold sigma.
rewrite H1, H2.
reflexivity.
Qed.


Add Parametric Morphism object : (@subtype object)
  with signature equiv ==> equiv ==> equiv
  as equiv_subtype.
Proof.
intros m1 m1' H1 m2 m2' H2.
unfold subtype.
rewrite H1, H2.
reflexivity.
Qed.


Lemma equiv_dsubtype :
  forall object (a a' b b' : @term object),
    equiv a a'
    -> equiv b b'
    -> equivj (dsubtype a b) (dsubtype a' b').
Proof.
intros.
unfold dsubtype.
apply equiv_deq; auto using equiv_refl.
apply equiv_subtype; auto.
Qed.


Add Parametric Morphism object : (@dsubtype object)
  with signature (@equiv object) ==> (@equiv object) ==> (@equivj object)
  as dsubtype_mor.
Proof.
intros a a' Ha b b' Hb.
apply equiv_dsubtype; auto.
Qed.


Add Parametric Morphism object : (@sumcase object)
  with signature equiv ==> equiv ==> equiv ==> equiv
  as equiv_sumcase.
Proof.
intros m1 m1' H1 m2 m2' H2 m3 m3' H3.
unfold sumcase.
apply equiv_bite.
  {
  apply equiv_ppi1.
  rewrite H1.
  reflexivity.
  }

  {
  apply equiv_funct1; auto.
  apply equiv_ppi2; auto.
  }

  {
  apply equiv_funct1; auto.
  apply equiv_ppi2; auto.
  }
Qed.


Add Parametric Morphism object : (@sumleft object)
  with signature equiv ==> equiv
  as equiv_sumleft.
Proof.
intros m1 m1' H1.
unfold sumleft.
rewrite H1.
reflexivity.
Qed.


Add Parametric Morphism object : (@sumright object)
  with signature equiv ==> equiv
  as equiv_sumright.
Proof.
intros m1 m1' H1.
unfold sumright.
rewrite H1.
reflexivity.
Qed.


Add Parametric Morphism object : (@tarrow object)
  with signature equiv ==> equiv ==> equiv
  as equiv_tarrow.
Proof.
intros m1 m1' H1 m2 m2' H2.
unfold tarrow.
rewrite H1, H2.
reflexivity.
Qed.


Add Parametric Morphism object : (@univ object)
  with signature equiv ==> equiv
  as equiv_univ.
Proof.
intros m1 m1' H1.
unfold univ.
rewrite H1.
reflexivity.
Qed.


Add Parametric Morphism object : (@uptype object)
  with signature equiv ==> equiv
  as equiv_uptype.
Proof.
intros m1 m1' H1.
unfold uptype.
rewrite H1.
reflexivity.
Qed.


Add Parametric Morphism object : (@dot object)
  with signature equiv ==> equivsub ==> equivsub
  as equiv_dot.
Proof.
intros m1 m1' H1 m2 m2' H2.
apply equivsub_dot; auto.
Qed.


Add Parametric Morphism object : (@subst object)
  with signature equivsub ==> equiv ==> equiv
  as equiv_subst.
Proof.
intros s s' Hs m m' Hm.
apply equiv_funct; auto.
Qed.


Add Parametric Morphism object : (@under object)
  with signature eq ==> equivsub ==> equivsub
  as equiv_under.
Proof.
intros n s s' Hs.
apply equivsub_under; auto.
Qed.


Add Parametric Morphism object : (@List.app (@hyp object))
  with signature equivctx ==> equivctx ==> equivctx
  as app_mor.
Proof.
intros G1 G1' H1 G2 G2' H2.
apply Forall2_app; auto.
Qed.


Add Parametric Morphism object : (@substctx object)
  with signature equivsub ==> equivctx ==> equivctx
  as equiv_substctx.
Proof.
intros s s' Hs G G' HG.
apply equivctx_funct; auto.
Qed.


Add Parametric Morphism object : (@nsucc object)
  with signature equiv ==> equiv
  as equiv_nsucc.
Proof.
intros m1 m1' H1.
rewrite H1.
reflexivity.
Qed.


(*
Goal
  forall G G' a a' b m n,
    sequivctx G G'
    -> sequiv a a'
    -> tr G (deq m n (arrow a b))
    -> tr G' (deq m n (arrow a' b)).
Proof.
intros G G' a a' b m n Heq Heq' H.
rewrite <- Heq.
rewrite <- Heq'.
exact H.
Qed.
*)
