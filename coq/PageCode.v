
Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Equality.
Require Import Relation.
Require Import Syntax.
Require Import Ofe.
Require Import Uniform.
Require Import Spaces.
Require Import Dynamic.
Require Import Hygiene.
Require Import Equivalence.
Require Import Equivalences.
Require Import Ordinal.
Require Import Page.
Require Import Intensional.
Require Import Candidate.
Require Import System.
Require Import MapTerm.
Require Import Defined.


(* Literals *)

Fixpoint natlit {object} (i : nat) : term object :=
  match i with
  | 0 => nzero
  | S i' => nsucc (natlit i')
  end.


(* This is defined in a somewhat clumsy way to get the hygiene automation to work. *)
Definition finof w :=
  match lt_ord_dec w omega with
  | left h => pi1 (lt_omega_fin w h)
  | right _ => 0
  end.


(* Precondition: w finite *)
Definition levellit {object} w : term object
  :=
  natlit (finof w).


(* Precondition: str = cex = cin *)
Definition pagelit {object} pg : term object
  :=
  levellit (str pg).



(* Hygiene *)

Lemma natlit_closed :
  forall object i, @hygiene object clo (natlit i).
Proof.
intros object i.
induct i; intros; cbn [natlit]; repeat (apply hygiene_auto; cbn; repeat2 split; auto).
Qed.


Local Ltac prove_hygiene :=
  repeat (first [ apply hygiene_shift_permit
                | apply hygiene_sumbool
                | apply natlit_closed
                | apply hygiene_auto; cbn; repeat2 split; auto
                ]);
  eauto using hygiene_weaken, clo_min, hygiene_shift', hygiene_subst1;
  try (apply hygiene_var; cbn; auto; done).


Lemma levellit_closed :
  forall object w, @hygiene object clo (levellit w).
Proof.
intros object w.
unfold levellit.
prove_hygiene.
Qed.


Lemma pagelit_closed :
  forall object pg, @hygiene object clo (pagelit pg).
Proof.
intros object pg.
unfold pagelit.
apply levellit_closed.
Qed.


Lemma theta_closed :
  forall object, @hygiene object clo theta.
Proof.
intro object.
unfold theta.
prove_hygiene.
Qed.


Lemma leqtype_closed :
  forall object, @hygiene object clo leqtp.
Proof.
intro object.
unfold leqtp.
prove_hygiene.
Qed.


Lemma lttype_closed :
  forall object, @hygiene object clo lttp.
Proof.
intro object.
unfold lttp.
prove_hygiene.
Qed.


Lemma nzero_closed : forall object, hygiene clo (@nzero object).
Proof.
intro object.
unfold nzero.
apply hygiene_auto; cbn.
do2 2 split; auto.
  {
  apply hygiene_auto; cbn; auto.
  }

  {
  apply hygiene_auto; cbn.
  split; auto.
  }
Qed.


(* Substitution *)

Lemma subst_letnext :
  forall object (s : @sub object) m n, subst s (letnext m n) = letnext (subst s m) (subst (under 1 s) n).
Proof.
intros.
unfold letnext.
simpsub.
reflexivity.
Qed.


Lemma subst_sumtype :
  forall object (s : @sub object) a b, subst s (sumtype a b) = sumtype (subst s a) (subst s b).
Proof.
intros.
unfold sumtype.
simpsub.
reflexivity.
Qed.


Lemma subst_sumleft :
  forall object (s : @sub object) m, subst s (sumleft m) = sumleft (subst s m).
Proof.
prove_subst.
Qed.


Lemma subst_sumright :
  forall object (s : @sub object) m, subst s (sumright m) = sumright (subst s m).
Proof.
prove_subst.
Qed.


Lemma subst_sumcase :
  forall object (s : @sub object) m n p, subst s (sumcase m n p) = sumcase (subst s m) (subst (under 1 s) n) (subst (under 1 s) p).
Proof.
intros.
unfold sumcase.
simpsub.
reflexivity.
Qed.


Lemma subst_nattp :
  forall object (s : @sub object), subst s nattp = nattp.
Proof.
prove_subst.
Qed.


Lemma subst_nzero :
  forall object (s : @sub object), subst s nzero = nzero.
Proof.
prove_subst.
Qed.


Lemma subst_nsucc :
  forall object (s : @sub object) a, subst s (nsucc a) = nsucc (subst s a).
Proof.
intros.
unfold nsucc.
simpsub.
reflexivity.
Qed.


Lemma subst_natlit :
  forall object (s : @sub object) i, subst s (natlit i) = natlit i.
Proof.
intros object s i.
induct i; auto.
(* S *)
intros i IH.
cbn [natlit].
rewrite -> subst_nsucc.
rewrite -> IH.
reflexivity.
Qed.


Hint Rewrite subst_letnext subst_sumtype subst_sumleft subst_sumright subst_sumcase subst_nattp subst_nzero subst_nsucc subst_natlit : subst.


Lemma subst_levellit :
  forall (s : ssub) lv,
    subst s (levellit lv) = levellit lv.
Proof.
intros s lv.
unfold levellit.
simpsub.
reflexivity.
Qed.


Lemma subst_pagelit :
  forall (s : ssub) pg,
    subst s (pagelit pg) = pagelit pg.
Proof.
intros s pg.
unfold pagelit, levellit.
simpsub.
reflexivity.
Qed.


Hint Rewrite subst_levellit subst_pagelit : subst.


Lemma subst_theta :
  forall object (s : @sub object), subst s theta = theta.
Proof.
intros object s.
apply subst_into_closed.
prove_hygiene.
Qed.


Hint Rewrite subst_theta : subst.


Lemma subst_wind :
  forall object (s : @sub object) f, subst s (wind f) = wind (subst s f).
Proof.
intros object s f.
unfold wind.
simpsub.
reflexivity.
Qed.


Hint Rewrite subst_wind : subst.


Lemma subst_leqpagetp :
  forall object (s : @sub object) a b, subst s (leqpagetp a b) = leqpagetp (subst s a) (subst s b).
Proof.
intros.
unfold leqpagetp.
simpsub.
reflexivity.
Qed.


Lemma subst_ltpagetp :
  forall object (s : @sub object) a b, subst s (ltpagetp a b) = ltpagetp (subst s a) (subst s b).
Proof.
intros.
unfold ltpagetp.
simpsub.
reflexivity.
Qed.


Hint Rewrite subst_leqpagetp subst_ltpagetp : subst.


(* Dynamic semantics *)

Lemma value_sumtype : forall {object a b}, value (@sumtype object a b).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_sumleft : forall {object m}, value (@sumleft object m).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_sumright : forall {object m}, value (@sumright object m).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_nattp : forall {object}, value (@nattp object).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_nzero : forall {object}, value (@nzero object).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_nsucc : forall {object m}, value (@nsucc object m).
Proof.
intros; apply value_i; eauto with dynamic.
Qed.


Lemma value_natlit : forall {object i}, value (@natlit object i).
Proof.
intros.
destruct i; cbn; auto using value_nzero, value_nsucc.
Qed.


Hint Resolve value_sumtype value_sumleft value_sumright value_nattp value_nzero value_nsucc value_natlit : dynamic.



(* Mapping *)

Lemma map_nattp :
  forall A B (f : A -> B), map_term f nattp = nattp.
Proof.
auto.
Qed.


Lemma map_nzero :
  forall A B (f : A -> B), map_term f nzero = nzero.
Proof.
auto.
Qed.


Lemma map_nsucc :
  forall A B (f : A -> B) a, map_term f (nsucc a) = nsucc (map_term f a).
Proof.
intros A B f a.
unfold nsucc, sumright.
simpmap.
f_equal.
Qed.


Lemma map_theta :
  forall A B (f : A -> B), map_term f theta = theta.
Proof.
intros A B f.
unfold theta.
simpmap.
reflexivity.
Qed.


Lemma map_wind :
  forall A B (f : A -> B) m, map_term f (wind m) = wind (map_term f m).
Proof.
intros A B f m.
unfold wind.
simpmap.
rewrite -> map_theta.
reflexivity.
Qed.


Lemma map_natlit :
  forall A B (f : A -> B) i, map_term f (natlit i) = natlit i.
Proof.
intros A B f i.
induct i; auto.
intros i IH.
cbn [natlit].
rewrite -> map_nsucc.
f_equal; auto.
Qed.


Hint Rewrite map_nattp map_nzero map_nsucc map_theta map_wind map_natlit : map.


Lemma map_levellit :
  forall A B (f : A -> B) l,
    map_term f (levellit l) = levellit l.
Proof.
intros A B f l.
unfold levellit.
simpmap.
reflexivity.
Qed.


Lemma map_pagelit :
  forall A B (f : A -> B) pg,
    map_term f (pagelit pg) = pagelit pg.
Proof.
intros A B f pg.
unfold pagelit, levellit.
simpmap.
reflexivity.
Qed.


Lemma map_ltpagetp :
  forall A B (f : A -> B) a b,
    map_term f (ltpagetp a b) = ltpagetp (map_term f a) (map_term f b).
Proof.
intros A B f a b.
unfold ltpagetp.
simpmap.
reflexivity.
Qed.


Hint Rewrite map_levellit map_pagelit map_ltpagetp : map.


(* Nat/level/page interpretation *)

Inductive natinterp : sterm -> nat -> Prop :=
| natinterp_0 :
    forall m n p,
      hygiene clo m
      -> star step m (ppair n p)
      -> star step n btrue
      -> star step p triv
      -> natinterp m 0

| natinterp_S :
    forall m n p i,
      hygiene clo m
      -> star step m (ppair n p)
      -> star step n bfalse
      -> natinterp p i
      -> natinterp m (S i)
.


Definition lvinterp (m : sterm) (w : ordinal) : Prop
  :=
  exists i,
    natinterp m i
    /\ w = fin i.


(* If we don't find a use for pages with varying components,
   we'll make them all the same for simplicity's sake.
*)
Definition pginterp (m : sterm) (pg : page) :=
  exists w,
    lvinterp m w
    /\ str pg = w
    /\ cex pg = w
    /\ cin pg = w.


Lemma natinterp_closed :
  forall m i,
    natinterp m i
    -> hygiene clo m.
Proof.
intros m i H.
invert H; auto.
Qed.


Lemma lvinterp_closed :
  forall m w,
    lvinterp m w
    -> hygiene clo m.
Proof.
intros m w H.
destruct H as (? & ? & _); eauto using natinterp_closed.
Qed.


Lemma pginterp_closed :
  forall m pg,
    pginterp m pg
    -> hygiene clo m.
Proof.
intros m l H.
destruct H as (w & H & _).
eapply lvinterp_closed; eauto.
Qed.



Lemma natinterp_equiv :
  forall m m' i,
    hygiene clo m'
    -> equiv m m'
    -> natinterp m i
    -> natinterp m' i.
Proof.
intros m m' i Hcl Hequiv H.
revert m' Hcl Hequiv.
induct H.

(* 0 *)
{
intros m n p _ Hstepsm Hstepsn Hstepsp m' Hcl Hequiv.
so (equiv_eval _#4 Hequiv (conj Hstepsm value_ppair)) as (m'' & (Hstepsm' & _) & Hmc).
invertc_mc Hmc.
intros n' Hequivn p' Hequivp <-.
fold (ppair n' p') in *.
so (equiv_eval _#4 Hequivn (conj Hstepsn value_btrue)) as (n'' & (Hstepsn' & _) & Hmc).
invertc_mc Hmc.
intros <-.
fold (@btrue (obj stop)) in *.
so (equiv_eval _#4 Hequivp (conj Hstepsp value_triv)) as (p'' & (Hp'' & _) & Hmc).
invertc_mc Hmc.
intros <-.
fold (@triv (obj stop)) in *.
eapply natinterp_0; eauto.
}

(* S *)
{
intros m n p i _ Hstepsm Hstepsn _ IH m' Hcl Hequiv.
so (equiv_eval _#4 Hequiv (conj Hstepsm value_ppair)) as (m'' & (Hstepsm' & _) & Hmc).
invertc_mc Hmc.
intros n' Hequivn p' Hequivp <-.
fold (ppair n' p') in *.
so (equiv_eval _#4 Hequivn (conj Hstepsn value_bfalse)) as (n'' & (Hstepsn' & _) & Hmc).
invertc_mc Hmc.
intros <-.
fold (@bfalse (obj stop)) in *.
eapply natinterp_S; eauto.
apply IH; auto.
prove_hygiene.
so (hygiene_invert_auto _#5 (steps_hygiene _#4 Hstepsm' Hcl)) as H; cbn in H.
destruct H as (_ & H & _).
exact H.
}
Qed.


Lemma lvinterp_equiv :
  forall lv lv' w,
    hygiene clo lv'
    -> equiv lv lv'
    -> lvinterp lv w
    -> lvinterp lv' w.
Proof.
intros lv lv' w Hcl Hequiv H.
destruct H as (i & Hint & ->).
exists i; split; auto.
eapply natinterp_equiv; eauto.
Qed.


Lemma pginterp_equiv :
  forall m m' pg,
    hygiene clo m'
    -> equiv m m'
    -> pginterp m pg
    -> pginterp m' pg.
Proof.
intros m m' pg Hcl Hequiv H.
destruct H as (i & Hint & Hstr & Hcex & Hcin).
exists i.
eauto using lvinterp_equiv.
Qed.


Lemma natinterp_fun :
  forall m i i',
    natinterp m i
    -> natinterp m i'
    -> i = i'.
Proof.
intros m i i' Hi Hi'.
revert i' Hi'.
induct Hi.

(* 0 *)
{
intros m n p _ Hstepsm Hstepsn Hstepsp ii Hii.
invertc Hii; auto.
intros n' p' i' _ Hstepsm' Hstepsn' _ <-.
exfalso.
so (determinism_eval _#4 (conj Hstepsm value_ppair) (conj Hstepsm' value_ppair)) as Heq.
injectionc Heq.
intros <- <-.
so (determinism_eval _#4 (conj Hstepsn value_btrue) (conj Hstepsn' value_bfalse)) as Heq.
discriminate Heq.
}

(* S *)
{
intros m n p i _ Hstepsm Hstepsn _ IH ii Hii.
invertc Hii.
  {
  intros n' p' _ Hstepsm' Hstepsn' _ <-.
  exfalso.
  so (determinism_eval _#4 (conj Hstepsm value_ppair) (conj Hstepsm' value_ppair)) as Heq.
  injectionc Heq.
  intros <- <-.
  so (determinism_eval _#4 (conj Hstepsn value_bfalse) (conj Hstepsn' value_btrue)) as Heq.
  discriminate Heq.
  }

  {
  intros n' p' i' _ Hstepsm' Hstepsn' Hi' <-.
  so (determinism_eval _#4 (conj Hstepsm value_ppair) (conj Hstepsm' value_ppair)) as Heq.
  injectionc Heq.
  intros <- <-.
  f_equal.
  apply IH; auto.
  }
}
Qed.


Lemma lvinterp_fun :
  forall m w w',
    lvinterp m w
    -> lvinterp m w'
    -> w = w'.
Proof.
intros m w w' H H'.
destruct H as (i & Hi & ->).
destruct H' as (i' & Hi' & ->).
so (natinterp_fun _#3 Hi Hi'); subst i'.
reflexivity.
Qed.


Lemma pginterp_fun :
  forall m pg pg',
    pginterp m pg
    -> pginterp m pg'
    -> pg = pg'.
Proof.
intros m pg pg' Hint Hint'.
destruct Hint as (i & Hint & Hstr & Hcex & Hcin).
destruct Hint' as (i' & Hint' & Hstr' & Hcex' & Hcin').
so (lvinterp_fun _#3 Hint Hint') as Heq.
move Heq after Hstr.
subst i'.
apply page_extensionality; etransitivity; eauto.
Qed.


Lemma lvinterp_lt_omega :
  forall lv w,
    lvinterp lv w
    -> w << omega.
Proof.
intros lv w H.
destruct H as (i & _ & ->).
apply le_fin_omega.
Qed.


Lemma lvinterp_lt_top :
  forall lv w,
    lvinterp lv w
    -> w << top.
Proof.
intros lv w H.
eapply lt_le_ord_trans; eauto using lvinterp_lt_omega, omega_top.
Qed.


Lemma pginterp_lt_top :
  forall lv pg,
    pginterp lv pg
    -> lt_page pg toppg.
Proof.
intros lv [str cex cin] H.
unfold pginterp in H.
cbn in H.
destruct H as (w & Hint & -> & -> & ->).
so (lvinterp_lt_top _ _ Hint) as Hlt.
split; cbn; auto.
Qed.


Lemma pginterp_succ_lt_top :
  forall lv pg h,
    pginterp lv pg
    -> lt_page (succ_page pg h) toppg.
Proof.
intros lv [str cex cin] h H.
unfold pginterp in H.
cbn in H.
destruct H as (w & Hint & -> & -> & ->).
so (lvinterp_lt_omega _ _ Hint) as Hlt.
assert (succ w << top).
  {
  refine (lt_le_ord_trans _#3 _ omega_top).
  apply omega_limit; auto.
  }
split; cbn; auto.
Qed.


Lemma lt_page_impl_succ_le_page :
  forall pg pg' h,
    lt_page pg pg'
    -> le_page (succ_page pg h) pg'.
Proof.
intros pg pg' h H.
destruct H as (Hstr & Hcex).
do2 2 split; cbn; auto.
eapply lt_le_ord_trans; eauto.
apply cin_cex.
Qed.


Lemma pginterp_str_top :
  forall lv pg,
    pginterp lv pg
    -> str pg << top.
Proof.
intros lv pg H.
destruct H as (i & Hi & Hstr & _).
subst i.
eapply lvinterp_lt_top; eauto.
Qed.


Lemma pginterp_cex_top :
  forall lv pg,
    pginterp lv pg
    -> cex pg << top.
Proof.
intros lv pg H.
destruct H as (i & Hi & _ & Hcex & _).
subst i.
eapply lvinterp_lt_top; eauto.
Qed.


Lemma pginterp_cin_top :
  forall lv pg,
    pginterp lv pg
    -> cin pg << top.
Proof.
intros lv pg H.
eapply le_lt_ord_trans; eauto using cin_cex.
eapply pginterp_cex_top; eauto.
Qed.


Lemma natinterp_nzero :
  natinterp nzero 0.
Proof.
unfold nzero.
eapply natinterp_0; eauto using star_refl; try prove_hygiene.
Qed.


Lemma natinterp_nsucc :
  forall m i,
    natinterp m i
    -> natinterp (nsucc m) (S i).
Proof.
intros m i Hint.
unfold nsucc.
so (natinterp_closed _ _ Hint) as Hcl.
eapply natinterp_S; eauto using star_refl; try prove_hygiene.
Qed.


Lemma natinterp_natlit :
  forall i, natinterp (natlit i) i.
Proof.
intros i.
induct i; auto using natinterp_nzero.
(* S *)
intros i IH.
cbn.
apply natinterp_nsucc; auto.
Qed.


Lemma finof_fin :
  forall i, finof (fin i) = i.
Proof.
intro i.
unfold finof.
erewrite -> lt_ord_dec_is.
Unshelve.
2:{
  apply lt_fin_omega.
  }
set (X := lt_omega_fin (fin i) (lt_fin_omega i 0)).
destruct X as (i' & Heq).
injection Heq.
intros <-.
reflexivity.
Qed.


Lemma lvinterp_levellit :
  forall m w,
    lvinterp m w
    -> lvinterp (levellit w) w.
Proof.
intros m w H.
destruct H as (i & Hint & ->).
unfold levellit.
rewrite -> finof_fin.
exists i.
split; auto.
apply natinterp_natlit.
Qed.


Lemma pginterp_impl_pagelit :
  forall lv pg,
    pginterp lv pg
    -> pginterp (pagelit pg) pg.
Proof.
intros lv pg H.
destruct H as (i & Hint & Hstr & Hcex & Hcin).
exists i.
do2 3 split; auto.
unfold pagelit.
rewrite -> Hstr.
eapply lvinterp_levellit; eauto.
Qed.



(* Fix *)

Lemma theta_fix' :
  forall object (m : term object),
    plus step (app theta m) (app m (app theta m)).
Proof.
intros object m.
eexists.
split.
  {
  apply step_app1.
  unfold theta.
  apply step_app2.
  }
simpsub.
eapply star_step.
  {
  apply step_app2.
  }
simpsub.
apply star_refl.
Qed.


Lemma theta_fix :
  forall object (m : term object),
    star step (app theta m) (app m (app theta m)).
Proof.
intros object m.
apply plus_star.
apply theta_fix'.
Qed.
