
Require Import Axioms.
Require Import Tactics.
Require Import Ordinal.


Parameter top : ordinal.

Definition stop : ordinal := succ top.


Record page : Type :=
mk_page
  { str : ordinal;  (* stratification level *)
    cex : ordinal;  (* external candidate level *)
    cin : ordinal;  (* internal candidate level *)

    str_top : str <<= top;
    cex_top : cex <<= top;
    cin_cex : cin <<= cex;
  }.


Lemma cin_top : forall pg, cin pg <<= top.
Proof.
intros pg.
eapply le_ord_trans; eauto using cex_top, cin_cex.
Qed.


Lemma cin_stop : forall pg, cin pg <<= stop.
Proof.
intros pg.
exact (le_ord_trans _#3 (cin_top pg) (succ_nodecrease _)).
Qed.


(* Probably should change this to use w <<= cex pg instead. *)
Definition upd_cin (pg : page) {w : ordinal} (h : w <<= cin pg) : page
  :=
  mk_page (str pg) (cex pg) w (str_top pg) (cex_top pg) (le_ord_trans _#3 h (cin_cex pg)).


Lemma page_extensionality :
  forall pg pg',
    str pg = str pg'
    -> cex pg = cex pg'
    -> cin pg = cin pg'
    -> pg = pg'.
Proof.
intros pg pg' ? ? ?.
destruct pg as [wn wx wi h1 h2 h3].
destruct pg' as [wn' wx' wi' h1' h2' h3'].
cbn in *.
subst.
so (proof_irrelevance _ h1 h1'); subst h1'.
so (proof_irrelevance _ h2 h2'); subst h2'.
so (proof_irrelevance _ h3 h3'); subst h3'.
reflexivity.
Qed.


Lemma upd_cin_self :
  forall pg (h : cin pg <<= cin pg), upd_cin pg h = pg.
Proof.
intros pg h.
apply page_extensionality; auto.
Qed.


Definition le_page (pg pg' : page) : Prop
  :=
  str pg <<= str pg'
  /\ cex pg <<= cex pg'
  /\ cin pg <<= cin pg'.


Definition lt_page (pg pg' : page) : Prop
  :=
  str pg << str pg'
  /\ cex pg << cin pg'.


Definition toppg : page := 
  mk_page top top top (le_ord_refl _) (le_ord_refl _) (le_ord_refl _).


Definition succ_page (pg : page) (h : lt_page pg toppg) : page
  :=
  mk_page (succ (str pg)) (succ (cex pg)) (succ (cex pg))
    (h andel) (h ander) (le_ord_refl _).


Lemma le_page_refl :
  forall pg, le_page pg pg.
Proof.
intros pg.
do2 2 split; apply le_ord_refl.
Qed.


Lemma le_page_refl' :
  forall pg pg',
    pg = pg'
    -> le_page pg pg'.
Proof.
intros pg pg' H.
subst pg'.
apply le_page_refl.
Qed.


Lemma le_page_trans :
  forall pg1 pg2 pg3,
    le_page pg1 pg2
    -> le_page pg2 pg3
    -> le_page pg1 pg3.
Proof.
intros pg1 pg2 pg3 H12 H23.
destruct H12 as (? & ? & ?).
destruct H23 as (? & ? & ?).
do2 2 split; eauto using le_ord_trans.
Qed.


Lemma lt_le_page_trans :
  forall pg1 pg2 pg3,
    lt_page pg1 pg2
    -> le_page pg2 pg3
    -> lt_page pg1 pg3.
Proof.
intros pg1 pg2 pg3 H12 H23.
destruct H12 as (? & ?).
destruct H23 as (? & ? & ?).
split; eauto using lt_le_ord_trans.
Qed.


Lemma lt_page_succ :
  forall pg h,
    lt_page pg (succ_page pg h).
Proof.
intros pg h.
split; apply succ_increase.
Qed.


Lemma lt_page_impl_le_page :
  forall pg pg',
    lt_page pg pg'
    -> le_page pg pg'.
Proof.
intros pg pg' H.
destruct H as (Hstr & Hcex).
do2 2 split; cbn; eauto using lt_ord_impl_le_ord.
  {
  apply lt_ord_impl_le_ord.
  eapply lt_le_ord_trans; eauto.
  apply cin_cex.
  }

  {
  apply lt_ord_impl_le_ord.
  eapply lt_le_ord_trans; eauto.
  eapply le_lt_ord_trans.
    {
    apply cin_cex.
    }
  apply succ_increase.
  }
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


Lemma le_page_antisymm :
  forall pg pg',
    le_page pg pg'
    -> le_page pg' pg
    -> pg = pg'.
Proof.
intros pg pg' H1 H2.
destruct H1 as (? & ? & ?).
destruct H2 as (? & ? & ?).
apply page_extensionality; eauto using le_ord_antisymm.
Qed.


Lemma toppg_max :
  forall pg, le_page pg toppg.
Proof.
intros pg.
do2 2 split; cbn; auto using str_top, cex_top, cin_top.
Qed.


Lemma str_mono :
  forall pg pg', le_page pg pg' -> str pg <<= str pg'.
Proof.
intros pg pg' H.
destruct H as (? & ? & ?); auto.
Qed.


Lemma cex_mono :
  forall pg pg', le_page pg pg' -> cex pg <<= cex pg'.
Proof.
intros pg pg' H.
destruct H as (? & ? & ?); auto.
Qed.


Lemma cin_mono :
  forall pg pg', le_page pg pg' -> cin pg <<= cin pg'.
Proof.
intros pg pg' H.
destruct H as (? & ? & ?); auto.
Qed.


Lemma upd_cin_mono :
  forall pg pg' w w' (h : w <<= cin pg) (h' : w' <<= cin pg'),
    le_page pg pg'
    -> w <<= w'
    -> le_page (upd_cin pg h) (upd_cin pg' h').
Proof.
intros [wn wx wi] [wn' wx' wi'] w w' h h' Hle Hw.
destruct Hle as (? & ? & ?).
do2 2 split; auto.
Qed.


Definition max_page (pg pg' : page) : page :=
  mk_page
    (max_ord (str pg) (str pg'))
    (max_ord (cex pg) (cex pg'))
    (max_ord (cin pg) (cin pg'))
    (max_ord_lub _#3 (str_top pg) (str_top pg'))
    (max_ord_lub _#3 (cex_top pg) (cex_top pg'))
    (max_ord_mono _#4 (cin_cex pg) (cin_cex pg')).


Lemma le_page_max_l :
  forall pg pg', le_page pg (max_page pg pg').
Proof.
intros pg pg'.
do2 2 split; cbn; apply le_ord_max_l.
Qed.


Lemma le_page_max_r :
  forall pg pg', le_page pg' (max_page pg pg').
Proof.
intros pg pg'.
do2 2 split; cbn; apply le_ord_max_r.
Qed.


Parameter omega_top : omega <<= top.
