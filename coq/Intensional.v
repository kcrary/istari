
Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Equality.
Require Import Relation.
Require Import Syntax.
Require Import Ofe.
Require Import Uniform.
Require Import Spaces.
Require Import Urelsp.
Require Import Page.


Section object.


Arguments operator {object}.
Arguments term {object}.
Arguments row {object}.
Arguments urel {object}.
Arguments urel_ofe {object}.


Variable object : Type.


(* Basically we want to define:

     Inductive meta : Type :=
     | meta_nats   : nats -> meta
     | meta_fn     : forall (R : urel), (urelsp R -n> meta_ofe) -> meta
     | meta_pair   : meta -> meta -> meta
     | meta_half   : meta -> meta
     | meta_page   : page -> meta

     with meta_ofe : ofe := mk_ofe meta meta_dist ...

     with meta_dist : nat -> relation meta := ...

   but Coq provides no facility to define it directly.  It's the nonexpansive
   function space in meta_fn that makes it hard.  Because of it, all this stuff
   must be defined simultaneously.  The function space must be nonexpansive
   in order for meta_dist to be well-behaved (in particular, to be reflexive and
   downward closed).


   The meta_page case would be easy to get rid of, I just haven't bothered yet.
   We just reduce pages to syntax, and then use meta_term.
*)


Local Inductive pmeta : Type :=
| pmeta_nats   : car nats_ofe -> pmeta
| pmeta_fn     : forall (R : car (@urel_ofe object)),
                   (urelsp_car R -> pmeta) -> pmeta
| pmeta_pair   : pmeta -> pmeta -> pmeta
| pmeta_half   : pmeta -> pmeta
| pmeta_page   : page -> pmeta
.


Local Inductive pmeta_dist : nat -> pmeta -> pmeta -> Prop :=
| pmeta_dist_nats n I J :
    dist n I J
    -> pmeta_dist n (pmeta_nats I) (pmeta_nats J)

| pmeta_dist_fn n (A B : car urel_ofe) f g :
    dist n A B
    -> (forall (C : urelsp_car A) (D : urelsp_car B),
          urelsp_dist_dep A B n C D
          -> pmeta_dist n (f C) (g D))
    -> pmeta_dist n (pmeta_fn A f) (pmeta_fn B g)

| pmeta_dist_pair n x1 x2 y1 y2 :
    pmeta_dist n x1 y1
    -> pmeta_dist n x2 y2
    -> pmeta_dist n (pmeta_pair x1 x2) (pmeta_pair y1 y2)

| pmeta_dist_half n x y :
    pmeta_dist n x y
    -> pmeta_dist (S n) (pmeta_half x) (pmeta_half y)

| pmeta_dist_page n pg :
    pmeta_dist (S n) (pmeta_page pg) (pmeta_page pg)

| pmeta_dist_zero x y :
    pmeta_dist 0 x y
.


Local Inductive valid : pmeta -> Prop :=
| valid_nats I : valid (pmeta_nats I)

| valid_fn A f :
    (forall C, valid (f C))
    -> (forall n (C D : car (urelsp A)),
          dist n C D
          -> pmeta_dist n (f C) (f D))
    -> valid (pmeta_fn A f)

| valid_pair x y :
    valid x
    -> valid y
    -> valid (pmeta_pair x y)

| valid_half x :
    valid x
    -> valid (pmeta_half x)

| valid_page pg :
    valid (pmeta_page pg)
.


Definition meta := existsT (x : pmeta), valid x.


Definition meta_dist n (x y : meta) : Prop :=
  pmeta_dist n (pi1 x) (pi1 y).


Lemma meta_dist_refl :
  forall n x, meta_dist n x x.
Proof.
intros n x.
destruct x as (x, Hvalid).
unfold meta_dist.
cbn.
revert n.
induct Hvalid.

(* nats *)
{
intros I n.
apply pmeta_dist_nats.
apply dist_refl.
}

(* fn *)
{
intros A f _ IH Hne n.
apply pmeta_dist_fn.
  { apply dist_refl. }
intros C D HCD.
apply Hne.
apply urelsp_dist_dep_snd; auto.
}

(* pair *)
{
intros x y _ IH1 _ IH2 n.
apply pmeta_dist_pair; auto.
}

(* half *)
{
intros x _ IH n.
destruct n as [| n].
  {
  apply pmeta_dist_zero.
  }
apply pmeta_dist_half; auto.
}

(* page *)
{
intros pg n.
destruct n as [| n].
  {
  apply pmeta_dist_zero.
  }
apply pmeta_dist_page; auto.
}
Qed.


Lemma meta_dist_symm :
  forall n x y, meta_dist n x y -> meta_dist n y x.
Proof.
intros n x y Hxy.
destruct x as (x & Hx).
destruct y as (y & Hy).
unfold meta_dist in Hxy |- *.
cbn in Hxy |- *.
clear Hx Hy.
induct Hxy.

(* nats *)
{
intros.
apply pmeta_dist_nats.
apply dist_symm; auto.
}

(* fn *)
{
intros n A B f g HAB Hfg IH.
apply pmeta_dist_fn.
  { apply dist_symm; auto. }
intros D C HDC.
so (dist_dep_symm _ _ urelsp_dofe _#5 HDC) as HCD.
auto.
}

(* pair *)
{
intros n x1 x2 y1 y2 _ IH1 _ IH2.
apply pmeta_dist_pair; auto.
}

(* half *)
{
intros n x y _ IH.
apply pmeta_dist_half; auto.
}

(* page *)
{
intros n pg.
apply pmeta_dist_page; auto.
}

(* zero *)
{
intros x y.
apply pmeta_dist_zero.
}
Qed.


Local Lemma pmeta_dist_trans :
  forall n x y z, pmeta_dist n x y -> pmeta_dist n y z -> pmeta_dist n x z.
Proof.
intros n x y z Hxy.
revert z.
induct Hxy.

(* nats *)
{
intros n I J HIJ z H.
invertc H.
2:{
  intros <-.
  apply pmeta_dist_zero.
  }
intros K HJK <-.
apply pmeta_dist_nats.
eapply dist_trans; eauto.
}

(* fn *)
{
intros n A B f g HAB Hfg IH zz H.
so (lt_dec 0 n) as [Hpos | Hnpos].
2:{
  assert (n = 0) by omega.
  subst.
  apply pmeta_dist_zero.
  }
invertc H.
2:{
  intro; omega.
  }
intros C h HBC Hgh <-.
apply pmeta_dist_fn.
  { eapply dist_trans; eauto. }
intros D F HDF.
so (urelsp_neighbor n A B D Hpos HAB) as (E & HDE).
assert (urelsp_dist_dep B C n E F) as HEF.
  {
  eapply (dist_dep_trans _ _ urelsp_dofe); eauto.
  eapply (dist_dep_symm _ _ urelsp_dofe); auto.
  }
apply (IH _ E); auto.
}

(* pair *)
{
intros n x1 x2 y1 y2 _ IH1 _ IH2 z H.
invertc H.
2:{
  intros <-.
  apply pmeta_dist_zero.
  }
intros z1 z2 Hyz1 Hyz2 <-.
apply pmeta_dist_pair; eauto.
}

(* half *)
{
intros n x y _ IH1 zz H.
invertc H.
intros z Hyz <-.
apply pmeta_dist_half; auto.
}

(* page *)
{
intros n pg z H.
invertc H.
intros <-.
apply pmeta_dist_page.
}

(* zero *)
{
intros x y z H.
apply pmeta_dist_zero.
}
Qed.


Lemma meta_dist_trans :
  forall n x y z, meta_dist n x y -> meta_dist n y z -> meta_dist n x z.
Proof.
intros n x y z.
destruct x as (x & Hx).
destruct y as (y & Hy).
destruct z as (z & Hz).
unfold meta_dist.
cbn.
clear Hx Hy Hz.
intros Hxy Hyz.
eapply pmeta_dist_trans; eauto.
Qed.


Lemma meta_dist_limeq :
  forall x y,
    (forall n, meta_dist n x y)
    -> x = y.
Proof.
intros x y Hnear.
destruct x as [x Hx].
destruct y as [y Hy].
unfold meta_dist in Hnear.
cbn in Hnear.
apply exT_extensionality_prop.
cbn.
clear Hx Hy.
revert y Hnear.
induct x.

(* nats *)
{
intros I y Hnear.
invert (Hnear 1).
intros J _ <-.
f_equal.
apply (dist_limeq nats_ofe).
intros n.
so (Hnear n) as H.
invert H; auto.
intros <-.
apply dist_zero.
}

(* fn *)
{
intros A f IH yy Hnear.
invert (Hnear 1).
intros B g _ _ <-.
assert (A = B).
  {
  apply (dist_limeq urel_ofe).
  intro n.
  so (Hnear n) as H.
  invert H; auto.
  intros <-; apply dist_zero.
  }
subst B.
f_equal.
fextensionality 1.
intro C.
apply IH.
intro n.
so (Hnear n) as H.
invert H.
2:{
  intros <-; apply pmeta_dist_zero.
  }
intros _ Hfg.
apply Hfg.
apply (dist_dep_refl _ _ urelsp_dofe).
}

(* pair *)
{
intros x1 IH1 x2 IH2 y Hnear.
invert (Hnear 1).
intros y1 y2 _ _ <-.
f_equal.
  {
  apply IH1.
  intros n.
  so (Hnear n) as H.
  invert H; auto.
  intros <-; apply pmeta_dist_zero.
  }

  {
  apply IH2.
  intros n.
  so (Hnear n) as H.
  invert H; auto.
  intros <-; apply pmeta_dist_zero.
  }
}

(* half *)
{
intros p IH yy Hnear.
invert (Hnear 1).
intros y _ <-.
f_equal.
apply IH.
intros n.
so (Hnear (S n)) as H.
invert H; auto.
}

(* page *)
{
intros p y Hnear.
invert (Hnear 1).
intros <-.
reflexivity.
}
Qed.


Lemma meta_dist_downward :
  forall n x y, meta_dist (S n) x y -> meta_dist n x y.
Proof.
intros n x y.
destruct x as [x Hx].
destruct y as [y Hy].
unfold meta_dist.
cbn.
revert n y Hx Hy.
induct x.

(* nat *)
{
intros I n y _ _ Hdist.
invertc Hdist.
intros H HJ <-.
apply pmeta_dist_nats.
apply dist_downward; auto.
}

(* fn *)
{
intros A f IH n y Hxx Hyy H.
invertc H.
intros B g HAB Hfg <-.
invertc Hxx.
intros Hf Hnef.
invertc Hyy.
intros Hg Hneg.
apply pmeta_dist_fn.
  {
  apply dist_downward; auto.
  }
intros C D HCD.
change (car (urelsp A)) in C.
change (car (urelsp B)) in D.
(* Time for some fancy footwork. *)
so (lt_dec 0 n) as [Hpos | Hnpos].
2:{
  assert (n = 0) by omega; subst n.
  apply pmeta_dist_zero.
  }
so (urelsp_member_coerce _ (pred n) A A C (dist_refl urel_ofe _ _)) as HC'.
so (urelsp_member_coerce _ (pred n) B B D (dist_refl urel_ofe _ _)) as HD'.
set (C' := expair _ HC').
set (D' := expair _ HD').
assert (dist n C C') as HdistC.
  {
  intros j Hj.
  cbn.
  fextensionality 1.
  intro p.
  pextensionality.
    {
    intros; split; auto; omega.
    }

    {
    intros (_ & ?); auto.
    }
  }
assert (dist n D D') as HdistD.
  {
  intros j Hj.
  cbn.
  fextensionality 1.
  intro p.
  pextensionality.
    {
    intros; split; auto; omega.
    }

    {
    intros (_ & ?); auto.
    }
  }
assert (urelsp_dist_dep A B (S n) C' D') as HdistCD.
  {
  intros j _.
  fextensionality 1.
  intro p.
  pextensionality.
    {
    intros Hp.
    unfold C' in Hp.
    cbn in Hp.
    unfold D'.
    cbn.
    destruct Hp as (Hj' & Hp).
    split; [omega |].
    rewrite <- HCD; auto.
    omega.
    }

    {
    intros Hp.
    unfold C' in Hp.
    cbn in Hp.
    unfold D'.
    cbn.
    destruct Hp as (Hj' & Hp).
    split; [omega |].
    rewrite -> HCD; auto.
    omega.
    }
  }
apply (pmeta_dist_trans _ _ (f C')).
  {
  apply Hnef; auto.
  }
apply (pmeta_dist_trans _ _ (g D')).
2:{
  apply Hneg.
  apply dist_symm; auto.
  }
apply IH; auto.
}

(* pair *)
{
intros x1 IH1 x2 IH2 n y Hx Hy H.
invertc H.
intros y1 y2 H1 H2 <-.
invertc Hx.
intros Hx1 Hx2.
invertc Hy.
intros Hy1 Hy2.
apply pmeta_dist_pair; auto.
}

(* half *)
{
intros x IH n yy Hx Hy H.
invertc H.
intros y Hxy <-.
destruct n as [| n].
  {
  apply pmeta_dist_zero.
  }
apply pmeta_dist_half.
invertc Hx.
intro Hx.
invertc Hy.
intro Hy.
apply IH; auto.
}

(* page *)
{
intros pg n y _ _ H.
invertc H.
intros <-.
destruct n as [| n].
  {
  apply pmeta_dist_zero.
  }

  {
  apply pmeta_dist_page.
  }
}
Qed.


Lemma meta_dist_zero :
  forall x y, meta_dist 0 x y.
Proof.
intros x y.
destruct x as [x Hx].
destruct y as [y Hy].
unfold meta_dist.
cbn.
apply pmeta_dist_zero.
Qed.


Definition meta_ofe : ofe.
Proof.
apply (mk_ofe meta meta_dist); auto using meta_dist_limeq, meta_dist_downward, meta_dist_zero.
intros n; do2 2 split; intro; intros; eauto using meta_dist_refl, meta_dist_symm, meta_dist_trans.
Defined.


Definition meta_nats (I : car nats_ofe) : car meta_ofe
  :=
  expair (pmeta_nats I) (valid_nats I).


Definition meta_fn (R : @urel object) (f : urelsp R -n> meta_ofe) : car meta_ofe.
Proof.
refine (expair (pmeta_fn R (fun x => pi1 (pi1 f x))) _).
apply valid_fn.
  {
  intros C.
  cbn.
  exact (pi2 (pi1 f C)).
  }

  {
  intros n C D HCD.
  cbn.
  exact (pi2 f n C D HCD).
  }
Defined.


Definition meta_pair (x y : car meta_ofe) : car meta_ofe
  :=
  expair (pmeta_pair (pi1 x) (pi1 y)) (valid_pair _ _ (pi2 x) (pi2 y)).


Definition meta_half (x : car meta_ofe) : car meta_ofe
  :=
  expair (pmeta_half (pi1 x)) (valid_half _ (pi2 x)).


Definition meta_page (pg : page) : car meta_ofe
  :=
  expair (pmeta_page pg) (valid_page pg).


Local Lemma meta_nats_equal_expair :
  forall I H,
    meta_nats I = expair (pmeta_nats I) H.
Proof.
intros I H.
unfold meta_nats.
f_equal.
apply proof_irrelevance.
Qed.


Local Lemma make_fn :
  forall (R : @urel object) (f : urelsp_car R -> pmeta),
    (forall C, valid (f C))
    -> (forall n (C D : car (urelsp R)),
          dist n C D
          -> pmeta_dist n (f C) (f D))
    -> urelsp R -n> meta_ofe.
Proof.
intros R f Hvalid Hne.
refine (expair (fun C => expair (f C) (Hvalid C)) _).
intros n C D HCD.
cbn.
unfold meta_dist.
cbn.
exact (Hne _ _ _ HCD).
Defined.


Local Lemma destruct_valid_fn :
  forall R f,
    valid (pmeta_fn R f)
    -> forall C, valid (f C).
Proof.
intros R f H C.
invert H.
auto.
Qed.


Local Lemma destruct_valid_fn_ne :
  forall R f,
    valid (pmeta_fn R f)
    -> forall n (C D : car (urelsp R)),
         dist n C D
         -> pmeta_dist n (f C) (f D).
Proof.
intros R f H n C D Hdist.
invert H.
intros _ Hne.
apply Hne; auto.
Qed.


Local Lemma meta_fn_equal_expair :
  forall R f Hvalid,
    meta_fn R (make_fn R f (destruct_valid_fn R f Hvalid) (destruct_valid_fn_ne R f Hvalid))
    = expair (pmeta_fn R f) Hvalid.
Proof.
intros R f Hvalid.
unfold meta_fn.
apply exT_extensionality_prop.
cbn.
f_equal.
Qed.


Local Lemma destruct_valid_pair :
  forall x y,
    valid (pmeta_pair x y)
    -> valid x /\ valid y.
Proof.
intros x y H.
invert H; auto.
Qed.


Local Lemma meta_pair_equal_expair :
  forall x y H,
    meta_pair (expair x (destruct_valid_pair _ _ H andel)) (expair y (destruct_valid_pair _ _ H ander))
    =
    expair (pmeta_pair x y) H.
Proof.
intros x y H.
unfold meta_pair.
cbn.
f_equal.
apply proof_irrelevance.
Qed.


Local Lemma destruct_valid_half :
  forall x,
    valid (pmeta_half x)
    -> valid x.
Proof.
intros x H.
invert H; auto.
Qed.


Local Lemma meta_half_equal_expair :
  forall x H,
    meta_half (expair x (destruct_valid_half _ H))
    =
    expair (pmeta_half x) H.
Proof.
intros x H.
unfold meta_half.
cbn.
f_equal.
apply proof_irrelevance.
Qed.


Local Lemma meta_page_equal_expair :
  forall pg H,
    meta_page pg
    =
    expair (pmeta_page pg) H.
Proof.
intros pg H.
unfold meta_page.
f_equal.
apply proof_irrelevance.
Qed.


Lemma meta_rect :
  forall (P : meta -> Type),
    (forall (I : nats), P (meta_nats I))
    -> (forall R (f : urelsp R -n> meta_ofe),
          (forall (C : urelsp_car R),
             P (pi1 f C))
            -> P (meta_fn R f))
    -> (forall x, P x -> forall y, P y -> P (meta_pair x y))
    -> (forall x, P x -> P (meta_half x))
    -> (forall pg, P (meta_page pg))
    -> forall (x : meta), P x.
Proof.
intros P Hnats Hfn Hpair Hhalf Hpage x.
destruct x as [x Hx].
revert Hx.
induct x.

(* nats *)
{
intros I HI.
exact (transport (meta_nats_equal_expair _ _) P (Hnats I)).
}

(* fn *)
{
intros R f IH Hx.
refine (transport (meta_fn_equal_expair R f Hx) P _).
apply Hfn.
cbn.
intro C.
apply IH.
}

(* pair *)
{
intros x IH1 y IH2 Hxy.
refine (transport (meta_pair_equal_expair x y Hxy) P _).
apply Hpair; auto.
}

(* half *)
{
intros x IH Hx.
refine (transport (meta_half_equal_expair x Hx) P _).
apply Hhalf; auto.
}

(* page*)
{
intros pg Hvalid.
refine (transport (meta_page_equal_expair pg Hvalid) P _).
apply Hpage.
}
Defined.


Lemma meta_rect_nats :
  forall
    (P : meta -> Type)
    (Hnats : forall (I : nats), P (meta_nats I))
    (Hfn : forall R (f : urelsp R -n> meta_ofe),
             (forall (C : urelsp_car R),
                P (pi1 f C))
               -> P (meta_fn R f))
    (Hpair : forall x, P x -> forall y, P y -> P (meta_pair x y))
    (Hhalf : forall x, P x -> P (meta_half x))
    (Hpage : forall pg, P (meta_page pg))
    I,
      meta_rect P Hnats Hfn Hpair Hhalf Hpage (meta_nats I)
      =
      Hnats I.
Proof.
intros P Hnats Hfn Hpair Hhalf Hpage I.
unfold meta_rect.
cbn.
set (Heq := meta_nats_equal_expair I (valid_nats I)).
clearbody Heq.
unfold meta_nats in Heq.
substrefl Heq.
reflexivity.
Qed.


Lemma meta_rect_fn :
  forall
    (P : meta -> Type)
    (Hnats : forall (I : nats), P (meta_nats I))
    (Hfn : forall R (f : urelsp R -n> meta_ofe),
             (forall (C : urelsp_car R),
                P (pi1 f C))
               -> P (meta_fn R f))
    (Hpair : forall x, P x -> forall y, P y -> P (meta_pair x y))
    (Hhalf : forall x, P x -> P (meta_half x))
    (Hpage : forall pg, P (meta_page pg))
    R f,
      meta_rect P Hnats Hfn Hpair Hhalf Hpage (meta_fn R f)
      =
      Hfn R f (fun C => meta_rect P Hnats Hfn Hpair Hhalf Hpage (pi1 f C)).
Proof.
intros P Hnats Hfn Hpair Hhalf Hpage R f.
unfold meta_rect.
cbn.
apply heq_impl_eq.
eapply heq_trans.
  { apply heq_transport. }
assert (forall (f g : urelsp R -n> meta_ofe) (h : f = g) H H',
          transport h (fun f => forall C, P (pi1 f C)) H = H'
          -> heq (Hfn R f H) (Hfn R g H')) as Hprop.
  {
  clear f.
  intros f g h H H' Heq.
  subst g.
  cbn in Heq.
  subst H'.
  apply heq_refl.
  }
eapply Hprop; clear Hprop.
Unshelve.
2:{
  apply exT_extensionality_prop.
  cbn.
  fextensionality 1.
  intro C.
  cbn.
  apply exT_extensionality_prop.
  cbn.
  reflexivity.
  }
match goal with
| |- transport ?X _ _ = _ => set (Heq := X); clearbody Heq
end.
fextensionality 1.
intro C.
rewrite -> (app_transport_cod_dep _ _ _ _ _ Heq).
rewrite -> transport_commute.
match goal with
| |- transport ?X _ _ = _ => set (Heq' := X); clearbody Heq'
end.
cbn in Heq'.
destruct f as [f Hne].
cbn.
cbn in Heq'.
match type of Heq' with
| expair _ ?X = _ => set (Hvalid := X) in * |- *
end.
clearbody Hvalid.
cbn in Hvalid.
set (X := f C) in Heq', Hvalid |- *.
clearbody X.
destruct X as [x Hx].
cbn in Hvalid, Heq' |- *.
so (proof_irrelevance _ Hx Hvalid); subst Hx.
substrefl Heq'.
cbn.
reflexivity.
Qed.


Lemma meta_rect_pair :
  forall
    (P : meta -> Type)
    (Hnats : forall (I : nats), P (meta_nats I))
    (Hfn : forall R (f : urelsp R -n> meta_ofe),
             (forall (C : urelsp_car R),
                P (pi1 f C))
               -> P (meta_fn R f))
    (Hpair : forall x, P x -> forall y, P y -> P (meta_pair x y))
    (Hhalf : forall x, P x -> P (meta_half x))
    (Hpage : forall pg, P (meta_page pg))
    x y,
      meta_rect P Hnats Hfn Hpair Hhalf Hpage (meta_pair x y)
      =
      Hpair 
        x (meta_rect P Hnats Hfn Hpair Hhalf Hpage x)
        y (meta_rect P Hnats Hfn Hpair Hhalf Hpage y).
Proof.
intros P Hnats Hfn Hpair Hhalf Hpage x y.
unfold meta_rect.
cbn.
destruct x as [x Hx].
destruct y as [y Hy].
cbn.
set (Heq := meta_pair_equal_expair x y (valid_pair x y Hx Hy)).
clearbody Heq.
unfold meta_pair in Heq.
cbn in Heq.
set (Hvalid := destruct_valid_pair x y (valid_pair x y Hx Hy)) in Heq |- *.
clearbody Hvalid.
destruct Hvalid as [Hx' Hy'].
so (proof_irrelevance _ Hx Hx').
subst Hx'.
so (proof_irrelevance _ Hy Hy').
subst Hy'.
cbn in Heq.
substrefl Heq.
cbn.
reflexivity.
Qed.


Lemma meta_rect_half :
  forall
    (P : meta -> Type)
    (Hnats : forall (I : nats), P (meta_nats I))
    (Hfn : forall R (f : urelsp R -n> meta_ofe),
             (forall (C : urelsp_car R),
                P (pi1 f C))
               -> P (meta_fn R f))
    (Hpair : forall x, P x -> forall y, P y -> P (meta_pair x y))
    (Hhalf : forall x, P x -> P (meta_half x))
    (Hpage : forall pg, P (meta_page pg))
    x,
      meta_rect P Hnats Hfn Hpair Hhalf Hpage (meta_half x)
      =
      Hhalf 
        x (meta_rect P Hnats Hfn Hpair Hhalf Hpage x).
Proof.
intros P Hnats Hfn Hpair Hhalf Hpage x.
unfold meta_rect.
cbn.
destruct x as [x Hx].
cbn.
set (Heq := meta_half_equal_expair x (valid_half x Hx)).
clearbody Heq.
unfold meta_half in Heq.
cbn in Heq.
set (Hvalid := destruct_valid_half x (valid_half x Hx)) in Heq |- *.
clearbody Hvalid.
so (proof_irrelevance _ Hx Hvalid).
subst Hvalid.
cbn in Heq.
substrefl Heq.
cbn.
reflexivity.
Qed.


Lemma meta_rect_page :
  forall
    (P : meta -> Type)
    (Hnats : forall (I : nats), P (meta_nats I))
    (Hfn : forall R (f : urelsp R -n> meta_ofe),
             (forall (C : urelsp_car R),
                P (pi1 f C))
               -> P (meta_fn R f))
    (Hpair : forall x, P x -> forall y, P y -> P (meta_pair x y))
    (Hhalf : forall x, P x -> P (meta_half x))
    (Hpage : forall pg, P (meta_page pg))
    x,
      meta_rect P Hnats Hfn Hpair Hhalf Hpage (meta_page x)
      =
      Hpage x.
Proof.
intros P Hnats Hfn Hpair Hhalf Hpage pg.
unfold meta_rect.
cbn.
set (Heq := meta_page_equal_expair pg (valid_page pg)).
clearbody Heq.
so (proof_irrelevance _ Heq (eq_refl _)); subst Heq.
reflexivity.
Qed.


Lemma meta_dist_nats :
  forall n I J,
    dist n I J
    -> dist n (meta_nats I) (meta_nats J).
Proof.
intros n I J Hdist.
apply pmeta_dist_nats; auto.
Qed.


Definition meta_nats_ne : nats_ofe -n> meta_ofe
  :=
  expair meta_nats meta_dist_nats.


Lemma meta_dist_fn :
  forall n (A B : car urel_ofe) (f : urelsp A -n> meta_ofe) (g : urelsp B -n> meta_ofe),
    dist n A B
    -> (forall (C : car (urelsp A)) (D : car (urelsp B)),
          urelsp_dist_dep A B n C D
          -> dist n (pi1 f C) (pi1 g D))
    -> dist n (meta_fn A f) (meta_fn B g).
Proof.
intros n A B f g HAB Hfg.
apply pmeta_dist_fn; auto.
Qed.


Lemma meta_dist_pair :
  forall n (a b c d : car meta_ofe),
    dist n a c
    -> dist n b d
    -> dist n (meta_pair a b) (meta_pair c d).
Proof.
intros n a b c d Hac Hbd.
apply pmeta_dist_pair; auto.
Qed.


Lemma meta_dist_half :
  forall n (a b : car meta_ofe),
    dist n a b
    -> dist (S n) (meta_half a) (meta_half b).
Proof.
intros n a b H.
apply pmeta_dist_half; auto.
Qed.


Lemma meta_dist_page :
  forall n (pg : page),
    dist n (meta_page pg) (meta_page pg).
Proof.
intros n pg.
destruct n as [| n].
  {
  apply dist_zero.
  }

  {
  cbn.
  apply pmeta_dist_page.
  }
Qed.


Lemma meta_dist_nats_invert :
  forall n I x,
    n > 0
    -> dist n (meta_nats I) x
    -> exists J,
         x = meta_nats J
         /\ dist n I J.
Proof.
intros n I x Hpos Hdist.
destruct x as [x Hx].
cbn in Hdist.
unfold meta_dist in Hdist.
cbn in Hdist.
invert Hdist.
  2:{ intro; omega. }
intros J Hdist' <-.
exists J.
split; auto.
unfold meta_nats.
f_equal.
apply proof_irrelevance.
Qed.


Lemma meta_dist_fn_invert :
  forall n (A : car urel_ofe) f x,
    n > 0
    -> dist n (meta_fn A f) x
    -> exists B g,
         x = meta_fn B g
         /\ dist n A B
         /\ (forall C D,
               urelsp_dist_dep A B n C D
               -> dist n (pi1 f C) (pi1 g D)).
Proof.
intros n A f x Hpos Hdist.
destruct x as [x Hx].
cbn in Hdist.
unfold meta_dist in Hdist.
invert Hdist.
  2:{ intro; omega. }
intros B g HAB Hfg Heq.
cbn in Heq.
subst x.
invert Hx.
intros Hvalid Hne.
exists B.
exists (expair (fun C => expair (g C) (Hvalid C)) Hne).
do2 2 split; auto.
unfold meta_fn.
cbn.
apply exT_extensionality_prop.
cbn.
auto.
Qed.


Lemma meta_dist_pair_invert :
  forall n a b x,
    n > 0
    -> dist n (meta_pair a b) x
    -> exists c d,
         x = meta_pair c d
         /\ dist n a c
         /\ dist n b d.
Proof.
intros n a b x Hpos Hdist.
destruct x as [x Hx].
cbn in Hdist.
unfold meta_dist in Hdist.
invert Hdist.
  2:{ intro; omega. }
intros c d Hac Hbd Heq.
cbn in Heq.
subst x.
invert Hx.
intros Hc Hd.
exists (expair c Hc), (expair d Hd).
do2 2 split; auto.
unfold meta_pair.
cbn.
f_equal.
apply proof_irrelevance.
Qed.


Lemma meta_dist_half_invert :
  forall n a x,
    n > 0
    -> dist n (meta_half a) x
    -> exists b,
         x = meta_half b
         /\ dist (pred n) a b.
Proof.
intros n a x Hpos Hdist.
destruct x as [x Hx].
cbn in Hdist.
unfold meta_dist in Hdist.
invert Hdist.
  2:{ intro; omega. }
intros n' c Hac <- Heq.
cbn in Heq.
subst x.
invert Hx.
intros Hc.
exists (expair c Hc).
split; auto.
unfold meta_half.
cbn.
f_equal.
apply proof_irrelevance.
Qed.


Lemma meta_dist_page_invert :
  forall n pg x,
    n > 0
    -> dist n (meta_page pg) x
    -> x = meta_page pg.
Proof.
intros n pg x Hpos Hdist.
destruct x as [x Hx].
cbn in Hdist.
invert Hdist.
  2:{ intros; omega. }
intros n' <- Heq.
cbn in Heq.
subst x.
unfold meta_page.
f_equal.
apply proof_irrelevance.
Qed.


Global Opaque meta meta_dist meta_rect.
Global Opaque meta_nats meta_fn meta_pair meta_half meta_page.


Definition urelsp_sim_pred (A : @urel object) (x y : car (urelsp A)) : nat -> Prop
  :=
  fun i => exists m, pi1 x i m /\ pi1 y i m.


Lemma urelsp_sim_downward :
  forall (A : @urel object) (x y : urelsp_car A),
    forall i,
      urelsp_sim_pred A x y (S i)
      -> urelsp_sim_pred A x y i.
Proof.
intros A x y i H.
destruct H as (m & Hxm & Hym).
exists m.
split; apply (urelsp_downward _#4 (S i)); auto.
Qed.


Definition urelsp_sim (A : @urel object) (x y : car (urelsp A)) : car nats_ofe
  :=
  expair
    (urelsp_sim_pred A x y)
    (urelsp_sim_downward A x y).


Lemma urelsp_sim_inj :
  forall A (x y : car (urelsp A)),
    urelsp_sim A x = urelsp_sim A y
    -> x = y.
Proof.
intros A x y Heq.
apply exT_extensionality_prop.
fextensionality 2.
intros i m.
pextensionality.
  {
  intros Hxm.
  so (f_equal (fun z => pi1 (z x) i) Heq) as H.
  renameover H into Heq.
  cbn in Heq.
  unfold urelsp_sim_pred in Heq.
  assert (exists n, pi1 x i n /\ pi1 x i n) as H by eauto.
  rewrite -> Heq in H.
  destruct H as (n & Hyn & Hxn).
  eapply urelsp_trans; eauto.
  }

  {
  intros Hym.
  so (f_equal (fun z => pi1 (z y) i) Heq) as H.
  renameover H into Heq.
  cbn in Heq.
  unfold urelsp_sim_pred in Heq.
  assert (exists n, pi1 y i n /\ pi1 y i n) as H by eauto.
  rewrite <- Heq in H.
  destruct H as (n & Hxn & Hyn).
  eapply urelsp_trans; eauto.
  }
Qed.


Lemma urelsp_sim_nonexpansive :
  forall (A : urel) n (x x' y y' : car (urelsp A)),
      dist n x x'
      -> dist n y y'
      -> dist n (urelsp_sim A x y) (urelsp_sim A x' y').
Proof.
intros A n x x' y y' Hx Hy.
intros i Hi.
cbn.
unfold urelsp_sim_pred.
split.
  {
  intros (m & Hxm & Hym).
  exists m.
  rewrite <- (Hx i Hi).
  rewrite <- (Hy i Hi).
  auto.
  }

  {
  intros (m & Hxm & Hym).
  exists m.
  rewrite -> (Hx i Hi).
  rewrite -> (Hy i Hi).
  auto.
  }
Qed.


Lemma urelsp_sim_nonexpansive2 :
  forall (A : urel) (x : car (urelsp A)),
    forall n y y',
      dist n y y'
      -> dist n (urelsp_sim A x y) (urelsp_sim A x y').
Proof.
intros A x n y y' Hdist.
eapply urelsp_sim_nonexpansive; eauto.
apply dist_refl.
Qed.


Definition urelsp_sim_ne (A : urel) (x : car (urelsp A)) : urelsp A -n> nats_ofe
  :=
  expair
    (urelsp_sim A x)
    (urelsp_sim_nonexpansive2 A x).


Lemma urelsp_sim_nonexpansive_dep :
  forall (A B : car urel_ofe) n (x s : car (urelsp A)) (y t : car (urelsp B)),
    dist n A B
    -> dist_dep urelsp_dofe A B n x y
    -> dist_dep urelsp_dofe A B n s t
    -> dist n (urelsp_sim A x s) (urelsp_sim B y t).
Proof.
intros A B n x s y t HAB Hxy Hst.
intros i Hin.
unfold urelsp_sim, urelsp_sim_pred.
cbn in HAB, Hxy, Hst |- *.
unfold urelsp_dist_dep in Hxy, Hst.
unfold urel_dist in HAB.
split.
  {
  intros (m & Hxm & Hsm).
  exists m.
  rewrite <- Hxy; auto.
  rewrite <- Hst; auto.
  }

  {
  intros (m & Hxm & Hsm).
  exists m.
  rewrite -> Hxy; auto.
  rewrite -> Hst; auto.
  }
Qed.


Definition meta_term (R : urel) (C : urelsp_car R) : car meta_ofe 
  :=
  meta_fn R (nearrow_compose meta_nats_ne (urelsp_sim_ne R C)).


Lemma meta_dist_term :
  forall n (A B : car urel_ofe) C D,
    dist n A B
    -> urelsp_dist_dep A B n C D
    -> dist n (meta_term A C) (meta_term B D).
Proof.
intros n A B C D HAB HCD.
unfold meta_term.
apply meta_dist_fn; auto.
intros x y Hxy.
cbn -[dist].
apply meta_dist_nats.
eapply urelsp_sim_nonexpansive_dep; eauto.
Qed.


Lemma meta_fn_extensionality :
  forall A B f g,
    eq_dep urel (fun R => urelsp R -n> meta_ofe) A f B g
    -> meta_fn A f = meta_fn B g.
Proof.
intros A B f g H.
injectionT H.
intros <-.
injectionT H.
intros <-.
reflexivity.
Qed.


Lemma meta_term_extensionality :
  forall A B C D,
    eq_dep urel urelsp_car A C B D
    -> meta_term A C = meta_term B D.
Proof.
intros A B C D H.
injectionT H.
intros <-.
injectionT H.
intros <-.
reflexivity.
Qed.


Lemma meta_nats_inj :
  forall I J,
    meta_nats I = meta_nats J
    -> I = J.
Proof.
intros I J Heq.
so (f_equal 
      (fun z => meta_rect (fun _ => option nats) 
                  (fun A => Some A)
                  (fun _ _ _ => None)
                  (fun _ _ _ _ => None)
                  (fun _ _ => None)
                  (fun _ => None)
                  z)
      Heq) as Heq'.
cbn in Heq'.
rewrite -> !meta_rect_nats in Heq'.
injection Heq'.
auto.
Qed.


Lemma meta_fn_inj :
  forall A B f g,
    meta_fn A f = meta_fn B g
    -> eq_dep urel (fun R => urelsp R -n> meta_ofe) A f B g.
Proof.
intros A B f g Heq.
so (f_equal 
      (fun z => meta_rect (fun _ => option (exT urel (fun R => urelsp R -n> meta_ofe)))
                  (fun _ => None)
                  (fun R h _ => Some (expair R h))
                  (fun _ _ _ _ => None)
                  (fun _ _ => None)
                  (fun _ => None)
                  z)
      Heq) as Heq'.
cbn in Heq'.
rewrite -> !meta_rect_fn in Heq'.
injection Heq'.
intros Heq'' <-.
so (existT_injection_2 _#5 Heq'').
subst g.
apply eq_dep_refl.
Qed.


Lemma meta_pair_inj :
  forall a b c d,
    meta_pair a c = meta_pair b d
    -> a = b /\ c = d.
Proof.
intros a b c d Heq.
so (f_equal 
      (fun z => meta_rect (fun _ => option (meta * meta))
                  (fun _ => None)
                  (fun _ _ _ => None)
                  (fun x _ y _ => Some (x, y))
                  (fun _ _ => None)
                  (fun _ => None)
                  z)
      Heq) as Heq'.
cbn in Heq'.
rewrite -> !meta_rect_pair in Heq'.
injection Heq'.
auto.
Qed.


Lemma meta_half_inj :
  forall a b,
    meta_half a = meta_half b
    -> a = b.
Proof.
intros a b Heq.
so (f_equal 
      (fun z => meta_rect (fun _ => option meta)
                  (fun _ => None)
                  (fun _ _ _ => None)
                  (fun _ _ _ _ => None)
                  (fun x _ => Some x)
                  (fun _ => None)
                  z)
      Heq) as Heq'.
cbn in Heq'.
rewrite -> !meta_rect_half in Heq'.
injection Heq'.
auto.
Qed.


Lemma meta_page_inj :
  forall a b,
    meta_page a = meta_page b
    -> a = b.
Proof.
intros a b Heq.
so (f_equal 
      (fun z => meta_rect (fun _ => option page)
                  (fun _ => None)
                  (fun _ _ _ => None)
                  (fun _ _ _ _ => None)
                  (fun _ _ => None)
                  (fun x => Some x)
                  z)
      Heq) as Heq'.
cbn in Heq'.
rewrite -> !meta_rect_page in Heq'.
injection Heq'.
auto.
Qed.


Lemma meta_term_inj :
  forall A B C D,
    meta_term A C = meta_term B D
    -> eq_dep urel urelsp_car A C B D.
Proof.
unfold meta_term.
intros A B C D Heq.
so (meta_fn_inj _#4 Heq) as H.
injectionT H.
intros <-.
injectionT H.
intros Heq'.
apply eq_impl_eq_dep_snd.
apply (urelsp_sim_inj A).
fextensionality 1.
intros x.
apply meta_nats_inj.
so (f_equal (fun z => pi1 z x) Heq') as H.
cbn in H.
exact H.
Qed.


Lemma meta_dist_nats_invert' :
  forall n I J,
    dist n (meta_nats I) (meta_nats J)
    -> dist n I J.
Proof.
intros n I J Hdist.
apply dist_if_pos.
intro Hpos.
so (meta_dist_nats_invert _#3 Hpos Hdist) as (J' & Heq & Hdist').
so (meta_nats_inj _ _ Heq).
subst J'.
auto.
Qed.


Lemma meta_dist_fn_invert' :
  forall n (A B : car urel_ofe) f g,
    dist n (meta_fn A f) (meta_fn B g)
    -> dist n A B
       /\ (forall C D,
             urelsp_dist_dep A B n C D
             -> dist n (pi1 f C) (pi1 g D)).
Proof.
intros n A B f g Hdist.
so (lt_dec 0 n) as [Hpos | Hnpos].
2:{
  assert (n = 0) by omega; subst n.
  split; auto using dist_zero.
  }
so (meta_dist_fn_invert _#4 Hpos Hdist) as (B' & g' & Heq & H).
so (meta_fn_inj _#4 Heq) as Heq'.
so (eq_dep_impl_eq_fst _#6 Heq'); subst B'.
so (eq_dep_impl_eq_snd _#5 Heq'); subst g'.
exact H.
Qed.


Lemma meta_dist_pair_invert' :
  forall n a b c d,
    dist n (meta_pair a c) (meta_pair b d)
    -> dist n a b
       /\ dist n c d.
Proof.
intros n a b c d Hdist.
so (lt_dec 0 n) as [Hpos | Hnpos].
2:{
  assert (n = 0) by omega; subst n.
  split; auto using dist_zero.
  }
so (meta_dist_pair_invert _#4 Hpos Hdist) as (b' & d' & Heq & H).
so (meta_pair_inj _#4 Heq) as (<- & <-).
exact H.
Qed.


Lemma meta_dist_half_invert' :
  forall n a b,
    dist n (meta_half a) (meta_half b)
    -> dist (pred n) a b.
Proof.
intros n a b Hdist.
so (lt_dec 0 n) as [Hpos | Hnpos].
2:{
  assert (n = 0) by omega; subst n.
  cbn.
  apply meta_dist_zero.
  }
so (meta_dist_half_invert _#3 Hpos Hdist) as (b' & Heq & H).
so (meta_half_inj _ _ Heq); subst b'.
exact H.
Qed.


Definition iurel := @urel object /t\ meta.
Definition iurel_ofe := prod_ofe (@urel_ofe object) meta_ofe.


Definition den : car iurel_ofe -> car urel_ofe := fst.


Lemma den_nonexpansive : nonexpansive den.
Proof.
intros n r r' Hdist.
exact (Hdist andel).
Qed.  


Definition den_ne : iurel_ofe -n> urel_ofe := expair den den_nonexpansive.


Definition meta_null : car meta_ofe := meta_nats (nat_nats 0).


Definition iubase (R : urel) : iurel
  :=
  (R, meta_null).


Lemma den_iubase :
   forall (R : urel),
     den (iubase R) = R.
Proof.
intros.
reflexivity.
Qed.


Definition meta_urel (R : urel) : meta
  :=
  meta_fn R (nearrow_const _ _ meta_null).


Lemma meta_urel_nonexpansive :
  @nonexpansive urel_ofe meta_ofe meta_urel.
Proof.
intros i R R' Hdist.
apply meta_dist_fn; auto.
intros C D _.
apply dist_refl.
Qed.


Lemma meta_urel_inj :
  forall (A B : urel),
    meta_urel A = meta_urel B
    -> A = B.
Proof.
intros A B H.
so (meta_fn_inj _#4 H) as Heq.
exact (eq_dep_impl_eq_fst _#6 Heq).
Qed.


Definition meta_iurel (r : iurel) : meta
  :=
  meta_pair (meta_urel (fst r)) (snd r).


Lemma meta_iurel_nonexpansive :
  @nonexpansive iurel_ofe meta_ofe meta_iurel.
Proof.
intros i r r' Hdist.
destruct r as (R, x).
destruct r' as (R', y).
destruct Hdist as (HR, Hxy).
cbn in HR, Hxy.
apply meta_dist_pair; auto.
apply meta_urel_nonexpansive; auto.
Qed.


Definition meta_iurel_ne : iurel_ofe -n> meta_ofe
  :=
  expair meta_iurel (meta_iurel_nonexpansive).


Lemma meta_iurel_inj :
  forall (A B : iurel),
    meta_iurel A = meta_iurel B
    -> A = B.
Proof.
intros A B H.
so (meta_pair_inj _#4 H) as (Heq1 & Heq2).
apply prod_extensionality; auto.
eapply meta_urel_inj; eauto.
Qed.


End object.


Arguments meta_dist {object}.
Arguments den {object}.
Arguments den_ne {object}.
Arguments meta_nats {object}.
Arguments meta_fn {object}.
Arguments meta_term {object}.
Arguments meta_pair {object}.
Arguments meta_half {object}.
Arguments meta_page {object}.
Arguments meta_null {object}.
Arguments meta_urel {object}.
Arguments meta_iurel {object}.
Arguments meta_iurel_ne {object}.
Arguments iubase {object}.


Hint Resolve meta_dist_nats meta_dist_fn meta_dist_term meta_dist_pair : meta_dist.
Hint Rewrite meta_rect_nats meta_rect_fn meta_rect_pair : meta_rect.
