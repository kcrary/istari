
Require Import Axioms.
Require Import Tactics.
Require Import Relation.
Require Import Sigma.
Require Import Equality.
Require Import Syntax.
Require Import Hygiene.
Require Import Reduction.
Require Import Equivalence.
Require Import MapTerm.
Require Import Ofe.
Require Import Uniform.
Require Import Urelsp.
Require Import Ordinal.
Require Import Candidate.
Require Import Intensional.
Require Import IntensionalNerect.


Definition extend_xobj (v w : ordinal) (x : xobj v) : xobj w
  :=
  match x with
  | objnone => objnone

  | objsome Q h =>
      match lt_ord_dec (level (pi1 Q)) w with
      | left h' =>
          objsome Q h'

      | right _ =>
          objnone
      end
  end.


Definition extend (v w : ordinal) (Q : obj v) : obj w
  :=
  objin (extend_xobj v w (objout Q)).


Lemma extend_none :
  forall v w,
    extend v w (objin objnone) = objin objnone.
Proof.
intros v w.
unfold extend, extend_xobj.
rewrite -> objout_objin.
reflexivity.
Qed.


Lemma extend_some :
  forall v w Q h h',
    extend v w (objin (objsome Q h))
    =
    objin (objsome Q h').
Proof.
intros v w Q h h'.
unfold extend, extend_xobj.
rewrite -> objout_objin.
rewrite -> (lt_ord_dec_is _ _ h').
reflexivity.
Qed.


Lemma extend_some_to_none :
  forall v w Q h,
    ~ level (pi1 Q) << w
    -> extend v w (objin (objsome Q h)) = objin objnone.
Proof.
intros v w Q h Hnlt.
unfold extend, extend_xobj.
rewrite -> objout_objin.
rewrite -> (lt_ord_dec_is_not _ _ Hnlt).
reflexivity.
Qed.


Lemma extend_eq_objsome_form :
  forall v w x Q h,
    extend v w x = objin (objsome Q h)
    -> exists h', x = objin (objsome Q h').
Proof.
intros v w x Q h Heq.
rewrite <- (objin_objout _ x).
unfold extend, extend_xobj in Heq.
set (X := objout x) in Heq |- *.
destruct X as [Q' h' |].
  {
  set (X := lt_ord_dec (level (pi1 Q')) w) in Heq.
  destruct X as [Hlt | Hnlt].
    {
    injection (objin_inj _ _ _ Heq).
    intros ->.
    exists h'.
    reflexivity.
    }

    {
    discriminate (objin_inj _#3 Heq).
    }
  }

  {
  discriminate (objin_inj _#3 Heq).
  }
Qed.


Lemma extend_xobj_inv :
  forall v w, v <<= w -> forall x, extend_xobj w v (extend_xobj v w x) = x.
Proof.
intros v w Hle x.
destruct x as [Q h |].
  {
  cbn.
  rewrite -> (lt_ord_dec_is _ _ (lt_le_ord_trans _#3 h Hle)).
  cbn.
  rewrite -> (lt_ord_dec_is _ _ h).
  reflexivity.
  }

  {
  cbn.
  reflexivity.
  }
Qed.


Lemma extend_xobj_inj :
  forall v w, v <<= w -> injective (extend_xobj v w).
Proof.
intros v w Hle x y Heq.
so (f_equal (extend_xobj w v) Heq) as Heq'.
rewrite -> !extend_xobj_inv in Heq'; auto.
Qed.


Lemma extend_inv :
  forall v w, v <<= w -> inverses (extend w v) (extend v w).
Proof.
intros v w H x.
rewrite <- (objin_objout _ x) at 2.
unfold extend.
f_equal.
rewrite -> objout_objin.
rewrite -> extend_xobj_inv; auto.
Qed.


Lemma extend_inj :
  forall v w, v <<= w -> injective (extend v w).
Proof.
intros v w h.
eapply inverses_impl_injective; eauto using extend_inv.
Qed.


Lemma extend_term_equiv_inj :
  forall v w, v <<= w -> forall (m n : wterm v),
    equiv (map_term (extend v w) m) (map_term (extend v w) n)
    -> equiv m n.
Proof.
intros v w h m n Heq.
eapply map_term_equiv_inj; eauto.
apply extend_inj; auto.
Qed.


Lemma extend_term_inv :
  forall v w, v <<= w -> inverses (map_term (extend w v)) (map_term (extend v w)).
Proof.
intros v w Hlt.
apply map_term_inv.
apply extend_inv; auto.
Qed.


Lemma extend_term_inj :
  forall v w, v <<= w -> injective (map_term (extend v w)).
Proof.
intros v w h.
eapply inverses_impl_injective; eauto using extend_term_inv.
Qed.


Lemma extend_id :
  forall w,
    extend w w = (fun x => x).
Proof.
intros w.
fextensionality 1.
intro x.
rewrite <- (objin_objout _ x).
set (X := objout x).
unfold extend, extend_xobj.
rewrite -> objout_objin.
destruct X as [(Q, h) |]; auto.
cbn.
erewrite -> lt_ord_dec_is; eauto.
Qed.


Lemma extend_term_id :
  forall w m,
    map_term (extend w w) m = m.
Proof.
intros w m.
rewrite -> extend_id.
apply map_term_id.
Qed.


Lemma extend_sub_id :
  forall w s,
    map_sub (extend w w) s = s.
Proof.
intros w s.
rewrite -> extend_id.
apply map_sub_id.
Qed.


Lemma extend_compose_up :
  forall u v w,
    u <<= v
    -> forall x, extend u w x = extend v w (extend u v x).
Proof.
intros u v w Huv x.
unfold extend.
f_equal.
rewrite -> objout_objin.
set (X := @objout u x).
destruct X as [Q h |]; auto.
cbn.
rewrite -> (lt_ord_dec_is _ _ (lt_le_ord_trans _#3 h Huv)).
cbn.
reflexivity.
Qed.


Lemma extend_compose_down :
  forall u v w,
    w <<= v
    -> forall x, extend u w x = extend v w (extend u v x).
Proof.
intros u v w Hwv x.
unfold extend.
f_equal.
rewrite -> objout_objin.
set (X := @objout u x).

destruct X as [Q h |]; auto.
cbn.
set (X := lt_ord_dec (level (pi1 Q)) w).
destruct X as [Hlt | Hnlt].
  {
  rewrite -> (lt_ord_dec_is _ _ (lt_le_ord_trans _#3 Hlt Hwv)).
  cbn.
  rewrite -> (lt_ord_dec_is _ _ Hlt).
  reflexivity.
  }

  {
  set (X := lt_ord_dec (level (pi1 Q)) v).
  destruct X as [Hlt |].
    {
    cbn.
    rewrite -> (lt_ord_dec_is_not _ _ Hnlt).
    reflexivity.
    }
    
    {
    cbn.
    reflexivity.
    }
  }
Qed.


Lemma extend_term_compose_up :
  forall u v w,
    u <<= v
    -> forall m, map_term (extend v w) (map_term (extend u v) m) = map_term (extend u w) m.
Proof.
intros u v w Hle m.
rewrite -> map_term_compose.
f_equal.
fextensionality 1.
intro x.
symmetry.
apply extend_compose_up; auto.
Qed.  


Lemma extend_term_compose_down :
  forall u v w,
    w <<= v
    -> forall m, map_term (extend v w) (map_term (extend u v) m) = map_term (extend u w) m.
Proof.
intros u v w Hle m.
rewrite -> map_term_compose.
f_equal.
fextensionality 1.
intro x.
symmetry.
apply extend_compose_down; auto.
Qed.  


Lemma extend_sub_compose_up :
  forall u v w,
    u <<= v
    -> forall s, map_sub (extend v w) (map_sub (extend u v) s) = map_sub (extend u w) s.
Proof.
intros u v w Hle m.
rewrite -> map_sub_compose.
f_equal.
fextensionality 1.
intro x.
symmetry.
apply extend_compose_up; auto.
Qed.


Lemma extend_sub_compose_down :
  forall u v w,
    w <<= v
    -> forall s, map_sub (extend v w) (map_sub (extend u v) s) = map_sub (extend u w) s.
Proof.
intros u v w Hle m.
rewrite -> map_sub_compose.
f_equal.
fextensionality 1.
intro x.
symmetry.
apply extend_compose_down; auto.
Qed.


Lemma extend_term_cancel :
  forall v w,
    v <<= w
    -> forall m, map_term (extend w v) (map_term (extend v w) m) = m.
Proof.
intros v w H m.
rewrite -> extend_term_compose_up; auto.
apply extend_term_id.
Qed.


Lemma extend_sub_cancel :
  forall v w,
    v <<= w
    -> forall s, map_sub (extend w v) (map_sub (extend v w) s) = s.
Proof.
intros v w H m.
rewrite -> extend_sub_compose_up; auto.
apply extend_sub_id.
Qed.


Lemma extend_uniform :
  forall v w (R : wurel v),
    uniform (obj w)
      (fun i m p => rel R i (map_term (extend w v) m) (map_term (extend w v) p)).
Proof.
intros v w R.
do2 3 split.

(* closed *)
{
intros i m n Hrel.
so (urel_closed _#5 Hrel) as (Hcldm & Hcldn).
split; eapply map_hygiene_conv; eauto.
}

(* equiv *)
{
intros i m m' p p' Hclm Hclp Hm Hp Hrel.
eapply urel_equiv; eauto using map_equiv, map_hygiene.
}

(* zigzag *)
{
intros i m n p q Hmn Hpn Hpq.
eapply urel_zigzag; eauto.
}

(* downward *)
{
intros i m n Hrel.
apply urel_downward; auto.
}
Qed.


Definition extend_urel (v w : ordinal) (R : wurel v) : wurel w
  :=
  mk_urel
    (fun i m p => rel R i (map_term (extend w v) m) (map_term (extend w v) p))
    (extend_uniform _#3).


Lemma extend_urel_nonexpansive :
  forall v w, @nonexpansive (wurel_ofe v) (wurel_ofe w) (extend_urel v w).
Proof.
intros v w i R S HRS.
intros j Hj.
cbn.
fextensionality 2.
intros m p.
rewrite -> HRS; auto.
Qed.


Definition extend_urel_ne v w : wurel_ofe v -n> wurel_ofe w
  :=
  expair 
    (extend_urel v w)
    (extend_urel_nonexpansive v w).


Lemma extend_urel_inv :
  forall v w, v <<= w -> inverses (extend_urel w v) (extend_urel v w).
Proof.
intros v w Hle R.
apply urel_extensionality.
fextensionality 3.
intros i m p.
cbn.
rewrite -> !extend_term_cancel; auto.
Qed.


Lemma extend_urel_inj :
  forall v w, v <<= w -> injective (extend_urel v w).
Proof.
intros v w Hle.
eapply inverses_impl_injective; eauto using extend_urel_inv.
Qed.


Lemma extend_empty_urel :
  forall v w,
    v <<= w
    -> extend_urel v w empty_urel = empty_urel.
Proof.
intros v w Hvw.
apply urel_extensionality.
fextensionality 3.
intros i m p.
pextensionality; intro H; destruct H.
Qed.


Lemma extend_urelsp_rhs :
  forall v w,
    v <<= w
    -> forall (R : wurel v) (C : urelsp_car R),
         urelsp_car_rhs (extend_urel v w R)
         (fun i n => pi1 C i (map_term (extend w v) n)).
Proof.
intros v w Hvw R C.
destruct C as (P & i & m & p & Hmp & HP).
cbn.
exists i, (map_term (extend v w) m), (map_term (extend v w) p).
split.
  {
  cbn.
  rewrite -> !extend_term_cancel; auto.
  }
intros j n.
split.
  {
  intros Hdn.
  so (HP _ _ andel Hdn) as (Hji & Hdnp).
  split; auto.
  cbn.
  rewrite -> extend_term_cancel; auto.
  }

  {
  intros (Hji & Hnup).
  apply HP.
  split; auto.
  cbn in Hnup.
  rewrite -> extend_term_cancel in Hnup; auto.
  }
Qed.


Definition extend_urelsp {v w} (h : v <<= w) (R : wurel v) (C : car (urelsp R))
  : car (urelsp (extend_urel v w R))
  :=
  expair
    (fun i n => pi1 C i (map_term (extend w v) n))
    (extend_urelsp_rhs _ _ h R C).


Lemma extend_urelsp_nonexpansive :
  forall v w (h : v <<= w) (R : wurel v),
    nonexpansive (extend_urelsp h R).
Proof.
intros v w h R i C D Hdist.
intros j Hji.
fextensionality 1.
intros m.
cbn.
rewrite -> (Hdist j Hji).
reflexivity.
Qed.


Definition extend_urelsp_ne {v w} (h : v <<= w) (R : wurel v)
  : urelsp R -n> urelsp (extend_urel v w R)
  :=
  expair
    (extend_urelsp h R)
    (extend_urelsp_nonexpansive v w h R).


Lemma extend_urelsp_nonexpansive_dep :
  forall v w (h : v <<= w) n
    (C D : wurel v) (E : urelsp_car C) (F : urelsp_car D),
      urelsp_dist_dep C D n E F
      -> urelsp_dist_dep (extend_urel v w C) (extend_urel v w D) n 
           (extend_urelsp h C E) (extend_urelsp h D F).
Proof.
intros v w h n C D E F Hdist.
intros j Hj.
cbn.
fextensionality 1.
intros m.
rewrite -> (Hdist j Hj).
reflexivity.
Qed.


Lemma deextend_urelsp_rhs :
  forall v w (R : wurel v) (C : urelsp_car (extend_urel v w R)),
    v <<= w
    -> urelsp_car_rhs R (fun i n => pi1 C i (map_term (extend v w) n)).
Proof.
intros v w R C Hvw.
destruct C as (P & i & m & p & Hmp & HP).
cbn.
exists i, (map_term (extend w v) m), (map_term (extend w v) p).
cbn in Hmp.
split; auto.
intros j n.
split.
  {
  intros Hun.
  so (HP _ _ andel Hun) as (Hji & Hndp).
  cbn in Hndp.
  rewrite -> extend_term_cancel in Hndp; auto.
  }

  {
  intros (Hji & Hndp).
  apply HP.
  split; auto.
  cbn.
  rewrite -> extend_term_cancel; auto.
  }
Qed.


Definition deextend_urelsp {v w : ordinal} (h : v <<= w) (R : wurel v) (C : urelsp_car (extend_urel v w R))
  : urelsp_car R
  :=
  expair (fun i n => pi1 C i (map_term (extend v w) n))
    (deextend_urelsp_rhs _#4 h).


Lemma deextend_urelsp_nonexpansive :
  forall v w (h : v <<= w) (R : wurel v),
    @nonexpansive (urelsp (extend_urel v w R)) (urelsp R) (deextend_urelsp h R).
Proof.
intros v w h R i C D Hdist.
intros j Hji.
fextensionality 1.
intros m.
cbn.
exact (f_equal (fun z => z (map_term (extend v w) m)) (Hdist j Hji)).
Qed.


Definition deextend_urelsp_ne {v w : ordinal} (h : v <<= w) (R : wurel v) :
  urelsp (extend_urel v w R) -n> urelsp R
  :=
  expair
    (deextend_urelsp h R)
    (deextend_urelsp_nonexpansive _ _ h R).


Lemma deextend_urelsp_nonexpansive_dep :
  forall v w (h : v <<= w) n
    (C D : wurel v) (E : urelsp_car (extend_urel v w C)) (F : urelsp_car (extend_urel v w D)),
      urelsp_dist_dep (extend_urel v w C) (extend_urel v w D) n E F
      -> urelsp_dist_dep C D n (deextend_urelsp h C E) (deextend_urelsp h D F).
Proof.
intros v w h n C D E F Hdist.
intros j Hji.
fextensionality 1.
intros m.
cbn.
exact (f_equal (fun z => z (map_term (extend v w) m)) (Hdist j Hji)).
Qed.


Lemma deextend_urelsp_urelspinj :
  forall v w (h : v <<= w) (R : wurel v) i m p (Hmp : rel (extend_urel v w R) i m p),
    deextend_urelsp h R (urelspinj (extend_urel v w R) i m p Hmp)
    =
    urelspinj R i (map_term (extend w v) m) (map_term (extend w v) p) Hmp.
Proof.
intros v w h R i m p Hmp.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros j n.
rewrite -> map_term_inv; auto using extend_inv.
Qed.


Lemma extend_urelsp_inv :
  forall v w (h : v <<= w) (R : wurel v),
    inverses (deextend_urelsp h R) (extend_urelsp h R).
Proof.
intros v w h R C.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros i n.
rewrite -> extend_term_cancel; auto.
Qed.


Lemma extend_urelsp_inj :
  forall v w (h : v <<= w) (R : wurel v),
    injective (extend_urelsp h R).
Proof.
intros v w h R.
eapply inverses_impl_injective; eauto. 
apply extend_urelsp_inv.
Qed.


Definition extend_meta {v w} (h : v <<= w) (m : car (meta_ofe (obj v))) 
  : car (meta_ofe (obj w)).
Proof.
apply 
  (meta_nerect v (meta_ofe (obj w))
     (fun I => meta_nats I)
     (fun R a b => meta_fn (extend_urel v w R) (nearrow_compose b (deextend_urelsp_ne h R)))
     (fun _ x _ y => meta_pair x y)
     (fun _ x => meta_half x)
     (fun pg => meta_page pg)); eauto with meta_dist.

(* fn *)
{
intros i C D a b c d HCD Hab Hcd.
apply meta_dist_fn.
  {
  apply extend_urel_nonexpansive; auto.
  }

  {
  intros E F HEF.
  cbn.
  apply Hcd; auto.
  apply deextend_urelsp_nonexpansive_dep; auto.
  }
}

(* half *)
{
intros i p p' x x' Hp Hx.
apply meta_dist_half; auto.
}
Defined.


Lemma extend_meta_nonexpansive :
  forall v w (h : v <<= w),
    nonexpansive (extend_meta h).
Proof.
intros v w h.
unfold extend_meta.
apply meta_nerect_nonexpansive.
Qed.


Definition extend_meta_ne {v w} (h : v <<= w) 
  : meta_ofe (obj v) -n> meta_ofe (obj w)
  :=
  expair (extend_meta h) (extend_meta_nonexpansive v w h).


Definition extend_iurel {v w : ordinal} (h : v <<= w) (r : wiurel v) : wiurel w
  :=
  (extend_urel v w (fst r),
   extend_meta h (snd r)).


Lemma extend_iurel_nonexpansive :
  forall v w (h : v <<= w), @nonexpansive (wiurel_ofe v) (wiurel_ofe w) (extend_iurel h).
Proof.
intros v w h.
unfold extend_iurel.
intros i x y Hxy.
destruct Hxy.
split; cbn.
  {
  apply extend_urel_nonexpansive; auto.
  }

  {
  apply extend_meta_nonexpansive; auto.
  }
Qed.


Definition extend_iurel_ne {v w : ordinal} (h : v <<= w) :
  wiurel_ofe v -n> wiurel_ofe w
  :=
  expair (extend_iurel h) (extend_iurel_nonexpansive v w h).


Lemma den_extend_iurel :
  forall v w (h : v <<= w) A,
    den (extend_iurel h A) = extend_urel v w (den A).
Proof.
intros v w h A.
reflexivity.
Qed.


Lemma extend_meta_nats :
  forall v w (h : v <<= w) I,
    extend_meta h (meta_nats I) = meta_nats I.
Proof.
intros v w h I.
unfold extend_meta.
rewrite -> meta_nerect_nats.
reflexivity.
Qed.


Lemma extend_meta_fn :
  forall v w (h : v <<= w) R g,
    extend_meta h (meta_fn R g)
    =
    meta_fn (extend_urel v w R) 
      (nearrow_compose (nearrow_compose (extend_meta_ne h) g) (deextend_urelsp_ne h R)).
Proof.
intros v w h R g.
unfold extend_meta_ne.
unfold extend_meta.
rewrite -> meta_nerect_fn.
f_equal.
f_equal.
apply exT_extensionality_prop.
cbn.
reflexivity.
Qed.


Lemma extend_meta_term :
  forall v w (h : v <<= w) R C,
    extend_meta h (meta_term R C)
    =
    meta_term (extend_urel v w R) (extend_urelsp h R C).
Proof.
intros v w h R C.
unfold meta_term.
rewrite -> extend_meta_fn.
f_equal.
apply nearrow_extensionality.
intros x.
cbn.
rewrite -> extend_meta_nats.
f_equal.
so (urelsp_eta _ _ x) as (i & m & p & Hmp & ->).
rewrite -> deextend_urelsp_urelspinj.
apply exT_extensionality_prop.
fextensionality 1.
intro j.
cbn.
unfold urelsp_sim_pred.
cbn.
pextensionality.
  {
  intros (n & HCn & Hj & Hnp).
  exists (map_term (extend v w) n).
  rewrite -> extend_term_cancel; auto.
  }

  {
  intros (n & HCn & Hj & Hnp).
  exists (map_term (extend w v) n).
  auto.
  }
Qed.


Lemma extend_meta_pair :
  forall v w (h : v <<= w) m n,
    extend_meta h (meta_pair m n)
    =
    meta_pair (extend_meta h m) (extend_meta h n).
Proof.
intros v w h m n.
unfold extend_meta.
rewrite -> meta_nerect_pair.
reflexivity.
Qed.


Lemma extend_meta_half :
  forall v w (h : v <<= w) m,
    extend_meta h (meta_half m)
    =
    meta_half (extend_meta h m).
Proof.
intros v w h m.
unfold extend_meta.
rewrite -> meta_nerect_half.
reflexivity.
Qed.


Lemma extend_meta_page :
  forall v w (h : v <<= w) pg,
    extend_meta h (meta_page pg)
    =
    meta_page pg.
Proof.
intros v w h pg.
unfold extend_meta.
rewrite -> meta_nerect_page.
reflexivity.
Qed.


Lemma extend_meta_null :
  forall v w (h : v <<= w),
    extend_meta h meta_null = meta_null.
Proof.
intros v w h.
unfold meta_null.
apply extend_meta_nats.
Qed.


Lemma extend_meta_urel :
  forall v w (h : v <<= w) R,
    extend_meta h (meta_urel R) = meta_urel (extend_urel v w R).
Proof.
intros v w h R.
unfold meta_urel.
rewrite -> extend_meta_fn.
f_equal.
apply exT_extensionality_prop.
cbn.
fextensionality 1.
intros _.
rewrite -> extend_meta_null.
reflexivity.
Qed.


Lemma extend_meta_iurel :
  forall v w (h : v <<= w) R,
    extend_meta h (meta_iurel R)
    =
    meta_iurel (extend_iurel h R).
Proof.
intros v w h R.
unfold meta_iurel.
cbn.
rewrite -> extend_meta_pair.
rewrite -> extend_meta_urel.
reflexivity.
Qed.


Hint Rewrite extend_meta_nats extend_meta_fn extend_meta_term extend_meta_pair extend_meta_half extend_meta_page extend_meta_null extend_meta_urel extend_meta_iurel : extend_meta.


Ltac meta_discriminate Heq :=
  let H := fresh
  in
    so (f_equal (meta_rect _ (fun _ => nat) (fun _ => 0) (fun _ _ _ => 2) (fun _ _ _ _ => 4) (fun _ _ => 5) (fun _ => 6)) Heq) as H;
    autorewrite with meta_rect in H;
    cbn in H;
    discriminate Heq.


Lemma extend_meta_inj :
  forall v w (h : v <<= w),
    injective (extend_meta h).
Proof.
intros v w h.
intros m n Heq.
revert n Heq.
pattern m.
apply meta_rect.

(* nats *)
{
intros I n Heq.
revert Heq.
pattern n.
apply meta_rect;
try (intros;
     autorewrite with extend_meta in Heq;
     meta_discriminate Heq).
intros J Heq.
f_equal.
rewrite -> !extend_meta_nats in Heq.
eapply meta_nats_inj; eauto.
}

(* fn *)
{
intros R g IH n Heq.
revert Heq.
pattern n.
apply meta_rect;
try (intros;
     autorewrite with extend_meta in Heq;
     meta_discriminate Heq).
intros R' g' _ Heq.
rewrite -> !extend_meta_fn in Heq.
so (meta_fn_inj _#5 Heq) as Heq'.
so (extend_urel_inj _ _ h _ _ (eq_dep_impl_eq_fst _#6 Heq')).
subst R'.
f_equal.
so (eq_dep_impl_eq_snd _#5 Heq') as Heqg.
clear Heq Heq'.
apply exT_extensionality_prop.
fextensionality 1.
intro C.
so (f_equal (fun z => pi1 z (extend_urelsp h R C)) Heqg) as Heq.
cbn in Heq.
rewrite -> extend_urelsp_inv in Heq.
cbn in Heq.
exact (IH C (pi1 g' C) Heq).
}

(* pair *)
{
intros x IH1 y IH2 n Heq.
revert Heq.
pattern n.
apply meta_rect;
try (intros;
     autorewrite with extend_meta in Heq;
     meta_discriminate Heq).
intros x' _ y' _ Heq.
rewrite -> !extend_meta_pair in Heq.
so (meta_pair_inj _#5 Heq) as (Heq1 & Heq2).
f_equal; eauto.
}

(* half *)
{
intros x IH n Heq.
revert Heq.
pattern n.
apply meta_rect;
try (intros;
     autorewrite with extend_meta in Heq;
     meta_discriminate Heq).
intros x' _ Heq.
rewrite -> !extend_meta_half in Heq.
so (meta_half_inj _#3 Heq) as Heq'.
f_equal; auto.
}

(* page *)
{
intros pg n Heq.
revert Heq.
pattern n.
apply meta_rect;
try (intros;
     autorewrite with extend_meta in Heq;
     meta_discriminate Heq).
intros pg' Heq.
rewrite -> !extend_meta_page in Heq.
so (meta_page_inj _#3 Heq) as Heq'.
f_equal; auto.
}
Qed.


Lemma extend_iurel_inj :
  forall v w (h : v <<= w), injective (extend_iurel h).
Proof.
intros v w h.
intros r s Heq.
so (f_equal fst Heq) as Heq1.
so (f_equal snd Heq) as Heq2.
cbn in Heq1, Heq2.
apply prod_extensionality.
  {
  eapply extend_urel_inj; eauto.
  }

  {
  eapply (extend_meta_inj _ _ h); eauto.
  }
Qed.


Lemma extend_iubase :
  forall v w (h : v <<= w) R,
    extend_iurel h (iubase R)
    =
    iubase (extend_urel v w R).
Proof.
intros v w h R.
unfold iubase.
unfold extend_iurel, extend_urel, extend_iurel.
cbn.
rewrite -> extend_meta_null.
reflexivity.
Qed.


Lemma urel_updown :
  forall v w (A : wurel v) i m p,
    v <<= w
    -> rel A i m p
    -> rel (extend_urel v w A) i (map_term (extend v w) m) (map_term (extend v w) p).
Proof.
intros v w A i m p Hvw H.
cbn.
rewrite -> !extend_term_cancel; auto.
Qed.    


Lemma extend_urel_compose_up :
  forall u v w,
    u <<= v
    -> forall R, extend_urel u w R = extend_urel v w (extend_urel u v R).
Proof.
intros u v w Hle R.
apply urel_extensionality.
unfold extend_urel.
cbn.
fextensionality 3.
intros i m p.
rewrite -> !extend_term_compose_down; auto.
Qed.


Lemma extend_urelspinj :
  forall v w (h : v <<= w) (A : wurel v) i m p Hmp Hmp',
    extend_urelsp h A (urelspinj A i m p Hmp)
    =
    urelspinj (extend_urel v w A) i (map_term (extend v w) m) (map_term (extend v w) p) Hmp'.
Proof.
intros v w h A i m p Hmp Hmp'.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros j n.
pextensionality.
  {
  intros (Hj & Hrel).
  split; auto.
  rewrite -> extend_term_cancel; auto.
  }

  {
  intros (Hj & Hrel).
  split; auto.
  rewrite -> extend_term_cancel in Hrel; auto.
  }
Qed.


Lemma urelsp_index_extend :
  forall v w A (C : urelsp_car A) (h : v <<= w),
    urelsp_index (extend_urel v w A) (extend_urelsp h A C) = urelsp_index A C.
Proof.
intros v w A C h.
so (urelsp_eta _ _ C) as (i & m & p & Hmp & ->).
assert (rel (extend_urel v w A) i (map_term (extend v w) m) (map_term (extend v w) p)) as Hmp'.
  {
  cbn.
  rewrite -> !extend_term_cancel; auto.
  }
rewrite -> (extend_urelspinj _#8 Hmp').
rewrite -> !urelsp_index_inj.
reflexivity.
Qed.


Lemma extend_meta_compose :
  forall u v w (huv : u <<= v) (hvw : v <<= w) (huw : u <<= w) m,
    extend_meta huw m = extend_meta hvw (extend_meta huv m).
Proof.
intros u v w huv hvw huw m.
pattern m.
apply meta_rect; clear m.

(* nats *)
{
intro I.
rewrite -> !extend_meta_nats.
reflexivity.
}

(* fn *)
{
intros R f IH.
rewrite -> !extend_meta_fn.
assert (forall R R' (f : urelsp R -n> meta_ofe (obj w)) (f' : urelsp R' -n> meta_ofe (obj w)),
          eq_dep _ (fun R => urelsp R -n> meta_ofe (obj w)) R f R' f'
          -> meta_fn R f = meta_fn R' f') as H.
  {
  clear_all.
  intros R R' f f' H.
  injectionT H.
  intros <-.
  injectionT H.
  intros <-.
  reflexivity.
  }
apply H; clear H.
apply exT_extensionality_prop_eq_dep.
cbn.
apply functional_extensionality_eq_dep_dom.
  {
  apply extend_urel_compose_up; auto.
  }
intros C D Heq.
rewrite <- IH.
f_equal.
f_equal.
apply exT_extensionality_prop.
cbn.
fextensionality 2.
intros i n.
rewrite -> extend_term_compose_up; auto.
so (eq_dep_impl_eq_snd_free _#6 (eq_dep_pi1 _#7 Heq)) as Heq'.
exact (f_equal (fun z => z i (map_term (extend u w) n)) Heq').
}

(* pair *)
{
intros m IH1 n IH2.
rewrite -> !extend_meta_pair.
f_equal; auto.
}

(* half *)
{
intros m IH.
rewrite -> !extend_meta_half.
f_equal; auto.
}

(* page *)
{
intros pg.
rewrite -> !extend_meta_page.
reflexivity.
}
Qed.


Lemma extend_iurel_compose :
  forall u v w (h : u <<= v) (h' : v <<= w) R,
    extend_iurel (le_ord_trans _#3 h h') R = extend_iurel h' (extend_iurel h R).
Proof.
intros u v w h h' R.
unfold extend_iurel.
cbn.
f_equal.
  {
  apply (extend_urel_compose_up _#3 h).
  }

  {
  apply (extend_meta_compose u v w h h'(le_ord_trans _#3 h h')).
  }
Qed.


Lemma extend_urel_id :
  forall w R,
    extend_urel w w R = R.
Proof.
intros w R.
apply urel_extensionality.
unfold extend_urel.
cbn.
fextensionality 3.
intros i m p.
rewrite -> !extend_term_id; auto.
Qed.


Lemma deextend_urelsp_id :
  forall w (h : w <<= w) (R : wurel w) C,
    deextend_urelsp h R (transport (eqsymm (extend_urel_id w R)) urelsp_car C) = C.
Proof.
intros w h R C.
apply exT_extensionality_prop.
fextensionality 2.
intros i n.
cbn.
rewrite -> (pi1_transport_lift _ _ (fun z D => urelsp_car_rhs z D) _ _ (eqsymm (extend_urel_id w R))).
rewrite -> extend_term_id.
reflexivity.
Qed.


Lemma extend_meta_id :
  forall w (h : w <<= w) m,
    extend_meta h m = m.
Proof.
intros w h m.
pattern m.
apply meta_rect.

(* nats *)
{
intros I.
rewrite -> extend_meta_nats.
reflexivity.
}

(* fn *)
{
intros R f IH.
rewrite -> extend_meta_fn.
apply meta_fn_extensionality.
apply (eq_impl_eq_dep _#6 (extend_urel_id _ _)).
apply exT_extensionality_prop.
unfold nearrow.
rewrite -> (pi1_transport_dep_lift _ _ (fun z g => @nonexpansive (urelsp z) (meta_ofe (obj w)) g) _ _ (extend_urel_id w R)).
cbn.
fextensionality 1.
intro C.
rewrite -> app_transport_dom.
rewrite -> IH.
f_equal.
apply deextend_urelsp_id.
}

(* pair *)
{
intros x IH1 y IH2.
rewrite -> extend_meta_pair.
f_equal; auto.
}

(* half *)
{
intros x IH.
rewrite -> extend_meta_half.
f_equal; auto.
}

(* page *)
{
intro pg.
rewrite -> extend_meta_page.
reflexivity.
}
Qed.


Lemma extend_iurel_id :
  forall w (h : w <<= w) R,
    extend_iurel h R = R.
Proof.
intros w h R.
destruct R as (R, m).
unfold extend_iurel.
f_equal; auto using extend_urel_id, extend_meta_id.
Qed.
