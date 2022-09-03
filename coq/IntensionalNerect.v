
Require Import Axioms.
Require Import Tactics.
Require Import Sigma.
Require Import Equality.
Require Import Ofe.
Require Import Spaces.
Require Import Syntax.
Require Import Uniform.
Require Import Urelsp.
Require Import Intensional.
Require Import Possible.
Require Import Ordinal.
Require Import Candidate.
Require Import Page.


Section level.


Arguments urel {object}.
Arguments urel_ofe {object}.
Arguments meta {object}.
Arguments meta_ofe {object}.
Arguments iurel {object}.
Arguments iurel_ofe {object}.


Variable cur : ordinal.


Local Lemma meta_nerect_poss :
  forall (C : ofe)
    (f_nats   : car nats_ofe -> car C)
    (f_fn     : forall (R : car (wurel_ofe cur)),
                  (urelsp R -n> @meta_ofe (obj cur))
                  -> (urelsp R -n> C)
                  -> car C)
    (f_pair   : car (@meta_ofe (obj cur)) -> car C -> car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_half   : car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_page   : page -> car C),
      @meta (obj cur) -> poss (car C).
Proof.
intros C f_nats f_fn f_pair f_half f_page m.
refine (meta_rect _ (fun _ => poss (car C)) _ _ _ _ _ m); clear m.

(* nats *)
{
intros I.
exact (poss_unit (f_nats I)).
}

(* fn *)
{
intros R f ih.
change (car (urelsp R) -> poss (car C)) in ih.
refine (poss_bind (poss_lift ih) _).
intros ih'.
refine (poss_assume (nonexpansive ih') _).
intro Hne.
exact (poss_unit (f_fn R f (expair ih' Hne))).
}

(* pair *)
{
intros m x n y.
refine (poss_bind x _).
intro x'.
refine (poss_bind y _).
intro y'.
exact (poss_unit (f_pair m x' n y')).
}

(* half *)
{
intros m x.
refine (poss_bind x _).
intro x'.
exact (poss_unit (f_half m x')).
}

(* page *)
{
intros pg.
exact (poss_unit (f_page pg)).
}
Defined.


Local Lemma meta_nerect_poss_fn :
  forall (C : ofe)
    (f_nats   : car nats_ofe -> car C)
    (f_fn     : forall (R : car (wurel_ofe cur)),
                  (urelsp R -n> @meta_ofe (obj cur))
                  -> (urelsp R -n> C)
                  -> car C)
    (f_pair   : car (@meta_ofe (obj cur)) -> car C -> car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_half   : car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_page   : page -> car C)
    (R : wurel cur) (f : urelsp R -n> meta_ofe),
      meta_nerect_poss C f_nats f_fn f_pair f_half f_page (meta_fn R f)
      =
      poss_bind (poss_lift (fun D => meta_nerect_poss C f_nats f_fn f_pair f_half f_page (pi1 f D)))
        (fun ih =>
           poss_assume (nonexpansive ih)
           (fun Hne =>
              poss_unit (f_fn R f (expair ih Hne)))).
Proof.
intros C f_nats f_fn f_pair f_half f_page R f.
unfold meta_nerect_poss.
rewrite -> meta_rect_fn.
reflexivity.
Qed.


Local Lemma meta_nerect_poss_nonexpansive :
  forall (C : ofe)
    (f_nats   : car nats_ofe -> car C)
    (f_fn     : forall (R : car (wurel_ofe cur)),
                  (urelsp R -n> @meta_ofe (obj cur))
                  -> (urelsp R -n> C)
                  -> car C)
    (f_pair   : car (@meta_ofe (obj cur)) -> car C -> car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_half   : car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_page   : page -> car C),
      (forall n I J, dist n I J -> dist n (f_nats I) (f_nats J))
      -> (forall n 
            (A B : car urel_ofe) 
            (e : car (nearrow_ofe (urelsp A) meta_ofe))
            (f : car (nearrow_ofe (urelsp B) meta_ofe))
            g h,
              dist n A B
              -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n e f
              -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n g h
              -> dist n (f_fn A e g) (f_fn B f h))
      -> (forall n (p p' q q' : car meta_ofe) (x x' y y' : car C),
              dist n p p'
              -> dist n q q'
              -> dist n x x'
              -> dist n y y'
              -> dist n (f_pair p x q y) (f_pair p' x' q' y'))
      -> (forall n (p p' : car meta_ofe) (x x' : car C),
            dist n p p'
            -> dist n x x'
            -> dist (S n) (f_half p x) (f_half p' x'))
      -> forall n (m m' : car meta_ofe),
           dist n m m'
           -> poss_dist n
                (meta_nerect_poss C f_nats f_fn f_pair f_half f_page m)
                (meta_nerect_poss C f_nats f_fn f_pair f_half f_page m').
Proof.
intro C.
intros f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half n m m' Hdist.
revert n m' Hdist.
pattern m.
apply meta_rect.

(* nats *)
{
intros I n mm Hdist.
apply poss_dist_if_pos.
intro Hpos.
so (meta_dist_nats_invert _#4 Hpos Hdist) as (J & -> & Hdist').
unfold meta_nerect_poss.
rewrite -> !meta_rect_nats.
apply poss_dist_unit.
apply Hne_nats; auto.
}

(* fn *)
{
intros A f IH n mm Hdist.
apply poss_dist_if_pos.
intros Hpos.
so (meta_dist_fn_invert _#5 Hpos Hdist) as (B & g & -> & HAB & Hfg).
set (X := meta_nerect_poss C f_nats f_fn f_pair f_half f_page (meta_fn A f)).
set (Y := meta_nerect_poss C f_nats f_fn f_pair f_half f_page (meta_fn B g)).
revert X Y.
rewrite -> !meta_nerect_poss_fn .
intros X Y.
subst X Y.
intros p p'.
apply Hne_fn; auto.
  {
  clear p p'.
  split; auto.
  intros i a b Hi Hab.
  so (meta_dist_fn_invert' _#6 (dist_downward_leq _#5 Hi Hdist)) as (_ & Hfg').
  apply Hfg'; auto.
  }

  {
  split; auto.
  intros i a b Hi Hab.
  cbn.
  apply IH.
  clear p p'.
  so (meta_dist_fn_invert' _#6 (dist_downward_leq _#5 Hi Hdist)) as (_ & Hfg').
  apply Hfg'; auto.
  }
}

(* pair *)
{
intros a IH1 b IH2 n mm Hdist.
apply poss_dist_if_pos.
intro Hpos.
so (meta_dist_pair_invert _#5 Hpos Hdist) as (c & d & -> & Hac & Hbd).
unfold meta_nerect_poss.
rewrite -> !meta_rect_pair.
apply (poss_dist_bind _ _ n).
  {
  apply IH1; auto.
  }
intros a' c' Hac'.
apply (poss_dist_bind _ _ n).
  {
  apply IH2; auto.
  }
intros b' d' Hbd'.
apply poss_dist_unit.
apply Hne_pair; auto.
}

(* half *)
{
intros a IH n mm Hdist.
apply poss_dist_if_pos.
intro Hpos.
so (meta_dist_half_invert _#4 Hpos Hdist) as (b & -> & Hab).
unfold meta_nerect_poss.
rewrite -> !meta_rect_half.
apply (poss_dist_bind _ _ (pred n)).
  {
  apply IH; auto.
  }
intros a' c' Hac'.
apply poss_dist_unit.
destruct n as [| n].
  {
  apply dist_zero.
  }
apply Hne_half; auto.
}

(* page *)
{
intros pg n mm Hdist.
apply poss_dist_if_pos.
intro Hpos.
so (meta_dist_page_invert _#4 Hpos Hdist); subst mm.
unfold meta_nerect_poss.
rewrite -> !meta_rect_page.
apply poss_dist_unit.
apply dist_refl.
}
Qed.


Local Lemma meta_nerect_poss_true :
  forall (C : ofe)
    (f_nats   : car nats_ofe -> car C)
    (f_fn     : forall (R : car (wurel_ofe cur)),
                  (urelsp R -n> @meta_ofe (obj cur))
                  -> (urelsp R -n> C)
                  -> car C)
    (f_pair   : car (@meta_ofe (obj cur)) -> car C -> car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_half   : car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_page   : page -> car C),
      (forall n I J, dist n I J -> dist n (f_nats I) (f_nats J))
      -> (forall n 
            (A B : car urel_ofe) 
            (e : car (nearrow_ofe (urelsp A) meta_ofe))
            (f : car (nearrow_ofe (urelsp B) meta_ofe))
            g h,
              dist n A B
              -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n e f
              -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n g h
              -> dist n (f_fn A e g) (f_fn B f h))
      -> (forall n (p p' q q' : car meta_ofe) (x x' y y' : car C),
              dist n p p'
              -> dist n q q'
              -> dist n x x'
              -> dist n y y'
              -> dist n (f_pair p x q y) (f_pair p' x' q' y'))
      -> (forall n (p p' : car meta_ofe) (x x' : car C),
            dist n p p'
            -> dist n x x'
            -> dist (S n) (f_half p x) (f_half p' x'))
      -> forall (m : meta),
           pi1 (meta_nerect_poss C f_nats f_fn f_pair f_half f_page m).
Proof.
intros C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half m.
pattern m.
apply meta_rect.

(* nats *)
{
intros I.
unfold meta_nerect_poss.
rewrite -> meta_rect_nats.
cbn.
trivial.
}

(* fn *)
{
intros R f IH.
rewrite -> meta_nerect_poss_fn.
apply (poss_bind_true _#4 (poss_lift_true _#3 IH)).
eapply poss_assume_true.
Unshelve.
2:{
  intros n s t Hst.
  cbn.
  unfold poss_lift_true.
  apply meta_nerect_poss_nonexpansive; auto.
  exact (pi2 f n s t Hst).
  }
cbn.
trivial.
}

(* pair *)
{
intros x IH1 y IH2.
unfold meta_nerect_poss.
rewrite -> !meta_rect_pair.
apply (poss_bind_true _#4 IH1).
apply (poss_bind_true _#4 IH2).
cbn.
trivial.
}

(* half *)
{
intros x IH.
unfold meta_nerect_poss.
rewrite -> !meta_rect_half.
apply (poss_bind_true _#4 IH).
cbn.
trivial.
}

(* page *)
{
intros pg.
unfold meta_nerect_poss.
rewrite -> !meta_rect_page.
cbn.
trivial.
}
Qed.


Lemma meta_nerect :
  forall (C : ofe)
    (f_nats   : car nats_ofe -> car C)
    (f_fn     : forall (R : car (wurel_ofe cur)),
                  (urelsp R -n> @meta_ofe (obj cur))
                  -> (urelsp R -n> C)
                  -> car C)
    (f_pair   : car (@meta_ofe (obj cur)) -> car C -> car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_half   : car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_page   : page -> car C),
      (forall n I J, dist n I J -> dist n (f_nats I) (f_nats J))
      -> (forall n 
            (A B : car urel_ofe) 
            (e : car (nearrow_ofe (urelsp A) meta_ofe))
            (f : car (nearrow_ofe (urelsp B) meta_ofe))
            (g : car (nearrow_ofe (urelsp A) C))
            (h : car (nearrow_ofe (urelsp B) C)),
              dist n A B
              -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n e f
              -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n g h
              -> dist n (f_fn A e g) (f_fn B f h))
      -> (forall n (p p' q q' : car meta_ofe) (x x' y y' : car C),
              dist n p p'
              -> dist n q q'
              -> dist n x x'
              -> dist n y y'
              -> dist n (f_pair p x q y) (f_pair p' x' q' y'))
      -> (forall n (p p' : car meta_ofe) (x x' : car C),
            dist n p p'
            -> dist n x x'
            -> dist (S n) (f_half p x) (f_half p' x'))
      -> car (@meta_ofe (obj cur)) -> car C.
Proof.
intros C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half.
exact (fun m => pi2 (meta_nerect_poss C f_nats f_fn f_pair f_half f_page m) (meta_nerect_poss_true C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half m)).
Defined.


Lemma meta_nerect_nonexpansive :
  forall (C : ofe)
    (f_nats   : car nats_ofe -> car C)
    (f_fn     : forall (R : car (wurel_ofe cur)),
                  (urelsp R -n> @meta_ofe (obj cur))
                  -> (urelsp R -n> C)
                  -> car C)
    (f_pair   : car (@meta_ofe (obj cur)) -> car C -> car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_half   : car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_page   : page -> car C)
    (Hne_nats : forall n I J, dist n I J -> dist n (f_nats I) (f_nats J))
    (Hne_fn : forall n 
                (A B : car urel_ofe) 
                (e : car (nearrow_ofe (urelsp A) meta_ofe))
                (f : car (nearrow_ofe (urelsp B) meta_ofe))
                (g : car (nearrow_ofe (urelsp A) C))
                (h : car (nearrow_ofe (urelsp B) C)),
                  dist n A B
                  -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n e f
                  -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n g h
                  -> dist n (f_fn A e g) (f_fn B f h))
    (Hne_pair : forall n (p p' q q' : car meta_ofe) (x x' y y' : car C),
                    dist n p p'
                    -> dist n q q'
                    -> dist n x x'
                    -> dist n y y'
                    -> dist n (f_pair p x q y) (f_pair p' x' q' y'))
    (Hne_half : forall n (p p' : car meta_ofe) (x x' : car C),
                  dist n p p'
                  -> dist n x x'
                  -> dist (S n) (f_half p x) (f_half p' x')),
      nonexpansive (meta_nerect C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half).
Proof.
intros C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half.
intros n m m' Hdist.
unfold meta_nerect.
apply meta_nerect_poss_nonexpansive; auto.
Qed.


Lemma meta_nerect_ne :
  forall (C : ofe)
    (f_nats   : car nats_ofe -> car C)
    (f_fn     : forall (R : car (wurel_ofe cur)),
                  (urelsp R -n> @meta_ofe (obj cur))
                  -> (urelsp R -n> C)
                  -> car C)
    (f_pair   : car (@meta_ofe (obj cur)) -> car C -> car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_half   : car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_page   : page -> car C),
      (forall n I J, dist n I J -> dist n (f_nats I) (f_nats J))
      -> (forall n 
            (A B : car urel_ofe) 
            (e : car (nearrow_ofe (urelsp A) meta_ofe))
            (f : car (nearrow_ofe (urelsp B) meta_ofe))
            (g : car (nearrow_ofe (urelsp A) C))
            (h : car (nearrow_ofe (urelsp B) C)),
              dist n A B
              -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n e f
              -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n g h
              -> dist n (f_fn A e g) (f_fn B f h))
      -> (forall n (p p' q q' : car meta_ofe) (x x' y y' : car C),
              dist n p p'
              -> dist n q q'
              -> dist n x x'
              -> dist n y y'
              -> dist n (f_pair p x q y) (f_pair p' x' q' y'))
      -> (forall n (p p' : car meta_ofe) (x x' : car C),
            dist n p p'
            -> dist n x x'
            -> dist (S n) (f_half p x) (f_half p' x'))
      -> @meta_ofe (obj cur) -n> C.
Proof.
intros C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half.
exists (meta_nerect C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half).
apply meta_nerect_nonexpansive.
Defined.


Lemma meta_nerect_nats :
  forall (C : ofe)
    (f_nats   : car nats_ofe -> car C)
    (f_fn     : forall (R : car (wurel_ofe cur)),
                  (urelsp R -n> @meta_ofe (obj cur))
                  -> (urelsp R -n> C)
                  -> car C)
    (f_pair   : car (@meta_ofe (obj cur)) -> car C -> car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_half   : car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_page   : page -> car C)
    (Hne_nats : forall n I J, dist n I J -> dist n (f_nats I) (f_nats J))
    (Hne_fn : forall n 
                (A B : car urel_ofe) 
                (e : car (nearrow_ofe (urelsp A) meta_ofe))
                (f : car (nearrow_ofe (urelsp B) meta_ofe))
                (g : car (nearrow_ofe (urelsp A) C))
                (h : car (nearrow_ofe (urelsp B) C)),
                  dist n A B
                  -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n e f
                  -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n g h
                  -> dist n (f_fn A e g) (f_fn B f h))
    (Hne_pair : forall n (p p' q q' : car meta_ofe) (x x' y y' : car C),
                    dist n p p'
                    -> dist n q q'
                    -> dist n x x'
                    -> dist n y y'
                    -> dist n (f_pair p x q y) (f_pair p' x' q' y'))
    (Hne_half : forall n (p p' : car meta_ofe) (x x' : car C),
                  dist n p p'
                  -> dist n x x'
                  -> dist (S n) (f_half p x) (f_half p' x'))
    I,
      meta_nerect C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half (meta_nats I)
      =
      f_nats I.
Proof.
intros C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half I.
unfold meta_nerect.
generalize (meta_nerect_poss_true C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half (meta_nats I)).
unfold meta_nerect_poss.
rewrite -> meta_rect_nats.
intro p.
cbn.
reflexivity.
Qed.


Lemma meta_nerect_fn :
  forall (C : ofe)
    (f_nats   : car nats_ofe -> car C)
    (f_fn     : forall (R : car (wurel_ofe cur)),
                  (urelsp R -n> @meta_ofe (obj cur))
                  -> (urelsp R -n> C)
                  -> car C)
    (f_pair   : car (@meta_ofe (obj cur)) -> car C -> car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_half   : car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_page   : page -> car C)
    (Hne_nats : forall n I J, dist n I J -> dist n (f_nats I) (f_nats J))
    (Hne_fn : forall n 
                (A B : car urel_ofe) 
                (e : car (nearrow_ofe (urelsp A) meta_ofe))
                (f : car (nearrow_ofe (urelsp B) meta_ofe))
                (g : car (nearrow_ofe (urelsp A) C))
                (h : car (nearrow_ofe (urelsp B) C)),
                  dist n A B
                  -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n e f
                  -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n g h
                  -> dist n (f_fn A e g) (f_fn B f h))
    (Hne_pair : forall n (p p' q q' : car meta_ofe) (x x' y y' : car C),
                    dist n p p'
                    -> dist n q q'
                    -> dist n x x'
                    -> dist n y y'
                    -> dist n (f_pair p x q y) (f_pair p' x' q' y'))
    (Hne_half : forall n (p p' : car meta_ofe) (x x' : car C),
                  dist n p p'
                  -> dist n x x'
                  -> dist (S n) (f_half p x) (f_half p' x'))
    R f,
      meta_nerect C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half (meta_fn R f)
      =
      f_fn R f
        (nearrow_compose
           (meta_nerect_ne C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half)
           f).
Proof.
intros C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half R f.
unfold meta_nerect.
generalize (meta_nerect_poss_true C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half (meta_fn R f)).
rewrite -> meta_nerect_poss_fn.
intro p.
cbn.
f_equal.
apply exT_extensionality_prop.
cbn.
fextensionality 1.
intro D.
unfold meta_nerect.
f_equal.
apply proof_irrelevance.
Qed.


Lemma meta_nerect_pair :
  forall (C : ofe)
    (f_nats   : car nats_ofe -> car C)
    (f_fn     : forall (R : car (wurel_ofe cur)),
                  (urelsp R -n> @meta_ofe (obj cur))
                  -> (urelsp R -n> C)
                  -> car C)
    (f_pair   : car (@meta_ofe (obj cur)) -> car C -> car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_half   : car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_page   : page -> car C)
    (Hne_nats : forall n I J, dist n I J -> dist n (f_nats I) (f_nats J))
    (Hne_fn : forall n 
                (A B : car urel_ofe) 
                (e : car (nearrow_ofe (urelsp A) meta_ofe))
                (f : car (nearrow_ofe (urelsp B) meta_ofe))
                (g : car (nearrow_ofe (urelsp A) C))
                (h : car (nearrow_ofe (urelsp B) C)),
                  dist n A B
                  -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n e f
                  -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n g h
                  -> dist n (f_fn A e g) (f_fn B f h))
    (Hne_pair : forall n (p p' q q' : car meta_ofe) (x x' y y' : car C),
                    dist n p p'
                    -> dist n q q'
                    -> dist n x x'
                    -> dist n y y'
                    -> dist n (f_pair p x q y) (f_pair p' x' q' y'))
    (Hne_half : forall n (p p' : car meta_ofe) (x x' : car C),
                  dist n p p'
                  -> dist n x x'
                  -> dist (S n) (f_half p x) (f_half p' x'))
    m n,
      meta_nerect C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half (meta_pair m n)
      =
      f_pair
        m (meta_nerect C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half m)
        n (meta_nerect C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half n).
Proof.
intros C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half m n.
unfold meta_nerect.
generalize (meta_nerect_poss_true C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half (meta_pair m n)).
unfold meta_nerect_poss.
rewrite -> meta_rect_pair.
intro p.
cbn.
f_equal.
  {
  f_equal.
  apply proof_irrelevance.
  }

  {
  f_equal.
  apply proof_irrelevance.
  }
Qed.


Lemma meta_nerect_half :
  forall (C : ofe)
    (f_nats   : car nats_ofe -> car C)
    (f_fn     : forall (R : car (wurel_ofe cur)),
                  (urelsp R -n> @meta_ofe (obj cur))
                  -> (urelsp R -n> C)
                  -> car C)
    (f_pair   : car (@meta_ofe (obj cur)) -> car C -> car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_half   : car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_page   : page -> car C)
    (Hne_nats : forall n I J, dist n I J -> dist n (f_nats I) (f_nats J))
    (Hne_fn : forall n 
                (A B : car urel_ofe) 
                (e : car (nearrow_ofe (urelsp A) meta_ofe))
                (f : car (nearrow_ofe (urelsp B) meta_ofe))
                (g : car (nearrow_ofe (urelsp A) C))
                (h : car (nearrow_ofe (urelsp B) C)),
                  dist n A B
                  -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n e f
                  -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n g h
                  -> dist n (f_fn A e g) (f_fn B f h))
    (Hne_pair : forall n (p p' q q' : car meta_ofe) (x x' y y' : car C),
                    dist n p p'
                    -> dist n q q'
                    -> dist n x x'
                    -> dist n y y'
                    -> dist n (f_pair p x q y) (f_pair p' x' q' y'))
    (Hne_half : forall n (p p' : car meta_ofe) (x x' : car C),
                  dist n p p'
                  -> dist n x x'
                  -> dist (S n) (f_half p x) (f_half p' x'))
    m,
      meta_nerect C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half (meta_half m)
      =
      f_half
        m (meta_nerect C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half m).
Proof.
intros C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half m.
unfold meta_nerect.
generalize (meta_nerect_poss_true C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half (meta_half m)).
unfold meta_nerect_poss.
rewrite -> meta_rect_half.
intro p.
cbn.
f_equal.
f_equal.
apply proof_irrelevance.
Qed.


Lemma meta_nerect_page :
  forall (C : ofe)
    (f_nats   : car nats_ofe -> car C)
    (f_fn     : forall (R : car (wurel_ofe cur)),
                  (urelsp R -n> @meta_ofe (obj cur))
                  -> (urelsp R -n> C)
                  -> car C)
    (f_pair   : car (@meta_ofe (obj cur)) -> car C -> car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_half   : car (@meta_ofe (obj cur)) -> car C -> car C)
    (f_page   : page -> car C)
    (Hne_nats : forall n I J, dist n I J -> dist n (f_nats I) (f_nats J))
    (Hne_fn : forall n 
                (A B : car urel_ofe) 
                (e : car (nearrow_ofe (urelsp A) meta_ofe))
                (f : car (nearrow_ofe (urelsp B) meta_ofe))
                (g : car (nearrow_ofe (urelsp A) C))
                (h : car (nearrow_ofe (urelsp B) C)),
                  dist n A B
                  -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n e f
                  -> dist_dep (nearrow_dofe _#4 urelsp_neighbor) A B n g h
                  -> dist n (f_fn A e g) (f_fn B f h))
    (Hne_pair : forall n (p p' q q' : car meta_ofe) (x x' y y' : car C),
                    dist n p p'
                    -> dist n q q'
                    -> dist n x x'
                    -> dist n y y'
                    -> dist n (f_pair p x q y) (f_pair p' x' q' y'))
    (Hne_half : forall n (p p' : car meta_ofe) (x x' : car C),
                  dist n p p'
                  -> dist n x x'
                  -> dist (S n) (f_half p x) (f_half p' x'))
    pg,
      meta_nerect C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half (meta_page pg)
      =
      f_page pg.
Proof.
intros C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half pg.
unfold meta_nerect.
generalize (meta_nerect_poss_true C f_nats f_fn f_pair f_half f_page Hne_nats Hne_fn Hne_pair Hne_half (meta_page pg)).
unfold meta_nerect_poss.
rewrite -> meta_rect_page.
intro p.
cbn.
reflexivity.
Qed.


Global Opaque meta_nerect.


End level.
