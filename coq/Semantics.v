
Require Import Tactics.
Require Import Axioms.
Require Import Sigma.
Require Import Relation.
Require Import Equality.
Require Import Syntax.
Require Import SimpSub.
Require Import Dynamic.
Require Import Equivalence.
Require Import Hygiene.
Require Import Ofe.
Require Import Spaces.
Require Import Uniform.
Require Import Urelsp.
Require Import Intensional.
Require Import Ordinal.
Require Import Candidate.
Require Import Model.
Require Import Truncate.
Require Import Standard.
Require Import System.
Require Import Extend.
Require Import MapTerm.
Require Import Ceiling.
Require Export Page.
Require Export PageCode.
Require Import ExtSpace.


Require Import SemanticsAll.
Require Import SemanticsConstfn.
Require Import SemanticsEqtype.
Require Import SemanticsEqual.
Require Import SemanticsExist.
Require Import SemanticsFut.
Require Import SemanticsGuard.
Require Import SemanticsKind.
Require Import SemanticsMu.
Require Import SemanticsPi.
Require Import SemanticsPositive.
Require Import SemanticsQuotient.
Require Import SemanticsSet.
Require Import SemanticsSigma.
Require Import SemanticsSimple.
Require Import SemanticsSubtype.
Require Import SemanticsUniv.
Require Import SemanticsWtype.
Require Import SemanticsPartial.
Require Import PreSpacify.


Section semantics.


Variable system : System.


Definition interp_kext pg i (m : sterm) K : Prop
  :=
  exists Q h,
    hygiene clo m
    /\ star step m (ext (objin (objsome Q h)))
    /\ level (pi1 Q) <<= cin pg
    /\ approx i (pi1 Q) = K.


Definition interp_uext pg i (m : sterm) (R : wurel (cin pg)) : Prop
  :=
  exists w R' h,
    hygiene clo m
    /\ star step m (ext (objin (objsome (expair (qtype w) R') h)))
    /\ w <<= cin pg
    /\ ceiling (S i) (extend_urel w (cin pg) (den R')) = R.


Inductive kbasicv : page -> bool -> nat -> sterm -> qkind -> Prop :=
| interp_kunit :
    forall pg s i,
      kbasicv pg s i unittp qone

| interp_kuniv :
    forall pg s i lv,
      pginterp lv pg
      -> kbasicv pg s i (univ lv) (qtype (cin pg))

| interp_kkarrow :
    forall pg s i k1 k2 K1 K2,
      kbasic pg s i k1 K1
      -> kbasic pg s i k2 K2
      -> kbasicv pg s i (karrow k1 k2) (qarrow K1 K2)

| interp_ktarrow :
    forall pg s i a k A K,
      basic pg s i a (extend_iurel (cin_stop pg) A)
      -> kbasic pg s i k K
      -> kbasicv pg s i (tarrow a k) (qtarrow (cin pg) (den A) K)

| interp_kprod :
    forall pg s i k1 k2 K1 K2,
      kbasic pg s i k1 K1
      -> kbasic pg s i k2 K2
      -> kbasicv pg s i (prod k1 k2) (qprod K1 K2)

| interp_kfut_zero :
    forall pg s k,
      hygiene clo k
      -> kbasicv pg s 0 (fut k) (qfut qone)

| interp_kfut :
    forall pg s i k K,
      kbasic pg s i k K
      -> kbasicv pg s (S i) (fut k) (qfut K)

| interp_krec :
    forall pg s i k K,
      kbasic pg s i (subst1 (rec k) k) K
      -> kbasicv pg s i (rec k) K

with cbasicv : page -> bool -> nat -> sterm -> candidate -> Prop :=
| interp_ext :
    forall pg s i Q h,
      level (pi1 Q) <<= cin pg
      -> cbasicv pg s i (ext (objin (objsome Q h))) (projc i (stdc (S i) Q))

| interp_cunit :
    forall pg s i,
      cbasicv pg s i cunit (expair qone tt)

| interp_clam :
    forall pg s i k a K L (A : space K -n> space L) (h : level K <<= top),
      L = approx i L
      -> interp_kext pg i k K
      -> (forall j,
            j <= i
            -> forall (x : spcar (approx j K)),
                 cbasic pg s j
                   (subst1 
                      (ext (objin (objsome
                                     (expair (approx j K) (std (S j) (approx j K) x))
                                     (le_ord_succ _ _ (le_ord_trans _#3 (approx_level j K) h)))))
                      a)
                   (expair (approx j L) (proj j L (std (S j) L (pi1 A (std (S j) K (embed j K x)))))))
      -> cbasicv pg s i (clam k a) (stdc (S i) (expair (qarrow K L) A))

| interp_capp :
    forall pg s i a b K L (A : space K -n> space L) (B : spcar K),
      cbasic pg s i a (expair (qarrow K L) A)
      -> cbasic pg s i b (expair K B)
      -> cbasicv pg s i (capp a b) (expair L (pi1 A B))

| interp_ctlam :
    forall pg s i a b k K 
      (A : wurel (cin pg))
      (f : forall j m n,
             rel (extend_urel (cin pg) stop A) j m n
             -> spcar (approx j K))
      (B : urelsp A -n> space K),
        hygiene (permit clo) b
        -> interp_uext pg i a A
        -> interp_kext pg i k K  (* need K explicitly, because A might be empty *)
        (* This circumlocution is to ensure B is uniquely determined,
           and then additionally complicated so that Coq gives us
           a good induction principle.
        *)
        -> (forall j m n (Hmn : rel (extend_urel (cin pg) stop A) j m n),
              cbasic pg s j
                (subst1 (if s then m else n) b)
                (expair (approx j K) (f j m n Hmn)))
        -> (forall j m n (Hmn : rel (extend_urel (cin pg) stop A) j m n),
              pi1 B (urelspinj A j _ _ Hmn)
              =
              embed j K (f j m n Hmn))
        -> cbasicv pg s i (ctlam a b k) (expair (qtarrow (cin pg) A K) B)

| interp_ctapp :
    forall pg (s : bool) i b m l A K (B : urelsp A -n> space K) n p (Hnp : rel A i n p),
      map_term (extend stop l) m = (if s then n else p)
      -> cbasic pg s i b (expair (qtarrow l A K) B)
      -> cbasicv pg s i (ctapp b m) (expair K (pi1 B (urelspinj _#4 Hnp)))

| interp_cpair :
    forall pg s i a b K L x y,
      cbasic pg s i a (expair K x)
      -> cbasic pg s i b (expair L y)
      -> cbasicv pg s i (cpair a b) (expair (qprod K L) (x, y))

| interp_cpi1 :
    forall pg s i a K L x,
      cbasic pg s i a (expair (qprod K L) x)
      -> cbasicv pg s i (cpi1 a) (expair K (fst x))

| interp_cpi2 :
    forall pg s i a K L x,
      cbasic pg s i a (expair (qprod K L) x)
      -> cbasicv pg s i (cpi2 a) (expair L (snd x))

| interp_cnext_zero :
    forall pg s a,
      hygiene clo a
      -> cbasicv pg s 0 (cnext a) (expair (qfut qone) tt)

| interp_cnext :
    forall pg s i a K x,
      cbasic pg s i a (expair K x)
      -> cbasicv pg s (S i) (cnext a) (expair (qfut K) x)

| interp_cprev :
    forall pg s i a K x,
      cbasic pg s (S i) a (expair (qfut K) x)
      -> cbasicv pg s i (cprev a) (expair K x)

| interp_cty :
    forall pg s i a (R : wiurel (cin pg)),
      basic pg s i a (extend_iurel (cin_stop pg) R)
      -> cbasicv pg s i (cty a) (expair (qtype (cin pg)) R)

with basicv : page -> bool -> nat -> sterm -> wiurel stop -> Prop :=
| interp_con :
    forall pg s i lv a gpg (R : wiurel (cin gpg)),
      pginterp lv gpg
      -> le_page gpg pg
      -> cbasic gpg s i a (expair (qtype (cin gpg)) R)
      -> basicv pg s i (con lv a) (extend_iurel (cin_stop gpg) R)

| interp_karrow :
    forall pg s i a b (A B : wiurel stop),
        basic pg s i a A
        -> basic pg s i b B
        -> basicv pg s i (karrow a b) (iuarrow stop i A B)

| interp_tarrow :
    forall pg s i a b (A B : wiurel stop),
        basic pg s i a A
        -> basic pg s i b B
        -> basicv pg s i (tarrow a b) (iuarrow stop i A B)

| interp_pi :
    forall pg s i a b
      (A : wiurel stop) (B : urelsp (den A) -n> wiurel_ofe stop),
        basic pg s i a A
        -> functional pg s i (den A) b B
        -> basicv pg s i (pi a b) (iupi stop i A B)

| interp_intersect :
    forall pg s i a b
      (A : wiurel stop) (B : urelsp (den A) -n> wiurel_ofe stop),
        basic pg s i a A
        -> functional pg s i (den A) b B
        -> basicv pg s i (intersect a b) (iuintersect stop i A B)

| interp_union :
    forall pg s i a b
      (A : wiurel stop) (B : urelsp (den A) -n> wiurel_ofe stop),
        basic pg s i a A
        -> functional pg s i (den A) b B
        -> basicv pg s i (union a b) (iuunion stop A B)

| interp_constfn :
    forall pg s i,
      basicv pg s i constfn (iubase (constfn_urel stop i))

| interp_prod :
    forall pg s i a b (A B : wiurel stop),
        basic pg s i a A
        -> basic pg s i b B
        -> basicv pg s i (prod a b) (iuprod stop A B)

| interp_sigma :
    forall pg s i a b
      (A : wiurel stop) (B : urelsp (den A) -n> wiurel_ofe stop),
        basic pg s i a A
        -> functional pg s i (den A) b B
        -> basicv pg s i (sigma a b) (iusigma stop A B)

| interp_set :
    forall pg s i a b
      (A : wiurel stop) (B : urelsp (den A) -n> wiurel_ofe stop),
        basic pg s i a A
        -> functional pg s i (den A) b B
        -> basicv pg s i (set a b) (iuset stop A B)

| interp_iset :
    forall pg s i a b
      (A : wiurel stop) (B : urelsp (den A) -n> wiurel_ofe stop),
        basic pg s i a A
        -> functional pg s i (den A) b B
        -> basicv pg s i (iset a b) (iuiset stop A B)

| interp_quotient :
    forall pg s i a b
      (A : wiurel stop)
      (B : urelsp (prod_urel stop (den A) (den A)) -n> wiurel_ofe stop)
      (hs : symmish stop (den A) (fun x => den (pi1 B x)))
      (ht : transish stop (den A) (fun x => den (pi1 B x))),
        basic pg s i a A
        -> functional pg s i (prod_urel stop (den A) (den A))
             (subst (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1)) b) B
        -> basicv pg s i (quotient a b) (iuquotient stop A B hs ht)

| interp_guard :
    forall pg s i a b 
      (A : wiurel stop) 
      (B : urelsp (squash_urel stop (den A) i) -n> wiurel_ofe stop),
        basic pg s i a A
        -> functional pg s i (squash_urel stop (den A) i) (subst sh1 b) B
        -> basicv pg s i (guard a b) (iuguard stop i A B)

| interp_coguard :
    forall pg s i a b 
      (A : wiurel stop) 
      (B : urelsp (squash_urel stop (den A) i) -n> wiurel_ofe stop),
        basic pg s i a A
        -> functional pg s i (squash_urel stop (den A) i) (subst sh1 b) B
        -> basicv pg s i (coguard a b) (iucoguard stop i A B)

| interp_fut_zero :
    forall pg s a,
      hygiene clo a
      -> basicv pg s 0 (fut a) (iufut0 stop)

| interp_fut :
    forall pg s i a (A : wiurel stop),
      basic pg s i a A
      -> basicv pg s (S i) (fut a) (iufut stop (S i) A)

| interp_void :
    forall pg s i,
      basicv pg s i voidtp (iubase (void_urel stop))

| interp_unit :
    forall pg s i,
      basicv pg s i unittp (iubase (unit_urel stop i))

| interp_bool :
    forall pg s i,
      basicv pg s i booltp (iubase (bool_urel stop i))

| interp_wt :
    forall pg s i a b
      (A : wiurel stop) (B : urelsp (den A) -n> wiurel_ofe stop),
        basic pg s i a A
        -> functional pg s i (den A) b B
        -> basicv pg s i (wt a b) (iuwt stop A B)

| interp_equal :
    forall pg s i a m n p q (A : wiurel stop) 
      (Hmp : srel s (den A) i m p)
      (Hnq : srel s (den A) i n q),
        basic pg s i a A
        -> basicv pg s i (equal a m n) 
             (iuequal stop s i A m n p q Hmp Hnq)

| interp_eqtype :
    forall pg s i a b R R',
      basic pg s i a R
      -> basic pg s i b R'
      -> basicv pg s i (eqtype a b) (iueqtype stop i R R')

| interp_sequal :
    forall s i m n,
      hygiene clo m
      -> hygiene clo n
      -> equiv m n
      -> basicv toppg s i (sequal m n) (iubase (unit_urel stop i))

| interp_subtype :
    forall pg s i a b R R',
      basic pg s i a R
      -> basic pg s i b R'
      -> basicv pg s i (subtype a b) (iusubtype stop i R R')

| interp_all :
    forall pg s i lv k a gpg K (A : space K -n> wiurel_ofe stop) (h : level K <<= top),
      pginterp lv gpg
      -> kbasic gpg s i k K
      -> le_page gpg pg
      -> (forall j,
            j <= i
            -> forall (x : spcar (approx j K)),
                 basic pg s j
                   (subst1 
                      (app 
                         (fromsp stop gpg (approx j K))
                         (ext (objin 
                                 (objsome
                                    (expair (approx j K) (std (S j) (approx j K) x))
                                    (le_ord_succ _ _ (le_ord_trans _#3 (approx_level j K) h))))))
                      a)
                   (iutruncate (S j) (pi1 A (std (S j) K (embed j K x)))))
      -> basicv pg s i (all lv k a) (iuall stop K (std (S i) (qarrow K (qtype stop)) A))

| interp_alltp :
    forall pg s i a (A : wiurel_ofe top -n> wiurel_ofe stop),
      (forall j,
         j <= i
         -> forall (X : wiurel top),
              basic pg s j
                (subst1
                   (extt (objin (objsome (expair (qtype top) X) (succ_increase top))))
                   a)
                (iutruncate (S j) (pi1 A X)))
      -> basicv pg s i (alltp a) (iualltp stop (nearrow_compose (iutruncate_ne (S i)) A))

| interp_exist :
    forall pg s i lv k a gpg K (A : space K -n> wiurel_ofe stop) (h : level K <<= top),
      pginterp lv gpg
      -> kbasic gpg s i k K
      -> le_page gpg pg
      -> (forall j,
            j <= i
            -> forall (x : spcar (approx j K)),
                 basic pg s j
                   (subst1 
                      (app 
                         (fromsp stop gpg (approx j K))
                         (ext (objin 
                                 (objsome
                                    (expair (approx j K) (std (S j) (approx j K) x))
                                    (le_ord_succ _ _ (le_ord_trans _#3 (approx_level j K) h))))))
                      a)
                   (iutruncate (S j) (pi1 A (std (S j) K (embed j K x)))))
      -> basicv pg s i (exist lv k a) (iuexist stop K (std (S i) (qarrow K (qtype stop)) A))

| interp_extt :
    forall pg s i w R (h : w << stop),
      w <<= cin pg
      -> basicv pg s i (extt (objin (objsome (expair (qtype w) R) h)))
           (extend_iurel (lt_ord_impl_le_ord _ _ h) (iutruncate (S i) R))

| interp_mu :
    forall pg w s i a (F : car (wurel_ofe w) -> car (wiurel_ofe w)),
        w <<= cin pg
        -> (forall (X : car (wurel_ofe w)) (h : w << stop),
              basic pg s i
                (subst1
                   (extt (objin
                            (objsome
                               (expair (qtype w) (iubase X))
                               h)))
                   a)
                (extend_iurel (lt_ord_impl_le_ord _ _ h) (F X)))
        -> nonexpansive (fun X => den (F X))
        -> monotone (fun X => den (F X))
        -> robust 0 a
        -> basicv pg s i (mu a) (iubase (extend_urel w stop (mu_urel w (fun X => den (F X)))))

| interp_ispositive :
    forall pg s i a,
      hygiene (permit clo) a
      -> basicv pg s i (ispositive a) (iubase (ispositive_urel stop i a))

| interp_isnegative :
    forall pg s i a,
      hygiene (permit clo) a
      -> basicv pg s i (isnegative a) (iubase (isnegative_urel stop i a))

| interp_rec :
    forall pg s i a A,
      basic pg s i (subst1 (rec a) a) A
      -> basicv pg s i (rec a) A

| interp_univ :
    forall pg s i m gpg,
      pginterp m gpg
      -> str gpg << str pg
      -> cex gpg << cin pg
      -> basicv pg s i (univ m) (iuuniv system i gpg)

| interp_kind :
    forall pg s i m gpg (h : lt_page gpg toppg),
      pginterp m gpg
      -> lt_page (succ_page gpg h) pg
      -> basicv pg s i (kind m) (iukind system i gpg h)

| interp_partial :
    forall pg s i a (A : wiurel stop),
      basic pg s i a A
      -> basicv pg s i (partial a) (iupartial stop i A)

| interp_halts :
    forall pg s i m,
      hygiene clo m
      -> basicv pg s i (halts m) (iubase (halts_urel stop i m))

| interp_admiss :
    forall pg s i a (A : wiurel stop),
      basic pg s i a A
      -> basicv pg s i (admiss a) (iuadmiss stop i A)

| interp_uptype :
    forall pg s i a (A : wiurel stop),
      basic pg s i a A
      -> basicv pg s i (uptype a) (iuuptype stop i A)


with kbasic : page -> bool -> nat -> sterm -> qkind -> Prop :=
| kinterp_eval :
    forall pg s i k k' K,
      hygiene clo k
      -> star step k k'
      -> kbasicv pg s i k' K
      -> kbasic pg s i k K


with cbasic : page -> bool -> nat -> sterm -> candidate -> Prop :=
| cinterp_eval :
    forall pg s i c c' Q,
      hygiene clo c
      -> star step c c'
      -> cbasicv pg s i c' Q
      -> cbasic pg s i c Q


with basic : page -> bool -> nat -> sterm -> wiurel stop -> Prop :=
| interp_eval :
    forall pg s i a a' R,
      hygiene clo a
      -> star step a a'
      -> basicv pg s i a' R
      -> basic pg s i a R


with functional : page -> bool -> nat -> forall (A : wurel stop), sterm -> (urelsp A -n> wiurel_ofe stop) -> Prop :=
| functional_i :
    forall pg s i (A : wurel stop) b (B : urelsp A -n> wiurel_ofe stop),
      hygiene (permit clo) b
      (* We know A = ceiling (S i) A, but requiring it here allows us to disentangle
         a mutual dependency between functionality and downward.
      *)
      -> A = ceiling (S i) A
      -> (forall j m p (Hj : j <= i) (Hmp : rel A j m p),
            basic pg s j 
              (subst1 (if s then m else p) b)
              (pi1 B (urelspinj A j m p Hmp)))
      -> functional pg s i A b B
.


Scheme kbasicv_mut_ind := Minimality for kbasicv Sort Prop
with   cbasicv_mut_ind := Minimality for cbasicv Sort Prop
with   basicv_mut_ind := Minimality for basicv Sort Prop
with   kbasic_mut_ind := Minimality for kbasic Sort Prop
with   cbasic_mut_ind := Minimality for cbasic Sort Prop
with   basic_mut_ind := Minimality for basic Sort Prop
with   functional_mut_ind := Minimality for functional Sort Prop.
Combined Scheme semantics_ind from kbasic_mut_ind, cbasic_mut_ind, basic_mut_ind, kbasicv_mut_ind, cbasicv_mut_ind, basicv_mut_ind, functional_mut_ind.


Lemma kbasicv_value :
  forall pg s i a X,
    kbasicv pg s i a X
    -> value a.
Proof.
intros pg s i a X H.
induct H; eauto with dynamic.
Qed.


Lemma cbasicv_value :
  forall pg s i a X,
    cbasicv pg s i a X
    -> value a.
Proof.
intros pg s i a X H.
induct H; eauto with dynamic.
Qed.


Lemma basicv_value :
  forall pg s i a X,
    basicv pg s i a X
    -> value a.
Proof.
intros pg s i a X H.
induct H; eauto with dynamic.
Qed.


Lemma kbasic_value_inv :
  forall pg s i k K,
    value k
    -> kbasic pg s i k K
    -> kbasicv pg s i k K.
Proof.
intros pg s i k K Hval Hint.
invertc Hint.
intros k' _ Hsteps Hint.
so (determinism_normal_value _#3 Hval Hsteps); subst k'.
exact Hint.
Qed.


Lemma cbasic_value_inv :
  forall pg s i c Q,
    value c
    -> cbasic pg s i c Q
    -> cbasicv pg s i c Q.
Proof.
intros pg s i c Q Hval Hint.
invertc Hint.
intros c' _ Hsteps Hint.
so (determinism_normal_value _#3 Hval Hsteps); subst c'.
exact Hint.
Qed.


Lemma basic_value_inv :
  forall pg s i a R,
    value a
    -> basic pg s i a R
    -> basicv pg s i a R.
Proof.
intros pg s i a R Hval Hint.
invertc Hint.
intros a' _ Hsteps Hint.
so (determinism_normal_value _#3 Hval Hsteps); subst a'.
exact Hint.
Qed.


Lemma transport_functional :
  forall pg s i A A' b B (h : A = A'),
    functional pg s i A' b B
    -> functional pg s i A b (nearrow_compose B (transport_ne h urelsp)).
Proof.
intros pg s i A A' b B h Hfunc.
subst A'.
force_exact Hfunc.
f_equal.
apply nearrow_extensionality.
intro x.
cbn.
reflexivity.
Qed.


Lemma functional_rewrite :
  forall pg s i A A' b B B',
    eq_dep _ (fun A => urelsp A -n> wiurel_ofe stop) A B A' B'
    -> functional pg s i A b B
       =
       functional pg s i A' b B'.
Proof.
intros pg s i A A' b B B' Heq.
injectionT Heq.
intros <-.
injectionT Heq.
intros <-.
reflexivity.
Qed.


Lemma basic_unstep :
  forall pg s i a b R,
    hygiene clo a
    -> star step a b
    -> basic pg s i b R
    -> basic pg s i a R.
Proof.
intros pg s i a b R Hhyg Hab Hint.
invertc Hint.
intros c _ Hbc Hint.
apply (interp_eval _#4 c); auto.
eapply star_trans; eauto.
Qed.


End semantics.


Hint Constructors kbasicv cbasicv basicv kbasic cbasic basic functional : semantics.
