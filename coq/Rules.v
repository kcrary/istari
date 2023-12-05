
Require Import Coq.Lists.List.

Require Import Tactics.
Require Import Sequence.
Require Import Syntax.
Require Import Subst.
Require Import SimpSub.
Require Import Promote.
Require Import Equivalence.
Require Import Defined.
Require Page.
Require Candidate.


Definition obj := Candidate.obj Page.stop.


Inductive tr : @context obj -> judgement -> Prop :=

(* Hypotheses *)

| tr_hyp_tm :
    forall G i a,
      index i G (hyp_tm a)
      -> tr G (deq (var i) (var i) (subst (sh (S i)) a))
  
| tr_hyp_tp :
    forall G i,
      index i G hyp_tp
      -> tr G (deqtype (var i) (var i)) 
  
(* Pi/Arrow/Karrow/Intersect *)

| tr_pi_formation :
    forall G a a' b b',
      tr G (deqtype a a')
      -> tr (cons (hyp_tm a) G) (deqtype b b')
      -> tr G (deqtype (pi a b) (pi a' b'))
  
| tr_pi_formation_univ :
    forall G lv a a' b b',
      tr G (deq a a' (univ lv))
      -> tr (cons (hyp_tm a) G) (deq b b' (univ (subst sh1 lv)))
      -> tr G (deq (pi a b) (pi a' b') (univ lv))
  
| tr_pi_intro :
    forall G a b m n,
      tr G (deqtype a a)
      -> tr (cons (hyp_tm a) G) (deq m n b)
      -> tr G (deq (lam m) (lam n) (pi a b))
  
| tr_pi_elim :
    forall G a b m n p q,
      tr G (deq m n (pi a b))
      -> tr G (deq p q a)
      -> tr G (deq (app m p) (app n q) (subst1 p b))
  
| tr_pi_eta :
    forall G a b m,
      tr G (deq m m (pi a b))
      -> tr G (deq m (lam (app (subst sh1 m) (var 0))) (pi a b))

| tr_pi_ext :
    forall G a b m n a' a'' b' b'',
      tr G (deqtype a a)
      -> tr (cons (hyp_tm a) G) 
           (deq 
              (app (subst sh1 m) (var 0))
              (app (subst sh1 n) (var 0))
              b)
      -> tr G (deq m m (pi a' b'))
      -> tr G (deq n n (pi a'' b''))
      -> tr G (deq m n (pi a b))

| tr_arrow_kind_formation :
    forall G lv a b k l,
      tr G (deq a b (univ lv))
      -> tr G (deq k l (kuniv lv))
      -> tr G (deq (arrow a k) (arrow b l) (kuniv lv))
  
| tr_arrow_formation :
    forall G a a' b b',
      tr G (deqtype a a')
      -> tr G (deqtype b b')
      -> tr G (deqtype (arrow a b) (arrow a' b'))
  
| tr_arrow_formation_univ :
    forall G lv a a' b b',
      tr G (deq a a' (univ lv))
      -> tr G (deq b b' (univ lv))
      -> tr G (deq (arrow a b) (arrow a' b') (univ lv))
  
| tr_arrow_pi_equal :
    forall G a b,
      tr G (deqtype a a)
      -> tr G (deqtype b b)
      -> tr G (deqtype (arrow a b) (pi a (subst sh1 b)))
  
| tr_arrow_pi_equal_univ :
    forall G lv a b,
      tr G (deq a a (univ lv))
      -> tr G (deq b b (univ lv))
      -> tr G (deq (arrow a b) (pi a (subst sh1 b)) (univ lv))
  
| tr_arrow_eta :
    forall G a b m,
      tr G (deq m m (arrow a b))
      -> tr G (deq m (lam (app (subst sh1 m) (var 0))) (arrow a b))

| tr_karrow_kind_formation :
    forall G lv k k' l l',
      tr G (deq k k' (kuniv lv))
      -> tr G (deq l l' (kuniv lv))
      -> tr G (deq (karrow k l) (karrow k' l') (kuniv lv))
  
| tr_karrow_formation :
    forall G k k' l l',
      tr G (deqtype k k')
      -> tr G (deqtype l l')
      -> tr G (deqtype (karrow k l) (karrow k' l'))
  
| tr_karrow_formation_univ :
    forall G lv k k' l l',
      tr G (deq k k' (univ lv))
      -> tr G (deq l l' (univ lv))
      -> tr G (deq (karrow k l) (karrow k' l') (univ lv))
  
| tr_karrow_pi_equal :
    forall G a b,
      tr G (deqtype a a)
      -> tr G (deqtype b b)
      -> tr G (deqtype (karrow a b) (pi a (subst sh1 b)))
  
| tr_karrow_pi_equal_univ :
    forall G lv a b,
      tr G (deq a a (univ lv))
      -> tr G (deq b b (univ lv))
      -> tr G (deq (karrow a b) (pi a (subst sh1 b)) (univ lv))
  
| tr_arrow_karrow_equal :
    forall G a b,
      tr G (deqtype a a)
      -> tr G (deqtype b b)
      -> tr G (deqtype (arrow a b) (karrow a b))
  
| tr_arrow_karrow_equal_univ :
    forall G lv a b,
      tr G (deq a a (univ lv))
      -> tr G (deq b b (univ lv))
      -> tr G (deq (arrow a b) (karrow a b) (univ lv))
  
| tr_karrow_eta :
    forall G a b m,
      tr G (deq m m (karrow a b))
      -> tr G (deq m (lam (app (subst sh1 m) (var 0))) (karrow a b))

| tr_pi_formation_invert1 :
    forall G a a' b b',
      tr G (deqtype (pi a b) (pi a' b'))
      -> tr G (deqtype a a')

| tr_pi_formation_invert2 :
    forall G a a' b b',
      tr G (deqtype (pi a b) (pi a' b'))
      -> tr (cons (hyp_tm a) G) (deqtype b b')

| tr_arrow_formation_invert1 :
    forall G a a' b b',
      tr G (deqtype (arrow a b) (arrow a' b'))
      -> tr G (deqtype a a')

| tr_arrow_formation_invert2 :
    forall G a a' b b',
      tr G (deqtype (arrow a b) (arrow a' b'))
      -> tr (cons (hyp_tm a) G) (deqtype (subst sh1 b) (subst sh1 b'))
  
| tr_karrow_formation_invert1 :
    forall G a a' b b',
      tr G (deqtype (karrow a b) (karrow a' b'))
      -> tr G (deqtype a a')

| tr_karrow_formation_invert2 :
    forall G a a' b b',
      tr G (deqtype (karrow a b) (karrow a' b'))
      -> tr (cons (hyp_tm a) G) (deqtype (subst sh1 b) (subst sh1 b'))

| tr_intersect_formation :
    forall G a a' b b',
      tr G (deqtype a a')
      -> tr (cons (hyp_tm a) G) (deqtype b b')
      -> tr G (deqtype (intersect a b) (intersect a' b'))

| tr_intersect_formation_univ :
    forall G lv a a' b b',
      tr G (deq a a' (univ lv))
      -> tr (cons (hyp_tm a) G) (deq b b' (univ (subst sh1 lv)))
      -> tr G (deq (intersect a b) (intersect a' b') (univ lv))

| tr_intersect_intro :
    forall G a b m n,
      tr G (deqtype a a)
      -> tr (cons (hyp_tm a) G) (deq (subst sh1 m) (subst sh1 n) b)
      -> tr G (deq m n (intersect a b))

| tr_intersect_elim :
    forall G a b m n p q,
      tr G (deq m n (intersect a b))
      -> tr G (deq p q a)
      -> tr G (deq m n (subst1 p b))

| tr_intersect_formation_invert1 :
    forall G a a' b b',
      tr G (deqtype (intersect a b) (intersect a' b'))
      -> tr G (deqtype a a')

| tr_intersect_formation_invert2 :
    forall G a a' b b',
      tr G (deqtype (intersect a b) (intersect a' b'))
      -> tr (cons (hyp_tm a) G) (deqtype b b')

(* Strong sums *)

| tr_sigma_formation :
    forall G a a' b b',
      tr G (deqtype a a')
      -> tr (cons (hyp_tm a) G) (deqtype b b')
      -> tr G (deqtype (sigma a b) (sigma a' b'))
  
| tr_sigma_formation_univ :
    forall G lv a a' b b',
      tr G (deq a a' (univ lv))
      -> tr (cons (hyp_tm a) G) (deq b b' (univ (subst sh1 lv)))
      -> tr G (deq (sigma a b) (sigma a' b') (univ lv))
  
| tr_sigma_intro :
    forall G a b m m' n n',
      tr G (deq m m' a)
      -> tr G (deq n n' (subst1 m b))
      -> tr (cons (hyp_tm a) G) (deqtype b b)
      -> tr G (deq (ppair m n) (ppair m' n') (sigma a b))
  
| tr_sigma_elim1 :
    forall G a b m n,
      tr G (deq m n (sigma a b))
      -> tr G (deq (ppi1 m) (ppi1 n) a)
  
| tr_sigma_elim2 :
    forall G a b m n,
      tr G (deq m n (sigma a b))
      -> tr G (deq (ppi2 m) (ppi2 n) (subst1 (ppi1 m) b))
  
| tr_sigma_eta :
    forall G a b m,
      tr G (deq m m (sigma a b))
      -> tr G (deq m (ppair (ppi1 m) (ppi2 m)) (sigma a b))
  
| tr_sigma_eta_hyp :
    forall G1 G2 a b m n c,
      tr (substctx (dot (ppair (var 1) (var 0)) (sh 2)) G2 ++ cons (hyp_tm b) (cons (hyp_tm a) G1)) (deq m n (subst (under (length G2) (dot (ppair (var 1) (var 0)) (sh 2))) c))
      -> tr (G2 ++ cons (hyp_tm (sigma a b)) G1) (deq (subst (under (length G2) (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1))) m) (subst (under (length G2) (dot (ppi2 (var 0)) (dot (ppi1 (var 0)) sh1))) n) c)

| tr_sigma_ext :
    forall G a b m n a' a'' b' b'',
      tr G (deq (ppi1 m) (ppi1 n) a)
      -> tr G (deq (ppi2 m) (ppi2 n) (subst1 (ppi1 m) b))
      -> tr (cons (hyp_tm a) G) (deqtype b b)
      -> tr G (deq m m (sigma a' b'))
      -> tr G (deq n n (sigma a'' b''))
      -> tr G (deq m n (sigma a b))

| tr_prod_kind_formation :
    forall G lv k k' l l',
      tr G (deq k k' (kuniv lv))
      -> tr G (deq l l' (kuniv lv))
      -> tr G (deq (prod k l) (prod k' l') (kuniv lv))
  
| tr_prod_formation :
    forall G k k' l l',
      tr G (deqtype k k')
      -> tr G (deqtype l l')
      -> tr G (deqtype (prod k l) (prod k' l'))
  
| tr_prod_formation_univ :
    forall G lv k k' l l',
      tr G (deq k k' (univ lv))
      -> tr G (deq l l' (univ lv))
      -> tr G (deq (prod k l) (prod k' l') (univ lv))
  
| tr_prod_sigma_equal :
    forall G a b,
      tr G (deqtype a a)
      -> tr G (deqtype b b)
      -> tr G (deqtype (prod a b) (sigma a (subst sh1 b)))
  
| tr_prod_sigma_equal_univ :
    forall G lv a b,
      tr G (deq a a (univ lv))
      -> tr G (deq b b (univ lv))
      -> tr G (deq (prod a b) (sigma a (subst sh1 b)) (univ lv))
  
| tr_prod_elim1 :
    forall G a b m n,
      tr G (deq m n (prod a b))
      -> tr G (deq (ppi1 m) (ppi1 n) a)
  
| tr_prod_elim2 :
    forall G a b m n,
      tr G (deq m n (prod a b))
      -> tr G (deq (ppi2 m) (ppi2 n) b)

| tr_sigma_formation_invert1 :
    forall G a a' b b',
      tr G (deqtype (sigma a b) (sigma a' b'))
      -> tr G (deqtype a a')

| tr_sigma_formation_invert2 :
    forall G a a' b b',
      tr G (deqtype (sigma a b) (sigma a' b'))
      -> tr (cons (hyp_tm a) G) (deqtype b b')

| tr_prod_formation_invert1 :
    forall G a a' b b',
      tr G (deqtype (prod a b) (prod a' b'))
      -> tr G (deqtype a a')

| tr_prod_formation_invert2 :
    forall G a a' b b',
      tr G (deqtype (prod a b) (prod a' b'))
      -> tr (cons (hyp_tm a) G) (deqtype (subst sh1 b) (subst sh1 b'))
  
(* Unions (weak sums) *)

| tr_union_formation :
    forall G a a' b b',
      tr G (deqtype a a')
      -> tr (cons (hyp_tm a) G) (deqtype b b')
      -> tr G (deqtype (union a b) (union a' b'))

| tr_union_formation_univ :
    forall G lv a a' b b',
      tr G (deq a a' (univ lv))
      -> tr (cons (hyp_tm a) G) (deq b b' (univ (subst sh1 lv)))
      -> tr G (deq (union a b) (union a' b') (univ lv))

| tr_union_intro :
    forall G a b p m n,
      tr G (deq p p a)
      -> tr G (deq m n (subst1 p b))
      -> tr (cons (hyp_tm a) G) (deqtype b b)
      -> tr G (deq m n (union a b))

| tr_union_elim :
    forall G a b c m n p q,
      tr G (deq m n (union a b))
      -> tr (cons (hyp_tm b) (cons (hyp_tm a) G)) (deq (subst (dot (var 0) (sh 2)) p) (subst (dot (var 0) (sh 2)) q) (subst (sh 2) c))
      -> tr G (deq (subst1 m p) (subst1 n q) c)
  
| tr_union_elim_eqtype :
    forall G a b m n p q,
      tr G (deq m n (union a b))
      -> tr (cons (hyp_tm b) (cons (hyp_tm a) G)) (deqtype (subst (dot (var 0) (sh 2)) p) (subst (dot (var 0) (sh 2)) q))
      -> tr G (deqtype (subst1 m p) (subst1 n q))
  
(* Fut *)

| tr_fut_kind_formation :
    forall G lv k k',
      tr (promote G) (deq k k' (kuniv lv))
      -> tr G (deq lv lv pagetp)
      -> tr G (deq (fut k) (fut k') (kuniv lv))
  
| tr_fut_formation :
    forall G a b,
      tr (promote G) (deqtype a b)
      -> tr G (deqtype (fut a) (fut b))
  
| tr_fut_formation_univ :
    forall G lv a b,
      tr (promote G) (deq a b (univ lv))
      -> tr G (deq lv lv pagetp)
      -> tr G (deq (fut a) (fut b) (univ lv))
  
| tr_fut_intro :
    forall G m n a,
      tr (promote G) (deq m n a)
      -> tr G (deq (next m) (next n) (fut a))
  
| tr_fut_elim :
    forall G m n a p q b,
      tr G (deq m n (fut a))
      -> tr (promote G) (deqtype a a)
      -> tr (cons (hyp_tml a) G) (deq p q b)
      -> tr G (deq (subst1 (prev m) p) (subst1 (prev n) q) (subst1 (prev m) b))
  
| tr_fut_elim_eqtype :
    forall G m n a b c,
      tr G (deq m n (fut a))
      -> tr (promote G) (deqtype a a)
      -> tr (cons (hyp_tml a) G) (deqtype b c)
      -> tr G (deqtype (subst1 (prev m) b) (subst1 (prev n) c))

| tr_fut_eta :
    forall G m a,
      tr G (deq m m (fut a))
      -> tr G (deq m (next (prev m)) (fut a))
  
| tr_fut_eta_hyp :
    forall G1 G2 a m n b,
      tr (promote G1) (deqtype a a)
      -> tr (substctx (dot (next (var 0)) sh1) G2 ++ cons (hyp_tml a) G1) (deq m n (subst (under (length G2) (dot (next (var 0)) sh1)) b))
      -> tr (G2 ++ cons (hyp_tm (fut a)) G1) (deq (subst (under (length G2) (dot (prev (var 0)) sh1)) m) (subst (under (length G2) (dot (prev (var 0)) sh1)) n) b)

| tr_fut_ext :
    forall G a b c m n,
      tr G (deq m m (fut b))
      -> tr G (deq n n (fut c))
      -> tr G (deq (next (prev m)) (next (prev n)) (fut a))
      -> tr G (deq m n (fut a))

(* Guarded recursive types *)

| tr_rec_kind_formation :
    forall G lv k k',
      tr (cons (hyp_tml (kuniv lv)) G) (deq k k' (kuniv (subst sh1 lv)))
      -> tr G (deq lv lv pagetp)
      -> tr G (deq (rec k) (rec k') (kuniv lv))

| tr_rec_formation :
    forall G a b,
      tr (cons hyp_tpl G) (deqtype a b)
      -> tr G (deqtype (rec a) (rec b))

| tr_rec_formation_univ :
    forall G lv a b,
      tr (cons (hyp_tml (univ lv)) G) (deq a b (univ (subst sh1 lv)))
      -> tr G (deq lv lv pagetp)
      -> tr G (deq (rec a) (rec b) (univ lv))

| tr_rec_unroll :
    forall G a,
      tr (cons hyp_tpl G) (deqtype a a)
      -> tr G (deqtype (rec a) (subst1 (rec a) a))

| tr_rec_unroll_univ :
    forall G lv a,
      tr (cons (hyp_tml (univ lv)) G) (deq a a (univ (subst sh1 lv)))
      -> tr G (deq lv lv pagetp)
      -> tr G (deq (rec a) (subst1 (rec a) a) (univ lv))

| tr_rec_bisim :
    forall G a b,
      tr (cons hyp_tpl G) (deqtype a a)
      -> tr G (deqtype b (subst1 b a))
      -> tr G (deqtype b (rec a))

(* Void *)

| tr_voidtp_formation_univ :
    forall G,
      tr G (deq voidtp voidtp (univ nzero))

| tr_voidtp_elim :
    forall G m n p q a,
      tr G (deq m n voidtp)
      -> tr G (deq p q a)

(* Unit *)

| tr_unittp_kind_formation :
    forall G lv,
      tr G (deq lv lv pagetp)
      -> tr G (deq unittp unittp (kuniv lv))

| tr_unittp_formation_univ :
    forall G,
      tr G (deq unittp unittp (univ nzero))

| tr_unittp_intro :
    forall G,
      tr G (deq triv triv unittp)

| tr_unittp_eta :
    forall G p,
      tr G (deq p p unittp)
      -> tr G (deq p triv unittp)

| tr_unittp_eta_hyp :
    forall G1 G2 m n b,
      tr (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
      -> tr (G2 ++ hyp_tm unittp :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b)

(* Bool *)

| tr_booltp_formation_univ :
    forall G,
      tr G (deq booltp booltp (univ nzero))

| tr_booltp_intro_btrue :
    forall G,
      tr G (deq btrue btrue booltp)

| tr_booltp_intro_bfalse :
    forall G,
      tr G (deq bfalse bfalse booltp)

| tr_booltp_elim :
    forall G m n p q r s a,
      tr G (deq m n booltp)
      -> tr G (deq p q (subst1 btrue a))
      -> tr G (deq r s (subst1 bfalse a))
      -> tr G (deq (bite m p r) (bite n q s) (subst1 m a))

| tr_booltp_elim_eqtype :
    forall G m n a b c d,
      tr G (deq m n booltp)
      -> tr G (deqtype a b)
      -> tr G (deqtype c d)
      -> tr G (deqtype (bite m a c) (bite n b d))

| tr_booltp_eta_hyp :
    forall G1 G2 m n p q a,
      tr (substctx (dot btrue id) G2 ++ G1) (deq m n (subst (under (length G2) (dot btrue id)) a))
      -> tr (substctx (dot bfalse id) G2 ++ G1) (deq p q (subst (under (length G2) (dot bfalse id)) a))
      -> tr (G2 ++ cons (hyp_tm booltp) G1) 
           (deq 
              (bite (var (length G2)) 
                 (subst (under (length G2) sh1) m)
                 (subst (under (length G2) sh1) p))
              (bite (var (length G2))
                 (subst (under (length G2) sh1) n) 
                 (subst (under (length G2) sh1) q) )
              a)

(* W-types (obsolete) *)

| tr_wt_formation :
    forall G a a' b b',
      tr G (deqtype a a')
      -> tr (cons (hyp_tm a) G) (deqtype b b')
      -> tr G (deqtype (wt a b) (wt a' b'))

| tr_wt_formation_univ :
    forall G lv a a' b b',
      tr G (deq a a' (univ lv))
      -> tr (cons (hyp_tm a) G) (deq b b' (univ (subst sh1 lv)))
      -> tr G (deq (wt a b) (wt a' b') (univ lv))

| tr_wt_elim :
    forall G a b c m m' n n',
      tr G (deq m m' (wt a b))
      -> tr
           (cons 
              (hyp_tm (pi (subst sh1 b) (subst (dot (app (var 1) (var 0)) (sh 3)) c)))
              (cons (hyp_tm (arrow b (subst sh1 (wt a b)))) (cons (hyp_tm a) G)))
           (deq n n' (subst (dot (ppair (var 2) (var 1)) (sh 3)) c))
      -> tr G (deq (app (wind (lam (lam (lam n)))) m) (app (wind (lam (lam (lam n')))) m') (subst1 m c))

| tr_wt_subtype_sigma :
    forall G a b,
      tr G (deqtype a a)
      -> tr (cons (hyp_tm a) G) (deqtype b b)
      -> tr G (dsubtype (wt a b) (sigma a (arrow b (subst sh1 (wt a b)))))

| tr_wt_sigma_subtype :
    forall G a b,
      tr G (deqtype a a)
      -> tr (cons (hyp_tm a) G) (deqtype b b)
      -> tr G (dsubtype (sigma a (arrow b (subst sh1 (wt a b)))) (wt a b))

| tr_wt_formation_inv1 :
    forall G a b,
      tr G (deqtype (wt a b) (wt a b))
      -> tr G (deqtype a a)

| tr_wt_formation_inv2 :
    forall G a b,
      tr G (deqtype (wt a b) (wt a b))
      -> tr (cons (hyp_tm a) G) (deqtype b b)


(* Impredicative polymorphism *)

| tr_all_formation :
    forall G glv k l a b,
      tr G (deq k l (kuniv glv))
      -> tr (cons (hyp_tm k) G) (deqtype a b)
      -> tr G (deqtype (all glv k a) (all glv l b))

| tr_all_formation_univ :
    forall G glv lv k l a b,
      tr G (deq k l (kuniv glv))
      -> tr (cons (hyp_tm k) G) (deq a b (univ (subst sh1 lv)))
      -> tr G (deq lv lv pagetp)
      -> tr G (deq triv triv (leqpagetp glv lv))
      -> tr G (deq (all glv k a) (all glv l b) (univ lv))
  
| tr_all_intro :
    forall G lv k a m n,
      tr G (deq k k (kuniv lv))
      -> tr (cons (hyp_tm k) G) (deq (subst sh1 m) (subst sh1 n) a)
      -> tr G (deq m n (all lv k a))
  
| tr_all_elim :
    forall G lv k a m n p,
      tr G (deq m n (all lv k a))
      -> tr G (deq p p k)
      -> tr (cons (hyp_tm k) G) (deqtype a a)
      -> tr G (deq m n (subst1 p a))

| tr_alltp_formation :
    forall G a b,
      tr (cons hyp_tp G) (deqtype a b)
      -> tr G (deqtype (alltp a) (alltp b))
  
| tr_alltp_intro :
    forall G a m n,
      tr (cons hyp_tp G) (deq (subst sh1 m) (subst sh1 n) a)
      -> tr G (deq m n (alltp a))

| tr_alltp_elim :
    forall G a b m n,
      tr G (deq m n (alltp a))
      -> tr G (deqtype b b)
      -> tr (cons hyp_tp G) (deqtype a a)
      -> tr G (deq m n (subst1 b a))

(* Impredicative existential *)

| tr_exist_formation :
    forall G glv k l a b,
      tr G (deq k l (kuniv glv))
      -> tr (cons (hyp_tm k) G) (deqtype a b)
      -> tr G (deqtype (exist glv k a) (exist glv l b))
  
| tr_exist_formation_univ :
    forall G glv lv k l a b,
      tr G (deq k l (kuniv glv))
      -> tr (cons (hyp_tm k) G) (deq a b (univ (subst sh1 lv)))
      -> tr G (deq lv lv pagetp)
      -> tr G (deq triv triv (leqpagetp glv lv))
      -> tr G (deq (exist glv k a) (exist glv l b) (univ lv))
  
| tr_exist_intro :
    forall G lv k a b m n,
      tr G (deq k k (kuniv lv))
      -> tr G (deq b b k)
      -> tr G (deq m n (subst1 b a))
      -> tr (cons (hyp_tm k) G) (deqtype a a)
      -> tr G (deq m n (exist lv k a))
  
| tr_exist_elim :
    forall G lv k a b m n p q,
      tr G (deq m n (exist lv k a))
      -> tr G (deqtype k k)
      -> tr (cons (hyp_tm k) G) (deqtype a a)
      -> tr (cons (hyp_tm a) (cons (hyp_tm k) G)) (deq (subst (dot (var 0) (sh 2)) p) (subst (dot (var 0) (sh 2)) q) (subst (sh 2) b))
      -> tr G (deq (subst1 m p) (subst1 n q) b)

| tr_exist_elim_eqtype :
    forall G lv k a m n p q,
      tr G (deq m n (exist lv k a))
      -> tr G (deqtype k k)
      -> tr (cons (hyp_tm k) G) (deqtype a a)
      -> tr (cons (hyp_tm a) (cons (hyp_tm k) G)) (deqtype (subst (dot (var 0) (sh 2)) p) (subst (dot (var 0) (sh 2)) q))
      -> tr G (deqtype (subst1 m p) (subst1 n q))

(* Inductive types *)

| tr_mu_formation :
    forall G a b,
      tr (hyp_tp :: G) (deqtype a b)
      -> tr G (deq triv triv (ispositive a))
      -> tr G (deq triv triv (ispositive b))
      -> tr G (deqtype (mu a) (mu b))

| tr_mu_formation_univ :
    forall G lv a b,
      tr G (deq lv lv pagetp)
      -> tr (hyp_tm (univ lv) :: G) (deq a b (univ (subst sh1 lv)))
      -> tr G (deq triv triv (ispositive a))
      -> tr G (deq triv triv (ispositive b))
      -> tr G (deq (mu a) (mu b) (univ lv))

| tr_mu_roll :
    forall G a,
      tr (hyp_tp :: G) (deqtype a a)
      -> tr G (deq triv triv (ispositive a))
      -> tr G (dsubtype (subst1 (mu a) a) (mu a))

| tr_mu_unroll :
    forall G a,
      tr (hyp_tp :: G) (deqtype a a)
      -> tr G (deq triv triv (ispositive a))
      -> tr G (dsubtype (mu a) (subst1 (mu a) a))

| tr_mu_roll_univ :
    forall G lv a,
      tr G (deq lv lv pagetp)
      -> tr (hyp_tm (univ lv) :: G) (deq a a (univ (subst sh1 lv)))
      -> tr G (deq triv triv (ispositive a))
      -> tr G (dsubtype (subst1 (mu a) a) (mu a))

| tr_mu_unroll_univ :
    forall G lv a,
      tr G (deq lv lv pagetp)
      -> tr (hyp_tm (univ lv) :: G) (deq a a (univ (subst sh1 lv)))
      -> tr G (deq triv triv (ispositive a))
      -> tr G (dsubtype (mu a) (subst1 (mu a) a))

| tr_mu_ind :
    forall G a b m,
      tr (hyp_tp :: G) (deqtype a a)
      -> tr G (deq triv triv (ispositive a))
      -> tr
           (hyp_tm (pi (var 2) (subst (under 1 (sh 3)) b)) ::
            hyp_tm (subtype (var 1) (mu (subst (under 1 (sh 2)) a))) ::
            hyp_tm a ::
            hyp_tp :: 
            G)
           (deq triv triv (subst (dot (var 2) (sh 4)) b))
      -> tr G (deq m m (mu a))
      -> tr G (deq triv triv (subst1 m b))

| tr_mu_ind_univ :
    forall G lv a b m,
      tr G (deq lv lv pagetp)
      -> tr (hyp_tm (univ lv) :: G) (deq a a (univ (subst sh1 lv)))
      -> tr G (deq triv triv (ispositive a))
      -> tr
           (hyp_tm (pi (var 2) (subst (under 1 (sh 3)) b)) ::
            hyp_tm (subtype (var 1) (mu (subst (under 1 (sh 2)) a))) ::
            hyp_tm a ::
            hyp_tm (univ lv) :: 
            G)
           (deq 
              (subst (dot (var 2) (sh 4)) b)
              (subst (dot (var 2) (sh 4)) b) 
              (univ (subst (sh 4) lv)))
      -> tr
           (hyp_tm (pi (var 2) (subst (under 1 (sh 3)) b)) ::
            hyp_tm (subtype (var 1) (mu (subst (under 1 (sh 2)) a))) ::
            hyp_tm a ::
            hyp_tm (univ lv) :: 
            G)
           (deq triv triv (subst (dot (var 2) (sh 4)) b))
      -> tr G (deq m m (mu a))
      -> tr G (deq triv triv (subst1 m b))
  
(* Positive/Negative *)

| tr_positive_algorithm :
    forall G a P N,
      hpositive P N 0 a
      -> (forall b,
            In b P
            -> tr G (deq triv triv (ispositive b)))
      -> (forall b,
            In b N
            -> tr G (deq triv triv (isnegative b)))
      -> tr G (deq triv triv (ispositive a))

| tr_positive_eta :
    forall G a p,
      tr G (deq p p (ispositive a))
      -> tr G (deq p triv (ispositive a))

| tr_negative_algorithm :
    forall G a P N,
      hnegative P N 0 a
      -> (forall b,
            In b P
            -> tr G (deq triv triv (ispositive b)))
      -> (forall b,
            In b N
            -> tr G (deq triv triv (isnegative b)))
      -> tr G (deq triv triv (isnegative a))

| tr_negative_eta :
    forall G a p,
      tr G (deq p p (isnegative a))
      -> tr G (deq p triv (isnegative a))

(* Equality *)

| tr_equal_formation :
    forall G a b m n p q,
      tr G (deqtype a b)
      -> tr G (deq m n a)
      -> tr G (deq p q a)
      -> tr G (deqtype (equal a m p) (equal b n q))

| tr_equal_formation_univ :
    forall G lv a b m n p q,
      tr G (deq a b (univ lv))
      -> tr G (deq m n a)
      -> tr G (deq p q a)
      -> tr G (deq (equal a m p) (equal b n q) (univ lv))
  
| tr_equal_intro :
    forall G a m n,
      tr G (deq m n a)
      -> tr G (deq triv triv (equal a m n))
  
| tr_equal_elim :
    forall G a m n,
      tr G (deq triv triv (equal a m n))
      -> tr G (deq m n a)
  
| tr_equal_eta :
    forall G a m n p,
      tr G (deq p p (equal a m n))
      -> tr G (deq p triv (equal a m n))

| tr_equal_eta_hyp :
    forall G1 G2 a p q m n b,
      tr (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
      -> tr (G2 ++ hyp_tm (equal a p q) :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b)

| tr_equal_formation_invert1 :
    forall G a a' m m' n n',
      tr G (deqtype (equal a m n) (equal a' m' n'))
      -> tr G (deqtype a a')

| tr_equal_formation_invert1_univ :
    forall G lv a a' m m' n n',
      tr G (deq (equal a m n) (equal a' m' n') (univ lv))
      -> tr G (deq a a' (univ lv))

| tr_equal_formation_invert2 :
    forall G a a' m m' n n',
      tr G (deqtype (equal a m n) (equal a' m' n'))
      -> tr G (deq m m' a)

| tr_equal_formation_invert3 :
    forall G a a' m m' n n',
      tr G (deqtype (equal a m n) (equal a' m' n'))
      -> tr G (deq n n' a)

(* Set Types *)

| tr_set_formation :
    forall G a a' b b' mr ml,
      tr G (deqtype a a')
      -> tr (cons (hyp_tm a) G) (deqtype b b)
      -> tr (cons (hyp_tm a) G) (deqtype b' b')
      (* b implies b' *)
      -> tr (hyp_tm b :: hyp_tm a :: G)
           (deq mr mr (subst sh1 b'))
      (* b' implies b *)
      -> tr (hyp_tm b' :: hyp_tm a :: G)
           (deq ml ml (subst sh1 b))
      -> tr G (deqtype (set a b) (set a' b'))
  
| tr_set_formation_univ :
    forall G lv a a' b b' mr ml,
      tr G (deq a a' (univ lv))
      -> tr (cons (hyp_tm a) G) (deq b b (univ (subst sh1 lv)))
      -> tr (cons (hyp_tm a) G) (deq b' b' (univ (subst sh1 lv)))
      (* b implies b' *)
      -> tr (hyp_tm b :: hyp_tm a :: G)
           (deq mr mr (subst sh1 b'))
      (* b' implies b *)
      -> tr (hyp_tm b' :: hyp_tm a :: G)
           (deq ml ml (subst sh1 b))
      -> tr G (deq (set a b) (set a' b') (univ lv))
  
| tr_set_intro :
    forall G a b m n p,
      tr G (deq m n a)
      -> tr G (deq p p (subst1 m b))
      -> tr (hyp_tm a :: G) (deqtype b b)
      -> tr G (deq m n (set a b))
  
| tr_set_elim1 :
    forall G a b m n,
      tr G (deq m n (set a b))
      -> tr G (deq m n a)
  
| tr_set_elim2 :
    forall G a b m J,
      tr G (deq m m (set a b))
      -> tr (hyp_tm a :: G) (deqtype b b)
      -> tr (hyp_tm (subst1 m b) :: G) (substj sh1 J)
      -> tr G J
  
| tr_set_hyp_weaken :
    forall G1 G2 a b J,
      tr (G2 ++ hyp_tm b :: hyp_tm a :: G1) J
      -> tr (G2 ++ hyp_tm b :: hyp_tm (set a b) :: G1) J
  
| tr_set_formation_invert :
    forall G a a' b b',
      tr G (deqtype (set a b) (set a' b'))
      -> tr G (deqtype a a')

| tr_iset_formation :
    forall G a a' b b',
      tr G (deqtype a a')
      -> tr (cons (hyp_tm a) G) (deqtype b b')
      -> tr G (deqtype (iset a b) (iset a' b'))
  
| tr_iset_formation_univ :
    forall G lv a a' b b',
      tr G (deq a a' (univ lv))
      -> tr (cons (hyp_tm a) G) (deq b b' (univ (subst sh1 lv)))
      -> tr G (deq (iset a b) (iset a' b') (univ lv))
  
| tr_iset_intro :
    forall G a b m n p,
      tr G (deq m n a)
      -> tr G (deq p p (subst1 m b))
      -> tr (hyp_tm a :: G) (deqtype b b)
      -> tr G (deq m n (iset a b))
  
| tr_iset_elim1 :
    forall G a b m n,
      tr G (deq m n (iset a b))
      -> tr G (deq m n a)
  
| tr_iset_elim2 :
    forall G a b m J,
      tr G (deq m m (iset a b))
      -> tr (hyp_tm (subst1 m b) :: G) (substj sh1 J)
      -> tr G J
  
| tr_iset_hyp_weaken :
    forall G1 G2 a b J,
      tr (G2 ++ hyp_tm b :: hyp_tm a :: G1) J
      -> tr (G2 ++ hyp_tm b :: hyp_tm (iset a b) :: G1) J
  
| tr_iset_formation_invert1 :
    forall G a a' b b',
      tr G (deqtype (iset a b) (iset a' b'))
      -> tr G (deqtype a a')

| tr_iset_formation_invert2 :
    forall G a a' b b',
      tr G (deqtype (iset a b) (iset a' b'))
      -> tr (cons (hyp_tm a) G) (deqtype b b')

| tr_squash_idem :
    forall G a b,
      tr G (deqtype (set a b) (set a b))
      -> tr G (deqtype (set a b) (set a (squash b)))

(* Quotient types *)

| tr_quotient_formation :
    forall G a a' b b' mr ml ms mt,
      tr G (deqtype a a')
      -> tr (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deqtype b b)
      -> tr (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deqtype b' b')
      (* b implies b' *)
      -> tr (hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)
           (deq mr mr (subst sh1 b'))
      (* b' implies b *)
      -> tr (hyp_tm b' :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)
           (deq ml ml (subst sh1 b))
      (* symmetry *)
      -> tr (hyp_tm b ::
             hyp_tm (subst sh1 a) ::
             hyp_tm a :: 
             G) 
           (deq ms ms (subst (dot (var 2) (dot (var 1) (sh 3))) b))
      (* transitivity *)
      -> tr (hyp_tm (subst (dot (var 1) (dot (var 2) (sh 4))) b) :: 
             hyp_tm (subst sh1 b) ::
             hyp_tm (subst (sh 2) a) :: 
             hyp_tm (subst sh1 a) :: 
             hyp_tm a :: 
             G)
           (deq mt mt (subst (dot (var 2) (dot (var 4) (sh 5))) b))
      -> tr G (deqtype (quotient a b) (quotient a' b'))
  
| tr_quotient_formation_univ :
    forall G lv a a' b b' mr ml ms mt,
      tr G (deq a a' (univ lv))
      -> tr (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deq b b (univ (subst (sh 2) lv)))
      -> tr (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deq b' b' (univ (subst (sh 2) lv)))
      (* b implies b' *)
      -> tr (hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)
           (deq mr mr (subst sh1 b'))
      (* b' implies b *)
      -> tr (hyp_tm b' :: hyp_tm (subst sh1 a) :: hyp_tm a :: G)
           (deq ml ml (subst sh1 b))
      (* symmetry *)
      -> tr (hyp_tm b ::
              hyp_tm (subst sh1 a) ::
              hyp_tm a :: 
              G) 
           (deq ms ms (subst (dot (var 2) (dot (var 1) (sh 3))) b))
      (* transitivity *)
      -> tr (hyp_tm (subst (dot (var 1) (dot (var 2) (sh 4))) b) :: 
              hyp_tm (subst sh1 b) ::
              hyp_tm (subst (sh 2) a) :: 
              hyp_tm (subst sh1 a) :: 
              hyp_tm a :: 
              G)
           (deq mt mt (subst (dot (var 2) (dot (var 4) (sh 5))) b))
      -> tr G (deq (quotient a b) (quotient a' b') (univ lv))
  
| tr_quotient_intro :
    forall G a b m n p,
      tr G (deqtype (quotient a b) (quotient a b))
      -> tr G (deq m m a)
      -> tr G (deq n n a)
      -> tr G (deq p p (subst (dot n (dot m id)) b))
      -> tr G (deq m n (quotient a b))
  
| tr_quotient_elim :
    forall G a b c m n p q,
      tr G (deq m n (quotient a b))
      -> tr (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deqtype b b)
      -> tr (hyp_tm (quotient a b) :: G) (deqtype c c)
      -> tr (hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deq (subst (sh 2) p) (subst (dot (var 1) (sh 3)) q) (subst (sh 2) c))
      -> tr G (deq (subst1 m p) (subst1 n q) (subst1 m c))
  
| tr_quotient_elim_eqtype :
    forall G a b m n c d,
      tr G (deq m n (quotient a b))
      -> tr (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deqtype b b)
      -> tr (hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deqtype (subst (sh 2) c) (subst (dot (var 1) (sh 3)) d))
      -> tr G (deqtype (subst1 m c) (subst1 n d))

| tr_descent :
    forall G a b c m n p,
      tr G (deq m m a)
      -> tr G (deq n n a)
      -> tr G (deq m n (quotient a b))
      -> tr (hyp_tm (subst sh1 a) :: hyp_tm a :: G) (deqtype b b)
      -> tr G (deqtype c c)
      -> tr (hyp_tm (subst (dot n (dot m id)) b) :: G) (deq (subst sh1 p) (subst sh1 p) (subst sh1 c))
      -> tr G (deq p p c)

| tr_quotient_hyp :
    forall G1 G2 a b m n c,
      tr (G2 ++ hyp_tm (quotient a b) :: G1) (deqtype c c)
      -> tr (G2 ++ hyp_tm a :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) c)
      -> tr (G2 ++ hyp_tm (quotient a b) :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) c)

| tr_quotient_hyp_with_refl :
    forall G1 G2 a b m n c,
      tr (hyp_tm (subst sh1 a) :: hyp_tm a :: G1) (deqtype b b)
      -> tr (G2 ++ hyp_tm (quotient a b) :: G1) (deqtype c c)
      -> tr 
           (substctx sh1 G2 ++ hyp_tm (subst (dot (var 0) (dot (var 0) sh1)) b) :: hyp_tm a :: G1)
           (deq
              (subst (under (length G2) (sh 2)) m)
              (subst (under (length G2) (sh 2)) n)
              (subst (under (length G2) sh1) c))
      -> tr (G2 ++ hyp_tm (quotient a b) :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) c)

| tr_quotient_hyp_eqtype :
    forall G1 G2 a b c d,
      tr (hyp_tm (subst sh1 a) :: hyp_tm a :: G1) (deqtype b b)
      -> tr (substctx (sh 2) G2 ++ hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G1) (deqtype (subst (under (length G2) (sh 2)) c) (subst (under (length G2) (dot (var 1) (sh 3))) d))
      -> tr (G2 ++ hyp_tm (quotient a b) :: G1) (deqtype c d)

| tr_quotient_hyp_eq :
    forall G1 G2 a b c m n,
      tr (hyp_tm (subst sh1 a) :: hyp_tm a :: G1) (deqtype b b)
      -> tr 
           (substctx (sh 2) G2 ++ hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G1)
           (deq
              (subst (under (length G2) (sh 2)) m)
              (subst (under (length G2) (dot (var 1) (sh 3))) n)
              (subst (under (length G2) (sh 3)) c))
      -> tr (G2 ++ hyp_tm (quotient a b) :: G1) (deq m n (subst (under (length G2) sh1) c))

| tr_quotient_hyp_eq_dep :
    forall G1 G2 a b c m n,
      tr (hyp_tm (subst sh1 a) :: hyp_tm a :: G1) (deqtype b b)
      -> tr 
           (substctx (sh 2) G2 ++ hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G1) 
           (deqtype
              (subst (under (length G2) (sh 2)) c)
              (subst (under (length G2) (dot (var 1) (sh 3))) c))
      -> tr 
           (substctx (sh 2) G2 ++ hyp_tm b :: hyp_tm (subst sh1 a) :: hyp_tm a :: G1)
           (deq
              (subst (under (length G2) (sh 2)) m)
              (subst (under (length G2) (dot (var 1) (sh 3))) n)
              (subst (under (length G2) (sh 2)) c))
      -> tr (G2 ++ hyp_tm (quotient a b) :: G1) (deq m n c)

| tr_quotient_formation_invert :
    forall G a a' b b',
      tr G (deqtype (quotient a b) (quotient a' b'))
      -> tr G (deqtype a a')

(* Guarded types *)

| tr_guard_formation :
    forall G a a' b b',
      tr G (deqtype a a')
      -> tr (cons (hyp_tm a) G) (deqtype (subst sh1 b) (subst sh1 b'))
      -> tr G (deqtype (guard a b) (guard a' b'))
  
| tr_guard_formation_univ :
    forall G lv a a' b b',
      tr G (deq a a' (univ lv))
      -> tr (cons (hyp_tm a) G) (deq (subst sh1 b) (subst sh1 b') (univ (subst sh1 lv)))
      -> tr G (deq (guard a b) (guard a' b') (univ lv))
  
| tr_guard_sat_eq :
    forall G a b m n,
      tr G (deq m n a)
      -> tr G (deqtype b b)
      -> tr G (deqtype b (guard a b))
  
| tr_guard_intro :
    forall G a b m n,
      tr G (deqtype a a)
      -> tr (hyp_tm a :: G) (deq (subst sh1 m) (subst sh1 n) (subst sh1 b))
      -> tr G (deq m n (guard a b))
  
| tr_guard_elim :
    forall G a b m n p q,
      tr G (deq m n (guard a b))
      -> tr G (deq p q a)
      -> tr G (deq m n b)

(* Universes *)

| tr_univ_kind_formation :
    forall G lv lv1 lv2,
      tr G (deq lv1 lv2 pagetp)
      -> tr G (deq lv1 lv pagetp)
      -> tr G (deq (univ lv1) (univ lv2) (kuniv lv))

| tr_univ_formation :
    forall G lv lv',
      tr G (deq lv lv' pagetp)
      -> tr G (deqtype (univ lv) (univ lv'))

| tr_univ_formation_univ :
    forall G lv lv1 lv2,
      tr G (deq lv1 lv2 pagetp)
      -> tr G (deq lv lv pagetp)
      -> tr G (deq triv triv (ltpagetp lv1 lv))
      -> tr G (deq (univ lv1) (univ lv2) (univ lv))

| tr_univ_cumulative :
    forall G lv lv' a b,
      tr G (deq a b (univ lv))
      -> tr G (deq lv' lv' pagetp)
      -> tr G (deq triv triv (leqpagetp lv lv'))
      -> tr G (deq a b (univ lv'))

| tr_formation_weaken :
    forall G lv a b,
      tr G (deq a b (univ lv))
      -> tr G (deqtype a b)

| tr_formation_strengthen :
    forall G lv a b,
      tr G (deqtype a b)
      -> tr G (deq a a (univ lv))
      -> tr G (deq b b (univ lv))
      -> tr G (deq a b (univ lv))

| tr_univ_formation_invert :
    forall G lv lv',
      tr G (deqtype (univ lv) (univ lv'))
      -> tr G (deq lv lv' pagetp)

(* Kind universes *)

| tr_kuniv_formation :
    forall G lv lv',
      tr G (deq lv lv' pagetp)
      -> tr G (deqtype (kuniv lv) (kuniv lv'))
  
| tr_kuniv_formation_univ :
    forall G lv lv1 lv2,
      tr G (deq lv1 lv2 pagetp)
      -> tr G (deq lv lv pagetp)
      -> tr G (deq triv triv (ltpagetp (nsucc lv1) lv))
      -> tr G (deq (kuniv lv1) (kuniv lv2) (univ lv))
  
| tr_kuniv_weaken :
    forall G lv a b,
      tr G (deq a b (kuniv lv))
      -> tr G (deq a b (univ (nsucc lv)))

| tr_kuniv_formation_invert :
    forall G lv lv',
      tr G (deqtype (kuniv lv) (kuniv lv'))
      -> tr G (deq lv lv' pagetp)

(* Type equality *)

| tr_eqtype_formation :
    forall G a a' b b',
      tr G (deqtype a a')
      -> tr G (deqtype b b')
      -> tr G (deqtype (eqtype a b) (eqtype a' b'))
  
| tr_eqtype_formation_univ :
    forall G lv a a' b b',
      tr G (deq a a' (univ lv))
      -> tr G (deq b b' (univ lv))
      -> tr G (deq (eqtype a b) (eqtype a' b') (univ lv))

| tr_eqtype_convert :
    forall G m n a b,
      tr G (deqtype a b)
      -> tr G (deq m n a)
      -> tr G (deq m n b)
  
| tr_eqtype_convert_hyp :
    forall G1 G2 a b J,
      tr G1 (deqtype a b)
      -> tr (G2 ++ hyp_tm b :: G1) J
      -> tr (G2 ++ hyp_tm a :: G1) J

| tr_eqtype_symmetry :
    forall G a b,
      tr G (deqtype a b)
      -> tr G (deqtype b a)
  
| tr_eqtype_transitivity :
    forall G a b c,
      tr G (deqtype a b)
      -> tr G (deqtype b c)
      -> tr G (deqtype a c)
  
| tr_eqtype_eta :
    forall G a b p,
      tr G (deq p p (eqtype a b))
      -> tr G (deq p triv (eqtype a b))

| tr_eqtype_eta_hyp :
    forall G1 G2 a a' m n b,
      tr (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
      -> tr (G2 ++ hyp_tm (eqtype a a') :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b)

| tr_eqtype_formation_invert1 :
    forall G a a' b b',
      tr G (deqtype (eqtype a b) (eqtype a' b'))
      -> tr G (deqtype a a')

| tr_eqtype_formation_invert2 :
    forall G a a' b b',
      tr G (deqtype (eqtype a b) (eqtype a' b'))
      -> tr G (deqtype b b')

(* Subtyping *)

| tr_subtype_formation :
    forall G a a' b b',
      tr G (deqtype a a')
      -> tr G (deqtype b b')
      -> tr G (deqtype (subtype a b) (subtype a' b'))
  
| tr_subtype_formation_univ :
    forall G lv a a' b b',
      tr G (deq a a' (univ lv))
      -> tr G (deq b b' (univ lv))
      -> tr G (deq (subtype a b) (subtype a' b') (univ lv))
  
| tr_subtype_intro :
    forall G a b,
      tr G (deqtype a a)
      -> tr G (deqtype b b)
      -> tr (hyp_tm a :: G) (deq (var 0) (var 0) (subst sh1 b))
      -> tr G (deq triv triv (subtype a b))
  
| tr_subtype_elim :
    forall G a b m n,
      tr G (deq triv triv (subtype a b))
      -> tr G (deq m n a)
      -> tr G (deq m n b)
  
| tr_subtype_eta :
    forall G a b p,
      tr G (deq p p (subtype a b))
      -> tr G (deq p triv (subtype a b))
  
| tr_subtype_eta_hyp :
    forall G1 G2 a a' m n b,
      tr (substctx (dot triv id) G2 ++ G1) (deq m n (subst (under (length G2) (dot triv id)) b))
      -> tr (G2 ++ hyp_tm (subtype a a') :: G1) (deq (subst (under (length G2) sh1) m) (subst (under (length G2) sh1) n) b)
  
| tr_subtype_convert_hyp :
    forall G1 G2 a b J,
      tr (cons (hyp_tm (eqtype a a)) G1) (dsubtype (subst sh1 a) (subst sh1 b))
      -> tr (cons (hyp_tm (eqtype a a)) G1) (dsubtype (subst sh1 b) (subst sh1 a))
      -> tr (G2 ++ hyp_tm b :: G1) J
      -> tr (G2 ++ hyp_tm a :: G1) J

| tr_subtype_formation_invert1 :
    forall G a a' b b',
      tr G (deqtype (subtype a b) (subtype a' b'))
      -> tr G (deqtype a a')

| tr_subtype_formation_invert2 :
    forall G a a' b b',
      tr G (deqtype (subtype a b) (subtype a' b'))
      -> tr G (deqtype b b')

(* Substitution *)

| tr_substitution :
    forall G1 G2 a m n n' b,
      tr (G2 ++ cons (hyp_tm a) G1) (deqtype b b)
      -> tr (G2 ++ cons (hyp_tm a) G1) (deq (var (length G2)) (subst (sh (S (length G2))) m) (subst (sh (S (length G2))) a))
      -> tr (substctx (dot m id) G2 ++ G1) (deq n n' (subst (under (length G2) (dot m id)) b))
      -> tr (G2 ++ cons (hyp_tm a) G1) (deq (subst (under (length G2) sh1) n) (subst (under (length G2) sh1) n') b)
  
| tr_substitution_simple :
    forall G1 G2 a m n n' b,
      tr (G2 ++ cons (hyp_tm a) G1) (deq (var (length G2)) (subst (sh (S (length G2))) m) (subst (sh (S (length G2))) a))
      -> tr (substctx (dot m id) G2 ++ G1) (deq n n' b)
      -> tr (G2 ++ cons (hyp_tm a) G1) (deq (subst (under (length G2) sh1) n) (subst (under (length G2) sh1) n') (subst (under (length G2) sh1) b))
  
| tr_strengthen_context :
    forall G1 G2 a b J,
      tr G1 (deqtype a a)
      -> tr (G2 ++ hyp_tm b :: G1) (dsubtype (subst (sh (S (length G2))) a) (subst (sh (S (length G2))) b))
      -> tr (G2 ++ hyp_tm b :: G1) (deq (var (length G2)) (var (length G2)) (subst (sh (S (length G2))) a))
      -> tr (G2 ++ hyp_tm a :: G1) J
      -> tr (G2 ++ hyp_tm b :: G1) J

| tr_generalize :
    forall G a m J,
      tr G (deq m m a)
      -> tr (cons (hyp_tm a) G) J
      -> tr G (substj (dot m id) J)

| tr_generalize_tp :
    forall G a J,
      tr G (deqtype a a)
      -> tr (cons hyp_tp G) J
      -> tr G (substj (dot a id) J)

| tr_generalize_eq :
    forall G a b m n p q,
      tr G (deq m n a)
      -> tr (cons (hyp_tm a) G) (deq p q b)
      -> tr G (deq (subst1 m p) (subst1 n q) (subst1 m b))

| tr_generalize_eq_type :
    forall G a b m n p q,
      tr G (deq m n a)
      -> tr (cons (hyp_tm a) G) (deq p q b)
      -> tr G (deqtype (subst1 m b) (subst1 n b))


(* Direct computation *)

| tr_compute :
    forall G a a' m m' n n',
      equiv a a'
      -> equiv m m'
      -> equiv n n'
      -> tr G (deq m' n' a')
      -> tr G (deq m n a)

| tr_compute_hyp :
    forall G1 G2 h h' J,
      equivh h h'
      -> tr (G2 ++ cons h' G1) J
      -> tr (G2 ++ cons h G1) J

(* Structural rules *)

| tr_symmetry :
    forall G m n a,
      tr G (deq m n a)
      -> tr G (deq n m a)
  
| tr_transitivity :
    forall G m n p a,
      tr G (deq m n a)
      -> tr G (deq n p a)
      -> tr G (deq m p a)
  
| tr_weakening :
    forall G1 G2 h J,
      tr (G2 ++ G1) J
      -> tr (substctx sh1 G2 ++ cons h G1) (substj (under (length G2) sh1) J)
  
| tr_contraction :
    forall G1 G2 h i m m' a,
      index i G1 h
      -> tr (substctx sh1 G2 ++ substh (sh (S i)) h :: G1) (deq m m' (subst (under (length G2) sh1) a))
      -> tr (G2 ++ G1) (deq (subst (under (length G2) (dot (var i) id)) m) (subst (under (length G2) (dot (var i) id)) m') a)
  
| tr_exchange :
    forall G1 G2 h1 h2 m m' a,
      tr (substctx (dot (var 1) (dot (var 0) (sh 2))) G2 ++ substh sh1 h1 :: h2 :: G1) (deq m m' (subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2)))) a))
      -> tr (G2 ++ substh sh1 h2 :: h1 :: G1) (deq (subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2)))) m) (subst (under (length G2) (dot (var 1) (dot (var 0) (sh 2)))) m') a)

(* Miscellaneous rules *)

| tr_inhabitation_formation :
    forall G m n a,
      tr G (deq m n a)
      -> tr G (deqtype a a)
.
