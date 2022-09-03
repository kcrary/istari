
Require Import Tactics.


(* Misc *)

Tactic Notation "isapp" constr(t) := (match t with context [_ _] => idtac end).


Ltac last_hyp k
  :=
  (lazymatch goal with
   | H:_ |- _ => k H
   end).


Ltac findhyp T :=
  lazymatch goal with
  | H : context [T _] |- _ => constr:(H)
  end.
  

Local Ltac headvar t :=
  (lazymatch t with
   | ?f _ => headvar f
   | _ => t
   end).

Tactic Notation "unfoldtop" hyp(H) :=
  let t := headvar ltac:(type of H)
  in
    unfold t in H.


Declare Reduction unf := lazy delta.


Tactic Notation "complete" tactic(tac)
  :=
  solve [tac].


Tactic Notation "eassert" constr(T)
  :=
  evargen T ltac:(fun X => assert X).


Tactic Notation "eassert" constr(T) "as" ident(H)
  :=
  evargen T ltac:(fun X => assert X as H).





(* Proof labels *)

Tactic Notation "toshow" constr(P)
  :=
  (lazymatch goal with
   | |- P => idtac
   | |- ?Q => (lazymatch eval compute in P with
               | ?P' => (lazymatch eval compute in Q with
                         | P' => idtac
                         | _ => fail "conclusion does not match specification"
                         end)
               end)
   end).

Tactic Notation "have" constr(P) "as" hyp(H)
  :=
  (match type of H with
   | P => idtac
   | ?Q => (lazymatch eval compute in P with
            | ?P' => (lazymatch eval compute in Q with
                      | P' => idtac
                      | _ => fail 1 "hypothesis does not match specification"
                      end)
            end)
   end).


(* Nat calculation *)

Ltac simplify_nat t :=
  let rec scan acc t :=
    (lazymatch t with
     | 0 =>
         acc
     | S ?t1 =>
         let acc' :=
           (lazymatch acc with
            | ?n + ?tacc => constr:(S n + tacc)
            | ?n => constr:(S n)
            end)
         in
           scan acc' t1
     | ?t1 + ?t2 =>
         let acc' := scan acc t1
         in
           scan acc' t2
     | _ =>
         (lazymatch acc with
          | ?n + ?tacc => constr:(n + (tacc + t))
          | ?n => constr:(n + t)
          end)
     end)
  in
  let t' :=
    (lazymatch scan 0 t with
     | 0 + ?tacc => tacc
     | ?acc => acc
     end)
  in
    t'.


Ltac find_nat f t :=
  (match t with
   | 0 => fail
   | S _ => progress (f t)
   | _ + _ => progress (f t)
   | ?t1 ?t2 =>
       first [ find_nat f t1 | find_nat f t2 ]
   end).


Ltac calculate :=
  let simpit t' := let t'' := simplify_nat t'
                   in
                     replace t' with t'' by omega
  in
  (match goal with 
   | |- ?t => find_nat simpit t
   end).


Tactic Notation "calculate" "in" hyp(H)
  := 
  let simpit t' := let t'' := simplify_nat t'
                   in
                     replace t' with t'' in H by omega
  in
  (match goal with
   | H : ?t |- _ => find_nat simpit t
   end).


(* Better replace *)

Tactic Notation "repl" constr(t) "with" constr(t') :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [| rewrite <- Heq; clear Heq].

Tactic Notation "repl" constr(t) "with" constr(t') "in" hyp(H) :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [| rewrite <- Heq in H; clear Heq].

Tactic Notation "repl" constr(t) "with" constr(t') "at" ne_integer_list(l) :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [| rewrite <- Heq at l; clear Heq].

Tactic Notation "repl" constr(t) "with" constr(t') "in" hyp(H) "at" ne_integer_list(l) :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [| rewrite <- Heq in H at l; clear Heq].

Tactic Notation "repl" constr(t) "with" constr(t') "by" tactic(tac) :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [solve [tac] | rewrite <- Heq; clear Heq].

Tactic Notation "repl" constr(t) "with" constr(t') "in" hyp(H) "by" tactic(tac) :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [solve [tac] | rewrite <- Heq in H; clear Heq].

Tactic Notation "repl" constr(t) "with" constr(t') "at" ne_integer_list(l) "by" tactic(tac) :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [solve [tac] | rewrite <- Heq at l; clear Heq].

Tactic Notation "repl" constr(t) "with" constr(t') "in" hyp(H) "at" ne_integer_list(l) "by" tactic(tac) :=
  let Heq := fresh
  in
    assert (t' = t) as Heq; [solve [tac] | rewrite <- Heq in H at l; clear Heq].


(* Notation *)

Definition tuple2 {T : Type} {A B : Set} :=
  fun (f : A -> B -> T) x => f (car x) (cdr x).

Definition tuple3 {T : Type} {A B C : Set} :=
  fun (f : A -> B -> C -> T) x => f (caar x) (cdar x) (cdr x).

Definition tuple4 {T : Type} {A B C D : Set} :=
  fun (f : A -> B -> C -> D -> T) x => f (caaar x) (cdaar x) (cdar x) (cdr x).

Definition tuple22 {T : Type} {A B C D : Set} :=
  fun (f : A -> B -> C -> D -> T) x => f (caar x) (cdar x) (cadr x) (cddr x).

Definition swapp {P Q : Prop} (x : P \/ Q) : (Q \/ P).
Proof.
destruct x as [y | z].
  right; assumption.

  left; assumption.
Qed.


(* Sor *)

Tactic Notation "sor" tactic(tac)
  :=
  eassert Prop; [tac |].


Tactic Notation "sor" tactic(tac) "as" simple_intropattern(pat)
  :=
  let H := fresh
  in
    eassert Prop as H; [tac | so H as pat; clear H].
