Require Import QArith.
Require Import Qcanon.
Require Import MyVector.
Require Import List.
Require Import ZArith.

Require Import Lang PHeap.

Set Implicit Arguments.
Unset Strict Implicit.

Close Scope Qc_scope.
Close Scope Q_scope.

Bind Scope exp_scope with exp.
Bind Scope bexp_scope with bexp.

Infix "+" := (Eplus) : exp_scope.
Infix "<" := (Blt) : bexp_scope.
Infix "==" := (Beq) : bexp_scope.

Notation nosimpl t := (let tt := tt in t).

Definition assn := stack -> pheap -> Prop.
(* empty *)
Definition Aemp : assn := (nosimpl (fun (s : stack) (ph : pheap) => forall x, this ph x = None)).
Notation emp := Aemp.
(* separate conjunction *)
Definition Astar P1 P2 := (nosimpl (fun (s : stack) (ph : pheap) => 
  exists (ph1 ph2 : pheap), P1 s ph1 /\ P2 s ph2 /\ pdisj ph1 ph2 /\ phplus ph1 ph2 = ph)).
Notation "P1 ** P2" := (Astar P1 P2) (at level 70, right associativity).
(* conjunction *)
Definition Aconj P1 P2 := (nosimpl (fun (s : stack) (ph : pheap) => P1 s ph /\ P2 s ph)).
Notation "P '//\\' Q" := (Aconj P Q) (at level 80, right associativity).
Definition Adisj P1 P2 := (nosimpl (fun (s : stack) (ph : pheap) => P1 s ph \/ P2 s ph)).
Notation "P '\\//' Q" := (Adisj P Q) (at level 85, right associativity).
Definition Apure b := (nosimpl (fun (s : stack) (ph : pheap) => bdenot b s = true)).
Notation pure b := (Apure b).
Definition Apointsto p e1 e2 := (nosimpl (fun (s : stack) (ph : pheap) =>
  forall x, this ph x = if Z.eq_dec x (edenot e1 s) then Some (p, edenot e2 s) else None)).
Notation "e1 '-->p' ( p ,  e2 )" := (Apointsto p e1 e2) (at level 75).
Definition ban P := (nosimpl (emp //\\ P)).
Notation "!( P )" := (emp //\\ P).
Notation "x '===' y" := 
  (nosimpl (fun s h => edenot x s = edenot y s)) (at level 70, no associativity).

Delimit Scope assn_scope with assn.
Delimit Scope exp_scope with exp.

Fixpoint is_array (e : exp) (n : nat) (f : nat -> Z) :=
  match n with
    | 0 => Aemp
    | S n' => e + Enum (Z.of_nat n') -->p (1%Qc, Enum (f n')) **
                       is_array e n' f
  end.

Notation sat ss P := (P (fst ss) (snd ss)).

Bind Scope assn_scope with assn.

Notation nat_of_fin i := (proj1_sig (Fin.to_nat i)).
Notation Z_of_fin i := (Z.of_nat (nat_of_fin i)).

Ltac unfold_conn :=
  unfold Aemp, Astar, Aconj, Adisj, Apure, Apointsto, ban in *; simpl in *.

Definition precise (p : assn) :=
  forall (h1 h2 h1' h2' : pheap) s,
    sat (s, h1) p -> sat (s, h1') p ->
    pdisj h1 h2 -> pdisj  h1' h2' ->
    phplus h1 h2 = phplus h1' h2' ->
    h1 = h1'.

Lemma precise_emp : precise Aemp.
Proof.
  unfold_conn; red; intros h1 h2 h1' h2' s hsat hsat' hdis hdis' heq;
  destruct h1 as [h1 ?], h1' as [h1' ?]; apply pheap_eq; extensionality x; simpl in *;
  rewrite hsat, hsat'; eauto.
Qed.

Lemma precise_star (p q : assn) : precise p -> precise q -> precise (Astar p q).
Proof.
  unfold_conn; intros pp pq h1 h2 h1' h2' s hsat hsat' hdis hdis' heq; simpl in *.
  destruct hsat as [ph1 [ph1' [satp1 [satq1 [Hdis1 Heq1]]]]], 
                   hsat' as [ph2 [ph2' [satp2 [satq2 [Hdis2 Heq2]]]]].
  destruct h1 as [h1 ?], h1' as [h1' ?]; apply pheap_eq; simpl in *; rewrite <-Heq1, <-Heq2 in *.
  apply pdisj_padd_expand in hdis; apply pdisj_padd_expand in hdis'; eauto.
  rewrite !padd_assoc in heq; try tauto. 
  f_equal; destruct hdis as [hdis1 hdis2], hdis' as [hdis1' hdis2'].
  - rewrite (pp ph1 (phplus_pheap hdis2) ph2 (phplus_pheap hdis2') s); eauto.
  - rewrite padd_left_comm in heq at 1; try tauto.
    rewrite (@padd_left_comm ph2 ph2' h2') in heq; try tauto.
    pose proof (pdisjE2 hdis1 hdis2) as dis12; pose proof (pdisjE2 hdis1' hdis2') as dis12'.
    rewrite (pq ph1' (phplus_pheap dis12) ph2' (phplus_pheap dis12') s); simpl in *; eauto; 
    apply pdisj_padd_comm; eauto.
Qed.

Lemma emp_emp_ph (s : stack) : emp s emp_ph.
Proof.
  unfold_conn; eauto.
Qed.

Notation "P |= Q" := (forall s h, P s h -> Q s h) (at level 10).

Lemma scCA (P Q R : assn) : (P ** Q ** R) |= (Q ** P ** R).
Proof.
  unfold_conn; intros s h (ph0 & ph1 & Hp & ((ph2 & ph3 & Hq & Hr & Hdis & Heq) & Hdis' & Heq')).
  rewrite <-Heq in *; clear Heq.
  assert (pdisj ph0 ph3) by (apply pdisj_padd in Hdis'; tauto). 
  exists ph2, (phplus_pheap H); repeat split; simpl; auto.
  exists ph0, ph3; repeat split; eauto.
  rewrite padd_left_comm; eauto.
Qed.

Lemma scA (P Q R : assn) : ((P ** Q ** R) |= ((P ** Q) ** R)).
Proof.
  unfold_conn; intros s h (ph0 & ph1 & Hp & ((ph2 & ph3 & Hq & Hr & Hdis & Heq) & Hdis' & Heq')).
  rewrite <-Heq in *.
  assert (Hdis02 : pdisj ph0 ph2) by (apply pdisj_padd in Hdis'; tauto).
  exists (phplus_pheap Hdis02), ph3; repeat split; simpl; auto.
  exists ph0, ph2; repeat split; auto.
  apply pdisj_padd_expand; auto.
  rewrite padd_assoc; auto.
Qed.

Lemma scRw (P Q P' Q' : assn) : (P |= P') -> (Q |= Q') -> (P ** Q) |= (P' ** Q').
Proof.
  unfold_conn; intros Hpp Hqq s h (phP & phQ & Hp & Hq & Hdis & Heq).
  apply Hpp in Hp; apply Hqq in Hq; eexists; eauto.
Qed.  

Ltac last_sc :=
  match goal with
    | [ |- (?P ** ?R) ?s ?h ] =>
      eapply scRw; [intros ? ? H; exact H | intros ? ? H; last_sc; exact H | idtac];
      apply scA
    | _ => idtac
  end.

Ltac append_sc :=
  match goal with
    | [ |- ((?P ** ?Q) ** ?R) ?s ?h ] =>
      eapply scRw; [intros ? ? H; last_sc; exact H | intros ? ? H; exact H | idtac];
      apply scA; append_sc
    | [ |- _ ] => idtac
  end.

Ltac normalize_goal :=
  match goal with
    | [ |- (?P ** ?Q) ?s ?h] => 
      eapply scRw; [intros ? ? H; normalize_goal; exact H |
                    intros ? ? H; normalize_goal; exact H | idtac];
      append_sc
    | _ => idtac
  end.
      
Goal forall (P Q R S : assn) s h, (((P ** Q) ** R) ** (R ** S)) s h.
Proof.
  intros P Q R S s h. 
  normalize_goal.

  
