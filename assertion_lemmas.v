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

Global Infix "+" := (Eplus) : exp_scope.
Global Infix "<" := (Blt) : bexp_scope.
Global Infix "==" := (Beq) : bexp_scope.

Notation nosimpl t := (let tt := tt in t).

Definition assn := stack -> pheap -> Prop.
(* empty *)
Definition Aemp : assn := (nosimpl (fun (s : stack) (ph : pheap) => forall x, this ph x = None)).
Notation emp := Aemp.
(* separate conjunction *)
Definition Astar (P1 P2 : assn) : assn := (nosimpl (fun (s : stack) (ph : pheap) => 
  exists (ph1 ph2 : pheap), P1 s ph1 /\ P2 s ph2 /\ pdisj ph1 ph2 /\ phplus ph1 ph2 = ph)).
Notation "P1 ** P2" := (Astar P1 P2) (at level 70, right associativity).
(* conjunction *)
Definition Aconj (P1 P2 : assn) : assn := (nosimpl (fun (s : stack) (ph : pheap) => P1 s ph /\ P2 s ph)).
Notation "P '//\\' Q" := (Aconj P Q) (at level 80, right associativity).
Definition Adisj (P1 P2 : assn) : assn := (nosimpl (fun (s : stack) (ph : pheap) => P1 s ph \/ P2 s ph)).
Notation "P '\\//' Q" := (Adisj P Q) (at level 85, right associativity).
Definition Apure (p : Prop) := (nosimpl (fun (s : stack) (ph : pheap) => p)).
Notation pure p := (Apure p).
Definition Apointsto (p : Qc) (e1 : _exp) (e2 : exp) := (nosimpl (fun (s : stack) (ph : pheap) =>
  forall x, this ph x = if loc_eq_dec x (ledenot e1 s) then Some (p, edenot e2 s) else None)).
Notation "e1 '-->sh' ( p ,  e2 )" := (Apointsto p e1 e2) (at level 75).
Definition ban (P : assn) := (nosimpl (emp //\\ P)).
Notation "!( P )" := (ban P).
Definition eeq (x y : exp) := (nosimpl (fun s (h : pheap) => edenot x s = edenot y s)).
Notation "x '===' y" := (eeq x y) (at level 70, no associativity).
Definition AEx {T : Type} (Px : T -> assn) := (nosimpl (fun s h => ex (fun x => Px x s h))).
Notation "'Ex' x .. y , p" := (AEx (fun x => .. (AEx (fun y => p)) ..))
  (at level 200, x binder, right associativity).                               
Definition subA' (x : var) (e : exp) (P : assn) := (nosimpl (fun (s : stack) (h : pheap) => P (var_upd s x (edenot e s)) h)).
Notation subA x e P := (subA' x e P).

Definition bexp_to_assn (b : bexp) : assn := fun s h => bdenot b s = true.
Coercion bexp_to_assn : bexp >-> assn.

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

Ltac unfold_conn_all :=
  unfold Aemp, Astar, Aconj, Adisj, Apure, Apointsto, ban, eeq, bexp_to_assn in *.

Ltac unfold_conn_in1 H :=
  unfold Aemp, Astar, Aconj, Adisj, Apure, Apointsto, ban, eeq, bexp_to_assn in H.
Ltac unfold_conn_in H :=
  match H with
    | (?Hs, ?H) => unfold_conn_in Hs; unfold_conn_in1 H
    | _ => unfold_conn_in1 H
  end.

Ltac unfold_conn :=
     unfold Aemp, Astar, Aconj, Adisj, Apure, Apointsto, ban, eeq, bexp_to_assn.

Notation "P |= Q" := (forall s h, P s h -> Q s h) (at level 87).

Section Precise.
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
End Precise.

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

Lemma sc_emp1 (P : assn) : P |= (emp ** P).
Proof.
  unfold_conn; intros s h H.
  exists emp_ph, h; repeat split; simpl; auto.
Qed.
Hint Resolve phplus_emp1 phplus_emp2 pdisj_empty2.
Lemma sc_emp2 (P : assn) : P |= (P ** emp).
Proof.
  unfold_conn; intros s h H.
  exists h, emp_ph; repeat split; simpl; auto.
Qed.

Lemma scEx {T : Type} (P Q : T -> assn) : (forall x, (P x) |= (Q x)) -> (Ex x, P x) |= (Ex x, Q x).
Proof.
  intros H s h [x Hp]; simpl in *.
  eexists; apply H; eauto.
Qed.  

Lemma scC (P Q : assn) : (P ** Q) |= (Q ** P).
Proof.
  unfold_conn; intros s h (phP & phQ & Hp & Hq & Hdis & Heq).
  exists phQ, phP; repeat split; auto.
  rewrite phplus_comm; auto.
Qed.

Lemma emp_emp_ph_eq s h : emp s h -> h = emp_ph.
Proof.
  intros H; unfold emp in *.
  destruct h as [h ?]; unfold emp_ph; apply pheap_eq; extensionality x; auto.
Qed.

Lemma scban_r (P Q : assn) s h:  P s h -> Q s emp_ph -> (P ** !(Q)) s h.
Proof.  
  intros Hp Hq.
  unfold "**"; repeat eexists; eauto.
  apply emp_emp_ph.
Qed.

Lemma scban_r' (P Q : assn) s h: (P ** !(Q)) s h -> P s h /\ Q s emp_ph.
Proof.  
  intros (phP & phQ & Hp & (Hemp & Hq) & Hdis & Heq); split; auto.
  assert (H : phQ = emp_ph).
  { unfold emp in *; destruct phQ as [phQ ?]; unfold emp_ph; apply pheap_eq.
    extensionality x; rewrite Hemp; eauto. }
  rewrite H, phplus_emp2 in Heq.
  assert (phP = h) by (destruct phP, h; apply pheap_eq; simpl in *; auto); subst; auto.
  apply emp_emp_ph_eq in Hemp; rewrite <-Hemp; auto.
Qed.

Lemma scban_l (P Q : assn) s h: P s emp_ph -> Q s h -> (!(P) ** Q) s h.
Proof.  
  intros Hp Hq.
  unfold "**"; repeat eexists; eauto.
  apply emp_emp_ph.
Qed.

Lemma scban_l' (P Q : assn) s h: (!(P) ** Q) s h -> P s emp_ph /\ Q s h.
Proof.  
  intros (phP & phQ & (Hemp & Hp) & Hq & Hdis & Heq).
  assert (H : phP = emp_ph).
  { unfold emp in *; destruct phP as [phP ?]; unfold emp_ph; apply pheap_eq.
    extensionality x; rewrite Hemp; eauto. }
  split.
  - apply emp_emp_ph_eq in Hemp; rewrite <-Hemp; auto.
  - rewrite H, phplus_emp1 in Heq.
    assert (phQ = h) by (destruct phQ, h; apply pheap_eq; simpl in *; auto); subst; auto.
Qed.

Lemma sc_emp1' (P : assn) : (emp ** P) |= P.
Proof.
  intros s h (ph1 & ph2 & Hsat1 & Hsat2 & Hdis & Heq).
  assert (h = ph2).
  { destruct h, ph2; apply pheap_eq; simpl in *; rewrite <-Heq.
    unfold phplus; extensionality x.
    unfold_conn_all; rewrite Hsat1; auto. }
  rewrite H; auto.
Qed.

Lemma sc_emp2' (P : assn) : (P ** emp) |= P.
Proof.
  intros s h (ph1 & ph2 & Hsat1 & Hsat2 & Hdis & Heq).
  assert (h = ph1).
  { destruct h as [h ?], ph1 as [ph1 ?]; apply pheap_eq; simpl in *; rewrite <-Heq.
    unfold phplus; extensionality x.
    unfold_conn_all; rewrite Hsat2; destruct (ph1 x) as [[? ?]|]; auto. }
  rewrite H; auto.
Qed.

Lemma scA' (P Q R : assn) : (((P ** Q) ** R) |= (P ** Q ** R)).
Proof.
  unfold_conn; intros s h (ph0 & ph1 & ((ph2 & ph3 & Hp & Hq & Hdis & Heq) & Hr & Hdis' & Heq')).
  rewrite <-Heq in *.
  assert (Hdis02 : pdisj ph3 ph1). 
  { apply pdisjC in Hdis'; apply pdisjC; apply pdisj_padd in Hdis'; tauto. }
  exists ph2, (phplus_pheap Hdis02). repeat split; simpl; auto.
  exists ph3, ph1; repeat split; auto.
  apply pdisj_padd_expand; auto.
  rewrite <-padd_assoc; auto.
  apply pdisj_padd_expand; auto.
Qed.

Lemma scRw_stack (s : stack) (P Q P' Q' : assn) :
  (forall h, P s h -> P' s h) -> (forall h, Q s h -> Q' s h) ->
  (forall h, (P ** Q) s h -> (P' ** Q') s h).
Proof.
  intros Hp Hq h (? & ? & ? & ? & ? & ?).
  exists x, x0; split; firstorder.
Qed.

Lemma mapsto_rewrite1 (E1 E2 E3 : exp) (p : Qc) (s : stack) (h : pheap) :
  (E1 === E2) s emp_ph -> (E1 -->p (p, E3)) s h -> (E2 -->p (p, E3)) s h.
Proof.
  intros.
  unfold_conn_all; simpl in *.
  rewrite<-H.
  auto.
Qed.
  
Lemma mapsto_rewrite2 (E1 E2 E3 : exp) (p : Qc) (s : stack) (h : pheap) :
  (E2 === E3) s emp_ph -> (E1 -->p (p, E2)) s h -> (E1 -->p (p, E3)) s h.
Proof.
  intros.
  unfold_conn_all; simpl in *.
  rewrite<-H.
  auto.
Qed.

Lemma pure_emp (P : assn) s h : P s emp_ph -> emp s h -> !(P) s h.
Proof.
  unfold_conn_all; intros.
  split; unfold_conn; auto.
  assert (h = emp_ph).
  destruct h as [h ?]; apply pheap_eq; extensionality x; simpl in *; auto.
  rewrite H1; auto.
Qed.