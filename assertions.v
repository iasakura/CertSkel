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
Definition AEx {T : Type} (Px : T -> assn) := (nosimpl (fun s h => ex (fun x => Px x s h))).
Notation "'Ex' x .. y , p" := (AEx (fun x => .. (AEx (fun y => p)) ..))
  (at level 200, x binder, right associativity).                               
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

Notation "P |= Q" := (forall s h, P s h -> Q s h) (at level 87).

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

Ltac last_slist :=
  let H := fresh "H" in
  match goal with
    | [ |- (?P ** ?R) ?s ?h ] =>
      eapply scRw; [intros ? ? H; exact H | intros ? ? H; last_slist; exact H | idtac];
      apply scA
    | _ => idtac
  end.

Ltac append_slist :=
  let H := fresh "H" in
  match goal with
    | [ |- ((?P ** ?Q) ** ?R) ?s ?h ] =>
      eapply scRw; [intros ? ? H; last_slist; exact H | intros ? ? H; exact H | idtac];
      apply scA; append_slist
    | [ |- _ ] => idtac
  end.

Ltac test_ex :=
  match goal with
    | [ |- exists x, ?P] => idtac P
  end.

Goal exists x, x + 1 = 10.
test_ex.
Abort.

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

Ltac sep_normal :=
  let H := fresh "H" in
  match goal with
    | [ |- (emp ** ?P) ?s ?h ] => apply sc_emp1; sep_normal 
    | [ |- (?P ** emp) ?s ?h ] => apply sc_emp2; sep_normal
    | [ |- (?P ** !(?Q)) ?s ?h ] => apply scban_r; [sep_normal | ]
    | [ |- (!(?P) ** ?Q) ?s ?h ] => apply scban_l; [ | sep_normal ]
    | [ |- (Ex _, _) ?s ?h ] => eapply scEx; [intros ? ? ? H; sep_normal; exact H | idtac ]
    | [ |- (?P ** ?Q) ?s ?h] => 
      eapply scRw; [intros ? ? H; sep_normal; exact H |
                    intros ? ? H; sep_normal; exact H | idtac];
      append_slist
    | _ => idtac
  end.
      
Example normalize_test1 (P Q R S : assn) s h :
  (P ** Q ** R ** S) s h -> ((P ** Q) ** (R ** S)) s h.
Proof.
  intros H. sep_normal. exact H.
Qed.
  
Example normalize_test2 (P Q R S : assn) s h : (P ** Q ** R) s h -> ((P ** Q) ** R) s h.
Proof.
  intros H. sep_normal. exact H.
Qed.

Example normalize_test3 (P Q R S : assn) s h : (P ** Q ** R) s h -> (((P ** emp) ** Q) ** R) s h.
Proof.
  intros H. sep_normal. exact H.
Qed.

Example sep_normal4 (P Q R S : nat -> assn) s h : 
  (Ex x, (P x ** Q x ** R x ** S x)) s h -> (Ex x, ((P x ** Q x) ** (R x ** S x))) s h.
Proof.
  intros H. sep_normal. exact H.
Qed.

Example normalize_test5 (P Q R S : assn) s h : 
  (P ** Q) s h -> R s emp_ph -> ((P ** Q) ** !(R)) s h.
Proof.
  intros H0 H1. sep_normal; [apply H0 | apply H1].
Qed.

Lemma sc_emp1' (P : assn) : (emp ** P) |= P.
Proof.
  intros s h (ph1 & ph2 & Hsat1 & Hsat2 & Hdis & Heq).
  assert (h = ph2).
  { destruct h, ph2; apply pheap_eq; simpl in *; rewrite <-Heq.
    unfold phplus; extensionality x.
    unfold_conn; rewrite Hsat1; auto. }
  rewrite H; auto.
Qed.

Lemma sc_emp2' (P : assn) : (P ** emp) |= P.
Proof.
  intros s h (ph1 & ph2 & Hsat1 & Hsat2 & Hdis & Heq).
  assert (h = ph1).
  { destruct h as [h ?], ph1 as [ph1 ?]; apply pheap_eq; simpl in *; rewrite <-Heq.
    unfold phplus; extensionality x.
    unfold_conn; rewrite Hsat2; destruct (ph1 x) as [[? ?]|]; auto. }
  rewrite H; auto.
Qed.

Goal forall (P : nat -> assn) s h, (Ex x, P x) s h -> False.
Proof.
  intros P s h H. eapply scEx in H.
Abort.

Goal forall (P Q : assn) s h, (P ** Q) s h -> False.
Proof.
  intros P Q s h H. eapply scRw in H.
Abort.

Goal forall (P Q R : assn) s h, ((P ** Q) ** R) s h -> False.
Proof.
  intros P Q R s h H. eapply scRw in H.
Abort.

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

Ltac last_slist_in H :=
  let Hf := fresh "H" in
  match goal with
    | [ H' : (?P ** ?R) ?s ?h |- _ ] => match H with H' =>
        eapply scRw in H; [ idtac |
                            intros ? ? Hf; exact Hf |
                            intros ? ? Hf; last_slist_in Hf; exact Hf ];
        apply scA in H
      end
    | _ => idtac
  end.

Example last_slist_in_test P Q R s h :
  (P ** Q ** R) s h -> ((P ** Q) ** R) s h.
Proof. intros H; last_slist_in H; exact H. Qed.

Ltac append_slist_in H :=
  let Hf := fresh "H" in
  match goal with
    | [ H' : ((?P ** ?Q) ** ?R) ?s ?h |- _ ] => match H with H' =>
        eapply scRw in H; [ idtac |
                            intros ? ? Hf; last_slist_in Hf; exact Hf |
                            intros ? ? Hf; exact Hf ];
        apply scA' in H; append_slist_in H
      end
    | [ |- _ ] => idtac
  end.

Ltac sep_normal_in' H :=
  let Hf := fresh "H" in
  match goal with
    | [ H' : (emp ** ?P) ?s ?h |- _ ] => match H with H' =>
        apply sc_emp1' in H; sep_normal_in' H
      end
    | [ H' : (?P ** emp) ?s ?h |- _ ] => match H with H' =>
        apply sc_emp2' in H; sep_normal_in' H
      end
    | [ H' : (Ex _, _) ?s ?h |- _ ] => match H with H' => 
        eapply scEx in H; [ idtac | intros ? ? ? Hf; sep_normal_in' Hf; exact Hf ]
      end
    | [ H' : (?P ** ?Q) ?s ?h |- _ ] => match H with H' => 
        eapply scRw in H; [ idtac |
                            intros ? ? Hf; sep_normal_in' Hf; exact Hf |
                            intros ? ? Hf; sep_normal_in' Hf; exact Hf ];
        append_slist_in H
      end
    | _ => idtac
  end.

Example sep_normal_in'_test1 (P Q R S : assn) s h :
  ((P ** Q) ** (R ** S)) s h -> (P ** Q ** R ** S) s h.
Proof.
  intros H. 
  sep_normal_in' H. exact H.
Qed.
  
Example sep_normal_in'_test2 (P Q R S : assn) s h : ((P ** Q) ** R) s h ->(P ** Q ** R) s h.
Proof.
  intros H. sep_normal_in' H. exact H.
Qed.

Example sep_normal_in'_test3 (P Q R S : assn) s h : (((P ** emp) ** Q) ** R) s h ->(P ** Q ** R) s h.
Proof.
  intros H. sep_normal_in' H. exact H.
Qed.

Example sep_normal_in'_goal4 (P Q R S : nat -> assn) s h : 
  (Ex x, ((P x ** Q x) ** (R x ** S x))) s h -> (Ex x, (P x ** Q x ** R x ** S x)) s h.
Proof.
  intros H. sep_normal_in' H. exact H.
Qed.

Example sep_normal_in'_test5 (P Q R S : assn) s h :
  (((P ** emp ** Q) ** Q) ** R) s h -> (P ** Q ** Q ** R) s h.
Proof.
  intros H; sep_normal_in' H; exact H.
Qed.

Ltac sep_lift_in H n :=
  match goal with
    | [ H' : (Ex _, _) ?s ?h |- _ ] => match H' with H =>
      match n with
        | O => fail 2
        | S ?n => 
          let Hf := fresh "H" in
          eapply scEx in H; [idtac | intros ? ? ? Hf; sep_lift_in Hf n; exact Hf] 
      end end
    | [ H' : (_ ** _ ** _) ?s ?h |- _ ] => match H' with H =>
      match n with
        | 0 => idtac
        | S ?n => 
          let Hf := fresh "H" in
          eapply scRw in H; [idtac |
                        intros ? ? Hf; exact Hf | 
                        intros ? ? Hf; sep_lift_in Hf n; exact Hf];
          apply scCA in H
      end end
    | [ H' : (_ ** _) ?s ?h |- _] => match H' with H =>
      match n with
        | 0 => idtac
        | S ?n => apply scC in H
      end end
    | _ => idtac
  end.

Example sep_lift_in_test_example (P0 P1 P2 : assn) s h :
  (P0 ** P1 ** P2) s h -> (P1 ** P0 ** P2) s h.
Proof. intros H. sep_lift_in H 1. exact H. Qed.

Example sep_lift_in_test0 (P0 P1 P2 P3 P4 : assn) s h :
  (P0 ** P1 ** P2 ** P3 ** P4) s h -> (P0 ** P1 ** P2 ** P3 ** P4) s h.
Proof. intros H. sep_lift_in H 0. exact H. Qed.

Example sep_lift_in_test1 (P0 P1 P2 P3 P4 : assn) s h :
  (P0 ** P1 ** P2 ** P3 ** P4) s h -> (P1 ** P0 ** P2 ** P3 ** P4) s h.
Proof. intros H. sep_lift_in H 1. exact H. Qed.

Example sep_lift_in_test2 (P0 P1 P2 P3 P4 : assn) s h :
  (P0 ** P1 ** P2 ** P3 ** P4) s h -> (P2 ** P0 ** P1 ** P3 ** P4) s h.
Proof. intros H. sep_lift_in H 2. exact H. Qed.

Example sep_lift_in_test3 (P0 P1 P2 P3 P4 : assn) s h :
  (P0 ** P1 ** P2 ** P3 ** P4) s h -> (P3 ** P0 ** P1 ** P2 ** P4) s h.
Proof. intros H. sep_lift_in H 3. exact H. Qed.

Example sep_lift_in_test4 (P0 P1 P2 P3 P4 : assn) s h :
  (P0 ** P1 ** P2 ** P3 ** P4) s h -> (P4 ** P0 ** P1 ** P2 ** P3) s h.
Proof. intros H. sep_lift_in H 4. exact H. Qed.

Example sep_lift_in_testEx0 (P0 P1 P2 : nat -> assn) s h :
  (Ex x, P0 x ** P1 x ** P2 x) s h -> (Ex x, (P1 x ** P0 x ** P2 x)) s h.
Proof. intros H. sep_lift_in H 2. exact H. Qed.

Example sep_lift_in_testEx1 (P0 P1 P2 : nat -> assn) s h :
  (Ex x, P0 x ** P1 x ** P2 x) s h -> (Ex x, (P2 x ** P0 x ** P1 x)) s h.
Proof. intros H. sep_lift_in H 3. exact H. Qed.

Ltac find_ban Ps k :=
  match Ps with
    | !(?P) => k (Some 0)
    | !(?P) ** _ => k (Some 0)
    | _ ** ?Ps => find_ban Ps ltac:(fun n =>
        idtac "debug:" n;
        match n with false => k false | Some ?n => k (Some (S n)) end)
    | _ => k false
  end.

Ltac sep_normal_in H :=
  sep_normal_in' H;
  repeat (match goal with
    | [ H' : ?P ?s ?h |- _ ] => match H' with H =>
      find_ban P ltac:(fun n =>
      idtac "debug" n;
      match n with
        | false => idtac
        | Some ?n =>
          let HP := fresh "HP" in
          sep_lift_in H n; apply scban_l' in H as [HP H]
      end)
  end end).

Example sep_normal_in_test5 (P Q R S : assn) s h :
  (((P ** emp ** !(Q)) ** !(S)) ** R) s h ->(P ** R) s h /\ Q s emp_ph /\ S s emp_ph.
Proof.
  intros H; sep_normal_in H; auto.
Qed.

Example sep_normal_in_test1 (P Q R S : assn) s h :
  ((P ** Q) ** (R ** S)) s h -> (P ** Q ** R ** S) s h.
Proof.
  intros H. 
  sep_normal_in H. exact H.
Qed.
  
Example sep_normal_in_test2 (P Q R S : assn) s h : ((P ** Q) ** R) s h ->(P ** Q ** R) s h.
Proof.
  intros H. sep_normal_in H. exact H.
Qed.

Example sep_normal_in_test3 (P Q R S : assn) s h : (((P ** emp) ** Q) ** R) s h ->(P ** Q ** R) s h.
Proof.
  intros H. sep_normal_in H. exact H.
Qed.

Example sep_normal_in_goal4 (P Q R S : nat -> assn) s h : 
  (Ex x, ((P x ** Q x) ** (R x ** S x))) s h -> (Ex x, (P x ** Q x ** R x ** S x)) s h.
Proof.
  intros H. sep_normal_in H. exact H.
Qed.

Ltac sep_lift n :=
  let pred_n n k :=
    match n with
      | S ?n => k n
      | 0 => fail 2; k 0
    end in
  match goal with
    | [ |- (Ex _, _) ?s ?h ] => 
      pred_n n ltac:(fun n =>
        let H := fresh "H" in
        eapply scEx; [intros ? ? ? H; sep_lift n; exact H| idtac] )
    | [ |- (_ ** _ ** _) ?s ?h ] =>
      match n with
        | 0 => idtac
        | S ?n => 
          let H := fresh "H" in
          eapply scRw; [intros ? ? H; exact H | 
                       intros ? ? H; sep_lift n; exact H|
                       idtac];
          apply scCA
      end
    | [ |- (_ ** _) ?s ?h ] =>
      match n with
        | 0 => idtac
        | S ?n => apply scC
      end
    | _ => idtac
  end.

Example sep_lift_test0 (P0 P1 P2 P3 P4 : assn) s h :
  (P0 ** P1 ** P2 ** P3 ** P4) s h -> (P0 ** P1 ** P2 ** P3 ** P4) s h.
Proof. intros H. sep_lift 0. exact H. Qed.

Example sep_lift_test1 (P0 P1 P2 P3 P4 : assn) s h :
  (P1 ** P0 ** P2 ** P3 ** P4) s h -> (P0 ** P1 ** P2 ** P3 ** P4) s h.
Proof. intros H. sep_lift 1. exact H. Qed.

Example sep_lift_test2 (P0 P1 P2 P3 P4 : assn) s h :
  (P2 ** P0 ** P1 ** P3 ** P4) s h -> (P0 ** P1 ** P2 ** P3 ** P4) s h.
Proof. intros H. sep_lift 2. exact H. Qed.

Example sep_lift_test3 (P0 P1 P2 P3 P4 : assn) s h :
  (P3 ** P0 ** P1 ** P2 ** P4) s h -> (P0 ** P1 ** P2 ** P3 ** P4) s h.
Proof. intros H. sep_lift 3. exact H. Qed.

Example sep_lift_test4 (P0 P1 P2 P3 P4 : assn) s h :
  (P4 ** P0 ** P1 ** P2 ** P3) s h -> (P0 ** P1 ** P2 ** P3 ** P4) s h.
Proof. intros H. sep_lift 4. exact H. Qed.

Example sep_lift_testEx0 (P0 P1 P2 : nat -> assn) s h :
  (Ex x, P1 x ** P0 x ** P2 x) s h -> (Ex x, (P0 x ** P1 x ** P2 x)) s h.
Proof. intros H. sep_lift 2. exact H. Qed.

Example sep_lift_testEx1 (P0 P1 P2 : nat -> assn) s h :
  (Ex x, P2 x ** P0 x ** P1 x) s h -> (Ex x, (P0 x ** P1 x ** P2 x)) s h.
Proof. intros H. sep_lift 3. exact H. Qed.

Goal forall P Q R, (Ex x : nat, (P ** Q ** R)) |= P ** Q ** R.
Proof.
  intros P Q R s h H.
  eapply scEx in H.
Abort.

Goal forall P Q R, (P ** Q ** R) |= P ** Q ** R.
Proof.
  intros P Q R s h H.
  eapply scRw in H;
    [ idtac |
      intros ? ? Hf; exact Hf |
      intros ? ? Hf; apply scC in Hf; exact Hf ];
  apply scCA in H.
Abort.


Ltac find_assn P Qs k :=
  match Qs with
    | P => k (Some 0)
    | P ** _ => k (Some 0)
    | _ ** ?Qs => find_assn P Qs ltac:(fun n => 
       match n with false => k false | Some ?n => k (Some (S n)) end)
    | _ => k false
  end.

Ltac search_match P Q k :=
  match Q with
    | ?R ** ?Q => find_assn R P ltac:(fun n =>
      match n with
        | Some ?n => k (Some (n, 0))
        | false => search_match P Q ltac:(fun p =>
          match p with
            | Some (?n, ?m) => k (Some (n, S m))
            | false => k false
          end)
      end)
    | _ => k false
  end.

Ltac sep_cancel :=
  match goal with
    | [ H : ?P ?s ?h |- ?P ?s ?h] => exact H
    | [ H : (?P ** ?Q) ?s ?h |- (?P ** ?R) ?s ?h] =>
      let Hf := fresh "H" in
      eapply scRw; [ intros ? ? Hf; exact Hf | 
                     clear s h H; intros s h H |
                     exact H]
    | [ H : ?P ?s ?h |- ?Q ?s ?h ] =>
      search_match P Q ltac:(fun p => 
      match p with
        | Some (?n, ?m) =>
          sep_lift m; sep_lift_in H n;
          sep_cancel
        | None => idtac
      end)
  end.

Example sep_cansel_example (P Q R : assn) s h :
  (P ** Q ** R) s h -> (R ** Q ** P) s h.
Proof.
  intros H.
  repeat sep_cancel. 
Qed.