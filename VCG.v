Set Implicit Arguments.
Unset Strict Implicit.

Require Import Qcanon.
Require Import assertions.
Require Import Lang.
Require Import CSL.
Require Import PHeap.

Definition TID := Var 0.
Definition ARR := Var 1.
Definition X := Var 2.

Open Scope exp_scope.
Open Scope bexp_scope.

Section independent_prover.
  Ltac inde_simpl :=
    unfold inde in *; simpl in *; intros x s h v Hin.

  Lemma inde_sconj (P Q : assn) (vs : list var) :
    inde P vs -> inde Q vs -> inde (P ** Q) vs.
  Proof.
    intros Hp Hq; inde_simpl.
    unfold_conn; split; intros (ph1 & ph2 & Hp' & Hq' & Hdis' & Heq).
    exists ph1, ph2; repeat split; [apply Hp | apply Hq | idtac..]; auto.
    exists ph1, ph2; repeat split; [apply<-Hp | apply<-Hq | idtac..]; eauto.
  Qed.

  Lemma inde_pure (P : assn) (vs : list var) : inde P vs -> inde !(P) vs.
  Proof.
    intros Hp; inde_simpl.
    unfold_conn; split; intros [H1 H2].
    split; [auto | apply Hp]; auto.
    split; [auto | apply<-Hp]; eauto.
  Qed.

  Lemma inde_conj (P Q : assn) (vs : list var) : inde P vs -> inde Q vs -> inde (P //\\ Q) vs.
  Proof.
    intros Hp Hq; inde_simpl.
    unfold_conn; split; intros [Hp' Hq'].
    split; [apply Hp | apply Hq]; auto.
    split; [apply <-Hp | apply <-Hq]; eauto.
  Qed.

  Lemma inde_disj (P Q : assn) (vs : list var) : inde P vs -> inde Q vs -> inde (P \\// Q) vs.
  Proof.
    intros Hp Hq; inde_simpl.
    unfold_conn; split; intros H.
    destruct H; [left; apply Hp | right; apply Hq]; auto.
    destruct H; [left; apply <-Hp | right; apply <-Hq]; eauto.
  Qed.

  Lemma inde_pointto (E E' : exp) (q : Qc) (vs : list var) :
    List.Forall (indeE E) vs -> List.Forall (indeE E') vs ->
    inde (E -->p (q, E')) vs.
  Proof.
    intros Hp Hq; inde_simpl.
    rewrite List.Forall_forall in *.
    unfold_conn; split; intros H.
    rewrite<-(Hp x Hin s); rewrite<-(Hq x Hin s); auto.
    erewrite (Hp x Hin s); erewrite (Hq x Hin s); eauto.
  Qed.

  Lemma inde_eeq (E E' : exp) (vs : list var) :
    List.Forall (indeE E) vs -> List.Forall (indeE E') vs ->
    inde (E === E') vs.
  Proof.
    intros H H'; inde_simpl.
    rewrite List.Forall_forall in *.
    unfold_conn; split; intros Heq.
    rewrite<-(H x Hin s); rewrite<-(H' x Hin s); auto.
    erewrite (H x Hin s); erewrite (H' x Hin s); eauto.
  Qed.
End independent_prover.

Ltac prove_indeE := unfold indeE, var_upd; intros; simpl; auto.

Ltac prove_inde :=
  match goal with
    | [ |- inde (?P ** ?Q) _ ] => apply inde_sconj; prove_inde
    | [ |- inde !(?P) _ ] => apply inde_pure; prove_inde
    | [ |- inde (?P //\\ ?Q) _ ] => apply inde_conj; prove_inde
    | [ |- inde (?P \\// ?Q) _ ] => apply inde_disj; prove_inde
    | [ |- inde (?E -->p (_, ?E')) _ ] => apply inde_pointto; repeat (constructor; prove_indeE)
    | [ |- inde (?E === ?E') _ ] => apply inde_eeq; repeat (constructor; prove_indeE)
    | [ |- _ ] => (unfold inde, var_upd; simpl; auto)
  end.

Ltac find_addr P E k :=
  idtac "find_addr debug:" P;
  match P with
    | (E -->p (?q, ?E1)) ** ?Q => k (Some 0)
    | _ ** ?Q => find_addr Q E ltac:(fun n =>
        match n with false => k false | Some ?n => k (Some (S n)) end)
    | _ => k false
  end.

Example find_addr_test E E1 P Q s h :(P ** (E -->p (1%Qc, E1)) ** Q) s h.
Proof.
  match goal with [ |- ?H ?s ?h ] => find_addr H E ltac:(fun n => idtac n) end.
  sep_lift 1. 
Abort.

Section hoare_lemmas.
  Variable ntrd : nat.
  Variable bspec : Bdiv.barrier_spec ntrd.
  Variable tid : Fin.t ntrd.
  Lemma Hbackward (P P' Q : assn) (C : cmd) :
    CSL bspec tid P' C Q -> (P |= P') -> CSL bspec tid P C Q.
  Proof.
    intros; eapply rule_conseq; eauto.
  Qed.

  Lemma Hforward (P Q Q' : assn) (C : cmd) :
    CSL bspec tid P C Q' -> (Q' |= Q) -> CSL bspec tid P C Q.
  Proof.
    intros; eapply rule_conseq; eauto.
  Qed.
End hoare_lemmas.

Notation "P <=> Q" := (forall s h, P s h <-> Q s h) (at level 87).

Lemma mapsto_rewrite (E1 E2 E3 : exp) (p : Qc) (s : stack) (h : pheap) :
  (E1 === E2) s h -> (E1 -->p (p, E3)) s h -> (E2 -->p (p, E3)) s h.
Proof.
  intros.
  unfold_conn; simpl in *.
  rewrite<-H.
  auto.
Qed.

Ltac find_enough_resource E H :=
  match type of H with
    | ((?E0 -->p (_, ?E1)) ?s ?h) => 
      let Hf := fresh in
      assert (Hf : ((E0 === E) s h)) by (unfold_conn; simpl in *; first [congruence | omega]);
      apply (mapsto_rewrite Hf) in H
    | ((?E0 -->p (_, ?E1) ** _) ?s _) =>
      let Hf := fresh in
      assert (Hf : forall h, (E0 === E) s h) by solve [congruence | omega];
        let hf := fresh in let Hf' := fresh in 
        eapply scRw_stack in H;
        [idtac |
         intros hf Hf'; eapply (mapsto_rewrite (Hf hf)) in Hf'; exact Hf |
         intros ? Hf'; exact Hf]
    | ((_ ** _) _ _) =>
      let Hf := fresh in
      eapply scRw_stack in H; [idtac | intros ? Hf; exact Hf |
                               intros ? Hf; find_enough_resource E Hf; exact Hf];
(*      match goal with [|- ?P] => idtac P end;*)
      match goal with [ H' : ?P |- _ ] => match H with H' => match P with
        | ((_ ** _ ** _) _ _) => apply scCA in H
        | ((_ ** _) _ _) => apply scC in H
      end end end
  end.
 
Ltac hoare_forward :=
  match goal with
    | [ |- CSL ?bspec ?tid ?P (?X ::= [?E]) ?Q ] => 
      let Hf := fresh in
      eapply Hbackward; [idtac |
        intros s ? Hf;
        sep_normal_in Hf;
        find_enough_resource E Hf;
        exact Hf];
      eapply Hforward; [
        eapply rule_frame;
        [try eapply rule_read; idtac "ok!!!"; try prove_indeE | try prove_inde] | idtac ]
  end.

Section Hoare_test.
  Variable ntrd : nat.
  Variable bspec : Bdiv.barrier_spec ntrd.
  Lemma rotate_l2 (tid : Fin.t ntrd) (P Q : assn) (E : exp) :
    (inde P (X :: List.nil)) -> (inde Q (X :: List.nil)) -> (indeE E X) ->
    CSL bspec tid 
      (P ** Q ** (E -->p (1%Qc, 3%Z)) ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid)))
      (X ::= [ ARR + TID]) 
      (P ** Q ** (ARR + TID -->p (1%Qc, (Z_of_fin tid))) ** !( TID === (Z_of_fin tid))).
    Proof.
      intros. hoare_forward.
      apply H1.
      intros ? ? Hsat; sep_normal_in Hsat. sep_normal.
      sep_cancel. sep_cancel. sep_cancel. 
      
      sep_lift 0. sep_lift_in Hsat 1. eapply scRw_stack; [intros ? Hf; exact Hf |
                                                          intros ? ? |
                                                          exact Hsat].
(*      intros; eapply Hbackward; [| intros s ? Hf; sep_normal_in Hf; find_enough_resource (ARR+TID) Hf]. Focus 2.*)
      intros; eapply Hbackward. Focus 2.
      assert (((ARR + Z_of_fin tid -->p (1,  Z_of_fin tid)) s h) -> False).
      intros H'.
      assert ((ARR + Z_of_fin tid === ARR + TID) s h) by (unfold_conn; simpl in *; omega).
      apply (mapsto_rewrite H1) in H'.
      intros s h Hf.
      sep_normal_in Hf.
      eapply scRw_stack in Hf.
      Focus 2. intros ? Hf'; exact Hf'.
      Focus 2. intros h' Hf'.
      eapply scRw_stack in Hf'.
      Focus 2. intros ? Hf''; exact Hf''.
      Focus 2. intros h'' Hf''.
      eapply scRw_stack in Hf''.
      Focus 2. intros ? Hf'''; exact Hf'''.
      Focus 2. intros h''' Hf'''; exact Hf'''.
      eapply scC in Hf''. exact Hf''.
      eapply scCA in Hf'. exact Hf'.
      eapply scCA in Hf. exac
      sep_normal_in Hf. 
      find_enough_resource (ARR + TID) Hf.

      match goal with
        | [|- CSL _ _ ?P (?X ::= [?E]) ?Q] =>
          let Hf := fresh in
          eapply Hbackward; [idtac | intros ? ? Hf; sep_normal_in Hf; find_enough_resource E Hf]
      end.

      eapply Hbackward;[idtac|
      intros ? ? ?; sep_lift_in H1 2;
      sep_normal_in H1;
      assert (forall h, (ARR + Z_of_fin tid === ARR + TID) s h) by 
          (unfold_conn; solve [congruence | omega]); 
      eapply scRw_stack in H1; [idtac |
                                intros hf Hf; eapply (mapsto_rewrite (H2 hf)) in Hf; exact Hf |
                                intros ? Hf; exact Hf]].