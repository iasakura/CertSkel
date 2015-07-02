Set Implicit Arguments.
Unset Strict Implicit.

Require Import Qcanon.
Require Import assertions.
Require Import Lang.
Require Import CSL.
Require Import PHeap.

Local Notation TID := (Var 0).
Local Notation ARR := (Var 1).
Local Notation X := (Var 2).
Local Notation Y := (Var 3).
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

Ltac prove_indeE := unfold indeE, var_upd in *; intros; simpl; auto.

Ltac prove_inde :=
  match goal with
    | [ |- inde (?P ** ?Q) _ ] => apply inde_sconj; prove_inde
    | [ |- inde !(?P) _ ] => apply inde_pure; prove_inde
    | [ |- inde (?P //\\ ?Q) _ ] => apply inde_conj; prove_inde
    | [ |- inde (?P \\// ?Q) _ ] => apply inde_disj; prove_inde
    | [ |- inde (?E -->p (_, ?E')) _ ] => apply inde_pointto; repeat (constructor; prove_indeE)
    | [ |- inde (?E === ?E') _ ] => apply inde_eeq; repeat (constructor; prove_indeE)
    | [ |- _ ] => (unfold inde, var_upd; simpl; try tauto)
  end.

Section subA_simpl.
  Lemma subA_pointto (X : var) (E1 E2 E  : exp) (q : Qc) s h : (subA X E (E1 -->p (q, E2))) s h ->
                                                     (subE X E E1 -->p (q, subE X E E2)) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn.
    repeat rewrite <-subE_assign in *; auto.
  Qed.

  Lemma subA_sconj (P Q : assn) (X : var) (E : exp) s h :
    subA X E (P ** Q) s h -> (subA X E P  ** subA X E Q) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn.
    destruct H as (ph1 & ph2 & ? & ? & ? & ?); eexists; eauto.
  Qed.

  Lemma subA_conj (P Q : assn) (X : var) (E : exp) s h :
    subA X E (P //\\ Q) s h -> (subA X E P //\\ subA X E Q) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn; auto.
  Qed.

  Lemma subA_disj (P Q : assn) (X : var) (E : exp) s h :
    subA X E (P \\// Q) s h -> (subA X E P \\// subA X E Q) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn; auto.
  Qed.

  Lemma subA_pure (P : assn) (X : var) (E : exp) s h :
    subA X E !(P) s h -> !(subA X E P) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn; auto.
  Qed.

  Lemma subA_eeq (X : var) (E E1 E2 : exp) s h :
    subA X E (E1 === E2) s h -> (subE X E E1 === subE X E E2) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn.
    repeat rewrite <-subE_assign in *; auto.
  Qed.
End subA_simpl.

Lemma conj_mono (P Q P' Q' : assn) s h : (P s h -> P' s h) -> (Q s h -> Q' s h) ->
                                         (P //\\ Q) s h -> (P' //\\ Q') s h.
Proof.
  intros ? ? [? ?]; split; auto.
Qed.

Lemma disj_mono (P Q P' Q' : assn) s h : (P s h -> P' s h) -> (Q s h -> Q' s h) ->
                                         (P \\// Q) s h -> (P' \\// Q') s h.
Proof.
  intros ? ? [? | ?]; ((left; tauto) || (right; tauto)).
Qed.

Lemma pure_mono (P P' : assn) s h : (P s h -> P' s h) ->
                                    !(P) s h -> !(P') s h.
Proof.
  intros ? [? ?]; split; auto.
Qed.

Lemma subA_bexp_to_assn (x : var) (e : exp) (b : bexp) :
  subA x e (bexp_to_assn b) |= bexp_to_assn (subB x e b).
Proof.
  intros.
  unfold bexp_to_assn, subA' in *; simpl.
  rewrite <-subB_assign in H; auto.
Qed.

Lemma subA_emp (x : var) (e : exp) : subA x e emp |= emp.
Proof. unfold_conn; auto. Qed.

Ltac subA_normalize_in H :=
  let Hf := fresh in
  match goal with _ => idtac end;
  match type of H with
    | subA _ _ (_ ** _) _ _ =>
      apply subA_sconj in H; eapply scRw in H;
        [ idtac | intros ? ? Hf; subA_normalize_in Hf; exact Hf .. ]
    | subA _ _ (_ //\\ _) _ _ =>
      apply subA_conj in H;  eapply conj_mono in H;
        [ idtac | intros Hf; subA_normalize_in Hf; exact Hf .. ]
    | subA _ _ (_ \\// _) _ _ =>
      apply subA_disj in H;  eapply disj_mono in H;
        [ idtac | intros Hf; subA_normalize_in Hf; exact Hf .. ]
    | subA _ _ (_ -->p (_, _)) _ _ => apply subA_pointto in H
    | subA _ _ !(_) _ _ => eapply subA_pure in H; eapply pure_mono in H;
        [ idtac | intros Hf; subA_normalize_in Hf; exact Hf ]
    | subA _ _ (_ === _) _ _ => apply subA_eeq in H
    | subA _ _ emp _ _ => apply subA_emp in H
    | subA _ _ (bexp_to_assn ?b) _ _ => apply subA_bexp_to_assn in H
    | _ => simpl in H
  end.

Example subA_test6 (E1 E2 : exp) (X : var) (E : exp) s h :
  subA X E (E1 === E2) s h -> (subE X E E1 === subE X E E2) s h.
Proof.
  intros. subA_normalize_in H.
Abort.
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

Ltac ltac_bug E H :=
  match type of H with
    | ((_ ** _) _ _) =>
      let Hf := fresh in
      eapply scRw_stack in H; [idtac | intros ? Hf; exact Hf |
                               intros ? Hf; ltac_bug E Hf; exact Hf];
      match goal with _ => idtac  end;
      match type of H with
        | ((_ ** _ ** _) _ _) => apply scCA in H
        | ((_ ** _) _ _) => apply scC in H
      end 
    | _ => idtac
  end.

Example ltac_bug P Q s h n (tid : Fin.t n) :
  (P ** Q ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid))) s h -> False.
Proof.
  intros.
  sep_split_in H.
  ltac_bug (ARR + Z_of_fin tid) H.
Abort.

Example find_test P Q s h n (tid : Fin.t n) :
  (P ** Q ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid))) s h -> False.
Proof.
  intros.
  sep_split_in H.
  find_enough_resource (ARR + Z_of_fin tid) H.
Abort.

Example sep_combine_test P Q R S s h : (P ** Q ** !(R) ** !(S)) s h -> True.
Proof.
  intros H; sep_split_in H.
  sep_combine_in H.
Abort.

Lemma rule_assign_forward (ntrd : nat) (bspec : Bdiv.barrier_spec ntrd) (tid : Fin.t ntrd) (X : var) (E : exp) (P : assn) :
  CSL bspec tid P (X ::= E) (Ex v, subA X v P ** !(X === subE X v E)).
Proof.
  unfold subA'.
  eapply Hbackward.
  apply rule_assign.
  intros s h H; exists (s X).
  sep_split; unfold_conn; simpl.
  rewrite subE_assign; unfold var_upd; simpl.
  destruct (var_eq_dec X X) as [_|]; try congruence.
  f_equal; extensionality x.
  destruct (var_eq_dec _ _); subst; congruence.

  assert (Heq : s = var_upd (var_upd s X (edenot E s)) X (s X)); [|rewrite <-Heq; auto].
  extensionality x; unfold var_upd; destruct (var_eq_dec _ _); subst; congruence.
Qed.

Global Create HintDb sep.

Ltac simplify :=
  autounfold; simpl; autorewrite with sep.

Ltac frame_analysis P :=
  let Pe := fresh in
  evar (Pe : assn);
  let Hf := fresh in
  let s := fresh in
  let h := fresh in
  intros s h Hf;
  let Hf' := fresh in
  assert (Hf' : (P ** Pe) s h);
  [ simplify;
    repeat match goal with
      | [P' := ?ev : assn, H : ?Q ?s ?h |- ?P ?s ?h] => match P with
           | P' => is_evar ev; sep_combine_in H; exact H
        end
      | _ => progress (sep_split_in Hf; unfold lt in *; sep_cancel; sep_combine_in Hf)
    end | exact Hf' ].

Lemma rule_if_disj (ntrd : nat) (bspec : Bdiv.barrier_spec ntrd) (tid : Fin.t ntrd) (P Q1 Q2 : assn)
      (b : bexp) (C1 C2 : cmd) :
  CSL bspec tid (P ** !(b)) C1 Q1 -> CSL bspec tid (P ** !(Bnot b)) C2 Q2 ->
  CSL bspec tid (P) (Cif b C1 C2) (Q1 \\// Q2).
Proof.
  intros.
  eapply rule_if;
  eapply Hforward; unfold Apure; unfold bexp_to_assn in *;
  [eapply Hbackward; [apply H |] | | eapply Hbackward; [apply H0 |] |];
   try (intros; destruct H1; exists h, emp_ph; repeat split; auto); intros; unfold_conn; tauto.
Qed.

Ltac hoare_forward :=
  match goal with
    | [ |- CSL ?bspec ?tid ?P (?X ::= [?E]) ?Q ] => 
      idtac "case: read";
      let Hf := fresh in
      let s := fresh in
      eapply Hbackward; [idtac |
        intros s ? Hf;
        sep_normal_in Hf;
        sep_split_in Hf;
        find_enough_resource E Hf;
        sep_combine_in Hf;
        exact Hf];
      eapply Hforward; [
        eapply rule_frame;
        [eapply rule_read; idtac "ok!!!"; prove_indeE | prove_inde] | prove_inde ]
    | [ |- CSL ?bspec ?tid ?P ([?E] ::= _) ?Q ] =>
      idtac "case: write";
      let Hf := fresh in
      let s := fresh in
      eapply Hbackward; [idtac |
        intros s ? Hf;
        sep_normal_in Hf;
        sep_split_in Hf;
        find_enough_resource E Hf;
        sep_combine_in Hf;
        exact Hf];
      eapply Hforward; [
        eapply rule_frame;
        [eapply rule_write; idtac "ok!!!" | prove_inde ] | idtac]
    | [ |- CSL ?bspec ?tid ?P (?X ::= _) ?Q] =>
      let Hf := fresh in
      eapply Hforward; [
        apply rule_assign_forward | idtac ]
    | [ |- CSL ?bspec ?tid ?P (Cbarrier ?i) ?Q] =>
      idtac "called";
      eapply Hbackward; [
        eapply Hforward; [
          eapply rule_frame; 
          [eapply rule_barrier | prove_inde] |
           autounfold; simpl; repeat rewrite MyVector.init_spec in *] | 
        frame_analysis (Vector.nth (fst (bspec i)) tid)]
    | [ |- CSL ?bspec ?tid ?P (Cif ?b ?c1 ?c2) ?Q ] =>
      eapply Hforward; [
          eapply rule_if_disj | idtac]
    | [ |- CSL ?bspec ?tid (?P1 \\// ?P2) ?C ?Q ] =>
      eapply rule_disj; hoare_forward
  end.

(*Section Hoare_test.
  Variable ntrd : nat.
  Notation ntrdZ := (Z.of_nat ntrd).

  Require Import MyVector.
  Import VectorNotations.

  Definition bpre (tid : Fin.t ntrd) := 
    (ARR + (Z_of_fin tid) -->p (1%Qc, (Z_of_fin tid)))%assn.
  Definition bpost (tid : Fin.t ntrd) := 
    (ARR + ((Z_of_fin tid + 1) mod ntrdZ)%Z) -->p (1%Qc, ((Z_of_fin tid + 1) mod ntrdZ)%Z).
  Notation FalseP := (fun (_ : stack) (h : pheap) => False).
  Definition default : (Vector.t assn ntrd * Vector.t assn ntrd) := 
    (init (fun _ => FalseP), init (fun _ => FalseP)).

  Definition bspec (i : nat) :=
    match i with
      | 0 => (init bpre, init bpost)
      | S _ => default
    end.

  Lemma rotate_l7 (tid : Fin.t ntrd) :
      CSL bspec tid
      (( ARR +  ((Z_of_fin tid + 1) mod ntrdZ))%exp -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ))%Z **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid)))
      (Cif ( TID ==  (ntrdZ - 1)%Z) (
         Y ::=  0%Z
       ) (
         Y ::=  TID +  1%Z
       ))
      ((( ARR +  Y) -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ)%Z) **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid) //\\
         Y ===  ((Z_of_fin tid + 1) mod ntrdZ)%Z))).
    Proof.
      hoare_forward; [hoare_forward | hoare_forward | idtac].
      intros. simpl in H. sep_split_in H. subA_normalize_in H. simpl in H.
      sep_combine_in H. exact H.
      intros. simpl in H. sep_split_in H. subA_normalize_in H. simpl in H. sep_combine_in H. exact H.
      intros ? ? H.
      destruct H.
      sep_split_in H.
    Abort.


  Hint Unfold bspec bpre bpost.
  Hint Rewrite MyVector.init_spec : sep.
  Lemma rotate_l4 (tid : Fin.t ntrd) :
    CSL bspec tid
      (( ARR +  (Z_of_fin tid)) -->p (1%Qc,  (Z_of_fin tid)) **
                                !( TID ===  (Z_of_fin tid)) ** !(X ===  (Z_of_fin tid)))
      (Cbarrier 0)
      (( ARR +  ((Z_of_fin tid + 1) mod ntrdZ)%Z) -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ)%Z) **
      !( TID ===  (Z_of_fin tid)) **  !(X ===  (Z_of_fin tid))).
  Proof.
    hoare_forward.
    intros.
    sep_cancel.
  Qed.

  Lemma rotate_l2 (tid : Fin.t ntrd) (P Q : assn) (E : exp) :
    (inde P (X :: List.nil)) -> (inde Q (X :: List.nil)) -> (indeE E X) ->
    CSL bspec tid 
      (P ** Q ** (E -->p (1%Qc, 3%Z)) ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid)))
      (X ::= [ ARR + TID]) 
      (P ** Q ** (ARR + TID -->p (1%Qc, (Z_of_fin tid))) ** !( TID === (Z_of_fin tid)) ** (E -->p (1%Qc, 3%Z))).
    Proof.
      intros. 
      hoare_forward.
      intros; sep_normal_in H2; sep_split_in H2; sep_normal; sep_split; solve [auto | repeat sep_cancel].
    Qed.

  Lemma rotate_l3 (tid : Fin.t ntrd) (P Q : assn) (E : exp) :
    (inde P (X :: List.nil)) -> (inde Q (X :: List.nil)) -> (indeE E X) ->
    CSL bspec tid 
      (P ** Q ** (E -->p (full_p%Qc, 2%Z)) ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid)))
      ([ ARR + TID] ::= 3%Z) 
      (P ** Q ** (ARR + TID -->p (full_p%Qc, 3%Z)) ** !( TID === (Z_of_fin tid)) ** (E -->p (1%Qc, 2%Z))).
  Proof.
    intros. hoare_forward.
    intros; repeat sep_cancel.
  Qed.

  Lemma test_assign (tid : Fin.t ntrd) (P Q : assn) (E : exp) :
    CSL bspec tid 
        (P ** Q ** (E -->p (full_p%Qc, 2%Z)) ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid)))
        (X ::= 3%Z) 
        (P ** Q ** (ARR + TID -->p (full_p%Qc, 3%Z)) ** !( TID === (Z_of_fin tid)) ** (E -->p (1%Qc, 2%Z))).
  Proof.
    intros. hoare_forward.
    intros s h H.
    sep_split_in H; simpl in *.
    subA_normalize_in H.
  Abort.
End Hoare_test.*)
