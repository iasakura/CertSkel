Set Implicit Arguments.
Unset Strict Implicit.

Require Import Qcanon.
Require Import assertions.
Require Import Lang.
Require Import CSL.
Require Import PHeap.
Require Import array_dist.
Local Notation TID := (Var 0).
Local Notation ARR := (Var 1).
Local Notation X := (Var 2).
Local Notation Y := (Var 3).
Open Scope exp_scope.
Open Scope bexp_scope.

Section independent_prover.
  Ltac inde_simpl :=
    unfold inde in *; simpl in *; intros ? ? ? ? ?.

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
    unfold_conn; split; intros H'.
    destruct H'; [left; apply Hp | right; apply Hq]; auto.
    destruct H'; [left; apply <-Hp | right; apply <-Hq]; eauto.
  Qed.

  Lemma inde_pointto (E E' : exp) (q : Qc) (vs : list var) :
    List.Forall (indeE E) vs -> List.Forall (indeE E') vs ->
    inde (E -->p (q, E')) vs.
  Proof.
    intros Hp Hq; inde_simpl.
    rewrite List.Forall_forall in *.
    unfold_conn; split; intros H'.
    rewrite<-(Hp x H s); rewrite<-(Hq x H s); auto.
    erewrite (Hp x H s); erewrite (Hq x H s); eauto.
  Qed.

  Lemma inde_eeq (E E' : exp) (vs : list var) :
    List.Forall (indeE E) vs -> List.Forall (indeE E') vs ->
    inde (E === E') vs.
  Proof.
    intros H H'; inde_simpl.
    rewrite List.Forall_forall in *.
    unfold_conn; split; intros Heq.
    rewrite<-(H x H0 s); rewrite<-(H' x H0 s); auto.
    erewrite (H x H0 s); erewrite (H' x H0 s); eauto.
  Qed.

  Lemma inde_distribute nt arr l f dist (i : nat) (vs : list var) : forall s,
    (i < nt)%nat -> (forall i, dist i < nt)%nat ->
    List.Forall (indeE arr) vs  ->
    inde (List.nth i (distribute nt arr l f dist s) emp) vs.
  Proof.
    induction l; intros; simpl.
    - simpl_nth. destruct (Compare_dec.leb _ _); inde_simpl; simpl; try tauto.
    - rewrite nth_add_nth in *; [|rewrite distribute_length; auto..].
      destruct (EqNat.beq_nat _ _); intuition.
      apply inde_sconj; [apply inde_pointto|]; intuition.
      clear IHl; induction vs; constructor; unfold indeE in *; inversion H1; subst; simpl; intuition.
      clear IHl; induction vs; constructor; unfold indeE in *; inversion H1; subst; simpl; intuition.
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
    | [ |- inde (inde (List.nth _ (distribute _ _ _ _ _ _) emp) _) ] =>
      apply inde_distribute; auto; repeat (constructor; prove_indeE)
    | [ |- _ ] => (* unfold inde, var_upd; simpl; try tauto *) idtac
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

  Lemma distribute_subA nt arr l f dist (i : nat) x e : forall s,
    (i < nt)%nat -> (forall i, dist i < nt)%nat ->
    subA x e (List.nth i (distribute nt arr l f dist s) emp) |=
    List.nth i (distribute nt (subE x e arr) l f dist s) emp.
  Proof.
    induction l; unfold subA'; intros s Hint dist_ok st hp H; simpl in *.
    - simpl_nth; destruct (Compare_dec.leb _ _); auto;
      split; intros; simpl; auto.
    - rewrite nth_add_nth in *; [|rewrite distribute_length; auto..].
      destruct (EqNat.beq_nat _ _); intuition.
      apply subA_sconj in H. 
      revert H; apply scRw; intros.
      apply subA_pointto in H; simpl in H; auto.
      apply IHl; eauto.
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
    | (_ ** _) _ _ =>
      eapply scRw in H;
        [ idtac | intros ? ? Hf; subA_normalize_in Hf; exact Hf ..]
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
    | subA _ _ (List.nth _ (distribute _ _ _ _ _ _) _) _ _ => apply distribute_subA in H; auto
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

Definition WhileI (I : assn) (b : bexp) (c : cmd) := nosimpl (Cwhile b c).

Lemma safe_ex {T : Type} (Q : T -> assn) ntrd bspec tid n C s h x:
  @safe_nt ntrd bspec tid n C s h (Q x) ->
  @safe_nt ntrd bspec tid n C s h (Ex x, Q x).
Proof.
  revert n C s h ; induction n; intros C s h H; simpl in *; eauto.
  repeat split; intuition.
  - eexists; eauto.
  - destruct (H3 hF h0 c' ss' H4 H6 H7) as (? & ? & ? & ? & ? & ?).
    exists x0, x1; intuition.
  - destruct (H5 j c' H4) as (? & ? & ? & ? & ? & ? ).
    exists x0, x1; intuition.
Qed.  
    
Lemma rule_ex {T : Type} (P Q : T -> assn) ntrd bspec tid C:
  (forall x, @CSL ntrd bspec tid (P x) C (Q x)) ->
  @CSL ntrd bspec tid (Ex x, P x) C (Ex x, Q x).
Proof.
  intros H; simpl; intros s h [x Hsat] n; specialize (H x s h Hsat n); simpl in *.
  eapply safe_ex; apply H.
Qed.

Ltac hoare_forward :=
  match goal with
    | [ |- CSL ?bspec ?tid (?P1 \\// ?P2) ?C ?Q ] =>
      eapply rule_disj; hoare_forward
    | [ |- CSL ?bspec ?tid (Ex _, _) ?C ?Q ] =>
      eapply rule_ex; intros ?
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
    | [ |- CSL ?bspec ?tid ?P (WhileI ?I ?b ?c) ?Q ] => 
      let Hf := fresh in
      eapply Hbackward; [
        eapply Hforward; [apply (@rule_while _ _ _ I) | idtac] |
        idtac
      ]
  end.



Section pmap.
  Require Import NPeano.
  Require Import Arith.
  Require Import List.
  Import ListNotations.
  Local Open Scope list_scope.
  Local Close Scope exp_scope.
  Local Open Scope nat_scope.

  Definition ele (x y : exp) := (nosimpl (fun s (h : pheap) => edenot x s <= edenot y s)%Z).
  Notation "x '<==' y" := (ele x y) (at level 70, no associativity).
  Definition elt (x y : exp) := (nosimpl (fun s (h : pheap) => edenot x s < edenot y s)%Z).
  Notation "x '<<' y" := (elt x y) (at level 70, no associativity).

  Variable ntrd : nat.
  Variable len : nat.
  
  Local Notation I := (Var 4).

  Notation Enum' x := (Enum (Z.of_nat x)).
  Variable f : nat -> Z.
  Definition inv (i : nat) :=
    Ex ix, !(I == Enum' (ix * ntrd + i)) **
      nth i (distribute ntrd ARR (ix * ntrd + i) (fun i => f i + 1)%Z (nt_step ntrd) 0) emp **
      nth i (distribute ntrd ARR (len - (ix * ntrd + i)) (fun i => f i) (nt_step ntrd) (ix * ntrd + i)) emp.

  Definition map_ker (i : nat) :=
    I ::= TID%Z;;
    WhileI  (inv i) (I < Z.of_nat len) (
      X ::= [ARR + I] ;;
      [ARR + I] ::= X + 1%Z ;;
      I ::= I + Z.of_nat ntrd%Z
    )%exp.

  Require Import MyVector.
  Notation FalseP := (fun (_ : stack) (h : pheap) => False).
  Definition default : (Vector.t assn ntrd * Vector.t assn ntrd) := 
    (init (fun _ => FalseP), init (fun _ => FalseP)).

  Variable tid : Fin.t ntrd.
  Hypothesis ntrd_neq0 : ntrd <> 0.

  Ltac ex_intro x H :=
    let t := fresh in
    let H' := fresh in 
    lazymatch type of H with
      | ?X ?s ?h => pose X as t; pattern x in t;
        match goal with
          | [t' := ?X x : _ |- _] => 
            let v := fresh in
            match t with t' => 
              assert (H' : (Ex v, X v) s h) by (exists x; auto)
            end 
        end;
        clear t; clear H; rename H' into H
    end.

  Ltac ex_intros vs H :=
    match vs with
      | tt => idtac
      | (?v, ?vs) => ex_intro v H; ex_intros vs H
    end.

  Lemma map_correct :
    CSL (fun n => default) tid
    (List.nth (nat_of_fin tid) (distribute ntrd ARR len f (nt_step ntrd) 0) emp **
     !(TID == Z_of_fin tid))
    (map_ker (nat_of_fin tid))
    (List.nth (nat_of_fin tid) (distribute ntrd ARR len (fun x => f x + 1)%Z (nt_step ntrd) 0) emp).
  Proof.
    assert (Htid : nat_of_fin tid < ntrd) by (destruct (Fin.to_nat _); simpl in *; auto).
    unfold map_ker.
    eapply rule_seq.
    { hoare_forward; intros ? ? H'.
      destruct H' as [v H']; subA_normalize_in H'. simpl in H'. exact H'. }
    hoare_forward.
    eapply Hbackward.
    Focus 2.
      intros s h H; sep_normal_in H.
      sep_split_in H.
      unfold bexp_to_assn in HP; simpl in HP.
      Require Import ZArith.
      destruct (Z_lt_dec _ _) as [HP' | _]; [|congruence]; clear HP.
      unfold inv in H.
      destruct H as [ix H]. sep_split_in H.
      red in HP; simpl in HP; destruct (Z_eq_dec _ _) as [HP'' | ]; [|congruence]; clear HP.
      rewrite HP'' in HP'; apply Nat2Z.inj_lt in HP'.
      eapply scRw in H; [|intros ? ? H'; exact H' | intros ? ? H' ].
      Focus 2.
      apply skip_arr_unfold in H'; auto; [exact H'| omega].
      assert ((I === Z.of_nat (ix * ntrd + nat_of_fin tid)) s emp_ph) by (unfold_conn; auto).
      sep_combine_in H.
      ex_intro ix H; exact H. 
    
    eapply rule_seq. 
    hoare_forward.
    hoare_forward.
      apply inde_distribute; auto; repeat (constructor; prove_indeE).
      apply inde_distribute; auto; repeat (constructor; prove_indeE).
      intros ? ? H; apply H.

    eapply rule_seq.
    hoare_forward.
    hoare_forward.
      apply inde_distribute; auto; repeat (constructor; prove_indeE).
      apply inde_distribute; auto; repeat (constructor; prove_indeE).
      intros ? ? H; apply H.
    
    eapply Hforward.
    hoare_forward.
    hoare_forward.
      intros ? ? H.
      destruct H as [v H].
      simpl in H. 
      eapply scRw in H; [| | intros ? ? Hf; exact Hf].
      Focus 2.
        intros ? ? Hf. eapply subA_sconj in Hf.
        subA_normalize_in Hf. simpl in Hf. 
        exact Hf.
      ex_intro v H; simpl in H; exact H.
    
    unfold inv; intros s h H. destruct H as (ix & v & H); simpl in H.
    sep_split_in H.
    exists (S ix).
    sep_split; [unfold_conn; simpl in *|].
    red; simpl; destruct (Z.eq_dec _ _); simpl in *; auto. 
    repeat first [rewrite Nat2Z.inj_add in * | rewrite Nat2Z.inj_mul in *]; simpl; omega.
    cutrewrite (len - (ix * ntrd + nat_of_fin tid) - ntrd = 
                len - (S ix * ntrd + nat_of_fin tid)) in H; [|simpl; omega].
    cutrewrite (ntrd + ix * ntrd + nat_of_fin tid = 
                S ix * ntrd + nat_of_fin tid) in H; [|simpl; omega].
    apply scC. sep_cancel.
    rewrite skip_arr_unfold.
    rewrite <-skip_arr_unfold in H0.
    Definition mark (T : Type) := nosimpl (fun x : T => x).
    Lemma marking (T : Type) : forall x : T, x = mark x.
    Proof. intros; unfold mark; simpl; auto. Qed.

    Ltac destruct_ex_in H tac :=
      let rec go vs :=
        lazymatch type of H with
          | (Ex _, _) ?s ?h =>
            let v := fresh "v" in destruct H as [v H]; idtac; go (v, vs)
          | _ => tac; ex_intros vs H
        end in
      go tt.

      destruct_ex_in H ltac:(
        sep_normal_in H;
        sep_split_in H;
        find_enough_resource (ARR + I)%exp H; sep_combine_in H).
      exact H.
      hoare_forward.
      hoare_forward.

      Lemma distribute_inde nt e n f dist s
      
      

Section map.
  Definition ele (x y : exp) := (nosimpl (fun s (h : pheap) => edenot x s <= edenot y s)%Z).
  Notation "x '<==' y" := (ele x y) (at level 70, no associativity).
  Definition elt (x y : exp) := (nosimpl (fun s (h : pheap) => edenot x s < edenot y s)%Z).
  Notation "x '<<' y" := (elt x y) (at level 70, no associativity).
  Local Notation I := (Var 4).
  Variable len : nat.
  Variable ntrd : nat.
  Notation ntrdZ := (Z.of_nat ntrd).
  Variable f : nat -> Z.
  Definition loop_inv : assn :=
    Ex x : nat,
      is_array ARR x (fun i => Z.succ (f i)) **
      is_array (ARR + Z.of_nat x) (len - x) (fun j => f (j + x)) **
      !(I === Z.of_nat x) ** !(pure (x < len))%nat.

  Definition map :=
    I ::= 0%Z;;
    WhileI loop_inv (I < Z.of_nat len) (
      X ::= [ARR + I] ;;
      [ARR + I] ::= X + 1%Z ;;
      I ::= I + 1%Z
    ).

  Lemma is_array_unfold : forall (n : nat) (i : nat) (fi : nat -> Z) (e : exp),
    (i < n)%nat ->
    is_array e n fi |=
      (e + Z.of_nat i) -->p (1, fi i) **
      (is_array e i fi) **
      (is_array (e + Z.succ (Z.of_nat i)) (n - i - 1) (fun j => fi (S (i + j))%nat)).
  Proof.
    induction n; intros; [omega|].
    assert (i < n \/ i = n)%nat as [Hle|] by omega; subst.
    simpl in H0.
    eapply scRw in H0; [|intros ? ? H'; exact H' | intros ? ? H'; apply (IHn i) in H'; [exact H' | auto]].
    do 2 sep_cancel.
    cutrewrite (S n - i - 1 = S (n - i - 1)); [|omega].
    simpl; apply scC; sep_cancel.
    assert (Z.of_nat i + Z.succ (Z.of_nat (n - i - 1)) = Z.of_nat n)%Z.
    (rewrite <-Zplus_succ_r_reverse, <-Znat.Nat2Z.inj_add, <-Znat.Nat2Z.inj_succ; f_equal; omega).
    assert (S (i + (n - i - 1)) = n)%nat by omega.
    sep_cancel.
    simpl in H0.
    sep_cancel.
    cutrewrite (S n - n - 1 = 0); [|omega]; simpl.
    sep_normal; sep_cancel.
  Qed.

  Lemma is_array_S : forall (n : nat) (fi : nat -> Z) (e : exp),
    is_array e (S n) fi |= e -->p (1, fi 0) ** is_array (e + 1%Z) n (fun i => fi (S i)).
  Proof.
    induction n as [|n]; [simpl|]; intros; sep_cancel.
    cutrewrite (is_array e (S (S n)) fi =
                ((e + Z.of_nat (S n)) -->p (1, fi (S n)) ** is_array e (S n) fi)) in H; [|auto].
    cutrewrite (is_array (e + 1%Z) (S n) (fun i : nat => fi (S i)) =
                (e + 1%Z + Z.of_nat n -->p (1, fi (S n)) ** 
                is_array (e + 1%Z) n (fun i : nat => fi (S i)))); [|auto].
    apply scCA. rewrite Znat.Nat2Z.inj_succ in H. sep_cancel.
    apply IHn in H. auto.
  Qed.

  Lemma Ex_intro {T : Type} (P : T -> assn) (x : T) :P x |= (Ex x, P x).
  Proof. intros; exists x; auto. Qed.

  Lemma map_correct (tid : Fin.t ntrd) (bspec : Bdiv.barrier_spec ntrd) :
    CSL bspec tid (is_array ARR len f) map (is_array ARR len (fun i => Z.succ (f i))).
  Proof.
    unfold map.
    eapply rule_seq; [hoare_forward; intros ? ? H; exact H| ].
    hoare_forward.
    eapply Hbackward.
    Focus 2.
    intros ? ? H.
    unfold loop_inv in H; sep_split_in H; destruct H; repeat sep_split_in H.
    cutrewrite (len - x = S (len - x - 1)) in H; [|unfold Apure in HP1; simpl in HP1; omega].
    eapply scRw in H; [idtac | intros ? ? H'; exact H' |
                       intros ? ? H'; apply is_array_S in H'; exact H'].
    sep_lift_in H 1.
    sep_combine_in H.

    
    
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
