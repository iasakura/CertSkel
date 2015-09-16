Require Import GPUCSL.

Section Map.
Local Notation TID := (Var 0).
Local Notation ARR := (Var 1).
Local Notation X := (Var 2).
Local Notation Y := (Var 3).
Local Notation I := (Var 4).

Variable ntrd : nat.
Variable len : nat.
Hypothesis len_neq_0 : len <> 0.

Variable f : nat -> Z.

Local Close Scope exp_scope.

Definition inv (i : nat) :=
  Ex ix, !(I === Enum' (ix * ntrd + i)) ** !(Apure (ix * ntrd + i < len + ntrd)%nat) **
     nth i (distribute ntrd ARR (ix * ntrd) (fun i => f i + 1)%Z (nt_step ntrd) 0) emp **
     nth i (distribute ntrd ARR (len - (ix * ntrd)) (fun i => f i) (nt_step ntrd) (ix * ntrd)) emp.

Definition map_ker (i : nat) :=
  I ::= TID%Z;;
  WhileI  (inv i) (I < Z.of_nat len) (
    X ::= [ARR + I] ;;
    [ARR + I] ::= X + 1%Z ;;
    I ::= I + Z.of_nat ntrd%Z
  )%exp.

Variable tid : Fin.t ntrd.
Hypothesis ntrd_neq0 : ntrd <> 0.

Ltac unfold_pures :=
  repeat lazymatch goal with
   | [H : (bexp_to_assn _) ?s emp_ph |- _] => bexp H
   | [H : _ ?s emp_ph |- _ ] => unfold_conn_in H; simpl in H
end.

Ltac sep_rewrite lem :=
  match goal with
    | [|- ?X _ _] => pattern X
  end; erewrite lem; cbv beta. 
Ltac sep_rewrite_r lem :=
  match goal with
    | [|- ?X _ _] => pattern X
  end; erewrite <-lem; cbv beta. 

Hint Rewrite Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_succ div_Zdiv : sep.
Lemma map_correct :
  CSL (fun n => default ntrd) tid
  (List.nth (nat_of_fin tid) (distribute ntrd ARR len f (nt_step ntrd) 0) emp **
   !(TID === Z_of_fin tid))
  (map_ker (nat_of_fin tid))
  (List.nth (nat_of_fin tid) (distribute ntrd ARR len (fun x => f x + 1)%Z (nt_step ntrd) 0) emp).
Proof.
  assert (Htid : nat_of_fin tid < ntrd) by (destruct (Fin.to_nat _); simpl in *; auto).
  unfold map_ker.
  eapply rule_seq.
  { hoare_forward; intros ? ? H'.
    destruct H' as [v H'].
    subA_normalize_in H'. simpl in H'. exact H'. }
  hoare_forward.
  { unfold inv; eapply Hbackward.
    Focus 2.
    { intros s h H; apply ex_lift_l_in in H as [x H]; sep_split_in H.
      change_in H; [unfold_pures|].
      sep_rewrite_in skip_arr_unfold' H; [|try omega..].
      2: rewrite HP0 in l; apply Nat2Z.inj_lt in l; omega.
      apply H. sep_combine_in H. ex_intro x H. simpl in H. exact H. } Unfocus.
    
    hoare_forward.
    eapply rule_seq. 
    { autorewrite with sep. eapply Hbackward. 
      Focus 2.
      intros s h H.
      sep_split_in H.
      change_in H.
      assert ((ARR + (Z.of_nat x * Z.of_nat ntrd + Z_of_fin tid)%Z === ARR + I)%exp s emp_ph).
      unfold_pures; unfold_conn; simpl; omega.
      sep_rewrite_in (mps_eq1) H; [|exact H0]. exact H.
      sep_combine_in H; exact H.
      hoare_forward; try (apply inde_distribute; auto; repeat (constructor; prove_indeE)).
      intros ? ? H; apply H. }

    eapply rule_seq.
    { hoare_forward.
      intros ? ? H; apply H. }
    
    eapply Hforward.
    { hoare_forward.
      intros ? ? H; destruct H as [v H]. subA_normalize_in H. simpl in H. ex_intro v H. exact H. }
    
    unfold inv; intros s h H. destruct H as (v & H); simpl in H.
    sep_split_in H; unfold_pures; subst.
    exists (S x); autorewrite with sep.
    sep_split.
    - unfold_conn; simpl. rewrite Z.mul_succ_l. omega.
    - unfold_conn. apply Nat2Z.inj_lt; autorewrite with sep; rewrite Z.mul_succ_l; omega.
    - sep_rewrite_r skip_arr_fold'; try omega.
      sep_normal. simpl. repeat sep_cancel.
      rewrite (plus_comm ntrd (x * ntrd)), Nat.sub_add_distr, (plus_comm _ ntrd).
      apply scC. sep_cancel.
      autorewrite with sep. sep_cancel. }

  { unfold inv; intros s h H. apply ex_lift_l_in in H as [x H]. sep_split_in H.
    unfold_pures.
    rewrite HP0 in n; rewrite <-Nat2Z.inj_lt in n.
    assert (x * ntrd <= len \/ len < x * ntrd) as [|] by omega.
    - apply scC in H; sep_rewrite_in nth_dist_nil H; try omega; eauto.
      2: instantiate (1 :=len - x * ntrd); intros j Hj; unfold nt_step;
         rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try omega.
      rewrite minus_diag in H; simpl in H.
      apply scC in H; sep_rewrite_in nth_dist_ext H; try omega; eauto.
      2: instantiate (1 :=len - x * ntrd); intros j Hj; simpl; unfold nt_step;
         rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try omega.
      cutrewrite (x * ntrd + (len - x * ntrd) = len) in H; [|omega].
      rewrite nth_nseq in H; destruct leb; sep_normal_in H; auto.
    - cutrewrite (len - x * ntrd = 0) in H; [|omega].
      cutrewrite (x * ntrd = len + (x * ntrd - len)) in H; [|omega].
      sep_rewrite_in_r nth_dist_ext H; try omega; eauto.
      simpl in H; rewrite nth_nseq in H; destruct leb; sep_normal_in H; sep_cancel.
      unfold nt_step; simpl; intros j Hj Hc.
      assert (len + j + ntrd < (S x) * ntrd) by (simpl; omega).
      assert (x * ntrd + j + (nf tid) < len + j + ntrd ) by omega.
      let t := (eval simpl in (Nat.mod_add (len + j) 1 ntrd)) in pose proof t. rewrite mult_1_l in H3.
      rewrite (Nat.div_mod (len + j + ntrd) ntrd ntrd_neq0), H3 in H1, H2; auto.
      assert (x * ntrd  < ntrd * ((len + j + ntrd) / ntrd)) by omega.
      assert (ntrd * ((len + j + ntrd) / ntrd) < S x * ntrd) by omega.
      rewrite mult_comm in H4; apply Nat.mul_lt_mono_pos_l in H4; try omega.
      rewrite mult_comm in H5; apply Nat.mul_lt_mono_pos_r in H5; omega. }

  {  intros s h H; unfold inv; exists 0; simpl.
     sep_split_in H; unfold_pures; sep_split.
     - unfold_conn; simpl; congruence.
     - unfold_conn; omega.
     - rewrite <-minus_n_O, nth_nseq; destruct leb; sep_normal; sep_cancel. }
Qed.
End Map.
