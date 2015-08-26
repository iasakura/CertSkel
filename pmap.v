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
  Ex ix, !(I == Enum' (ix * ntrd + i)) ** !(Apure (ix * ntrd + i - ntrd < len)%nat) **
     nth i (distribute ntrd ARR (ix * ntrd + i) (fun i => f i + 1)%Z (nt_step ntrd) 0) emp **
     nth i (distribute ntrd ARR (len - (ix * ntrd + i)) (fun i => f i) (nt_step ntrd) (ix * ntrd + i)) emp.

Definition map_ker (i : nat) :=
  I ::= TID%Z;;
  WhileI  (inv i) (I < Z.of_nat len) (
    X ::= [ARR + I] ;;
    [ARR + I] ::= X + 1%Z ;;
    I ::= I + Z.of_nat ntrd%Z
  )%exp.

Variable tid : Fin.t ntrd.
Hypothesis ntrd_neq0 : ntrd <> 0.

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
    destruct H' as [v H']; subA_normalize_in H'. simpl in H'. exact H'. }
  hoare_forward.
  { eapply Hbackward.
    Focus 2.
    { intros s h H; sep_normal_in H.
      sep_split_in H.
      unfold bexp_to_assn in HP; simpl in HP.
      destruct (Z_lt_dec _ _) as [HP' | _]; [|congruence]; clear HP.
      unfold inv in H.
      destruct H as [ix H]. sep_split_in H.
      red in HP; simpl in HP; destruct (Z_eq_dec _ _) as [HP'' | ]; [|congruence]; clear HP.
      rewrite HP'' in HP'; apply Nat2Z.inj_lt in HP'.
      eapply scRw in H; [|intros ? ? H'; exact H' | intros ? ? H' ].
      Focus 2.
      { apply skip_arr_unfold in H'; auto; [exact H'| omega]. } Unfocus.
      assert ((I === Z.of_nat (ix * ntrd + nat_of_fin tid)) s emp_ph) by (unfold_conn; auto).
      assert (pure (ix * ntrd + nat_of_fin tid < len) s emp_ph) by (unfold_conn; auto).
      sep_combine_in H.
      ex_intro ix H; exact H. } Unfocus.
    
    eapply rule_seq. 
    { hoare_forward.
      hoare_forward; try (apply inde_distribute; auto; repeat (constructor; prove_indeE)).
      intros ? ? H; apply H. }

    eapply rule_seq.
    { hoare_forward.
      hoare_forward.
      intros ? ? H; apply H. }
    
    eapply Hforward.
    { hoare_forward.
      hoare_forward.
      intros ? ? H.
      destruct H as [v H].
      simpl in H. 
      eapply scRw in H; [| | intros ? ? Hf; exact Hf].
      Focus 2.
      { intros ? ? Hf. eapply subA_sconj in Hf.
        subA_normalize_in Hf. simpl in Hf. 
        exact Hf. } Unfocus.
      ex_intro v H; simpl in H; exact H. }
    
    unfold inv; intros s h H. destruct H as (ix & v & H); simpl in H.
    sep_split_in H.
    exists (S ix).
    sep_split; [unfold_conn; simpl in *|.. ].
    { red; simpl; destruct (Z.eq_dec _ _); simpl in *; auto. 
      repeat first [rewrite Nat2Z.inj_add in * | rewrite Nat2Z.inj_mul in *]; simpl; omega. }
    { unfold_conn; unfold subA' in HP3; simpl in *. 
      revert HP3; generalize (ix * ntrd); intros; omega. }

    { cutrewrite (len - (ix * ntrd + nat_of_fin tid) - ntrd = 
                len - (S ix * ntrd + nat_of_fin tid)) in H; [|simpl; omega].
      cutrewrite (ntrd + ix * ntrd + nat_of_fin tid = 
                  S ix * ntrd + nat_of_fin tid) in H; [|simpl; omega].
      apply scC. sep_cancel.

      lazymatch type of H0 with
        | appcontext f [v] => let x := context f [Enum (Z.of_nat (ix * ntrd + nat_of_fin tid))] in 
                              assert x
      end; repeat sep_cancel.
      lazymatch type of H1 with
        | appcontext c [Evar X] => 
          let x := context c [Enum (f (ix * ntrd + nat_of_fin tid)%nat)] in 
          assert x
      end; repeat sep_cancel.
    
      apply scC in H2.
      apply (skip_arr_fold ARR (fun i => (f i + 1)%Z) ntrd_neq0 ix Htid) in H2; auto. } }

  { unfold inv; intros s h H; sep_split_in H.
    assert (s I >= Z.of_nat len)%Z.
    { unfold bexp_to_assn in HP; simpl in HP.
      destruct (Z_lt_dec _ _); simpl in *; try congruence. }
    destruct H as [ix H]; sep_split_in H.
    assert (ix * ntrd + nat_of_fin tid >= len).
    { unfold bexp_to_assn in HP0; simpl in HP0; destruct (Z.eq_dec _ _); try congruence.
      rewrite e in H0. apply Nat2Z.inj_ge in H0; auto. }
    cutrewrite (len - (ix * ntrd + nat_of_fin tid) = 0) in H; [|omega].
    match type of H with ((_ ** ?P) s h) => cutrewrite (P = emp) in H end;
      [|simpl; simpl_nth; (destruct Compare_dec.leb); auto].
    sep_normal_in H.
    apply (@nth_dist_ext _ ARR (fun i => (f i + 1)%Z) _ ntrd_neq0 (nt_step ntrd) (ix * ntrd + nat_of_fin tid - len) 0 len Htid); auto;
    [|cutrewrite (len + (ix * ntrd + nat_of_fin tid - len) = (ix * ntrd + nat_of_fin tid)); [auto|omega]].
    intros j Hj; simpl; unfold nt_step; unfold Apure in HP1.
    intros Hc.
    destruct ix.
    { assert (j + len < nat_of_fin tid) by (simpl in Hj; omega).
      assert (j + len < ntrd) by omega.
      rewrite Nat.mod_small in Hc; omega. }
    { cutrewrite (S ix * ntrd + nat_of_fin tid - ntrd = ix * ntrd + nat_of_fin tid) in HP1; [|simpl; generalize (ix * ntrd); intros; omega].
      assert (ix * ntrd + nat_of_fin tid < len + j) by omega.
      assert (len + j < S ix * ntrd + nat_of_fin tid) by omega.
      rewrite (div_mod (len + j) ntrd ntrd_neq0), Hc in H2, H3.
      assert (ix * ntrd < ntrd * ((len + j) / ntrd)) by omega.
      assert (ntrd * ((len + j) / ntrd) < S ix * ntrd) by omega.
      rewrite (mult_comm _ ntrd) in H4; rewrite (mult_comm _ ntrd) in H5.
      apply <-Nat.mul_lt_mono_pos_l in H4; apply <-Nat.mul_lt_mono_pos_l in H5; omega. } }
      
  { intros s h H; sep_split_in H; unfold inv.
    unfold eeq in HP, HP0; simpl in *.
    exists 0; simpl; repeat sep_split.
    - unfold bexp_to_assn; simpl; destruct (Z.eq_dec _ _); congruence.
    - unfold Apure. omega.
    - match goal with
        | [|- (?X ** _) s h] => assert (emp |= X)
      end.
      { intros.
        apply (nth_dist_nil _ _ ntrd_neq0) with (next := nat_of_fin tid); auto.
        simpl; unfold nt_step; intros j Hj Hc.
        rewrite Nat.mod_small in Hc; omega.
        rewrite minus_diag; simpl in H0; simpl_nth; destruct Compare_dec.leb; auto. }
      eapply scRw; [intros ? ? Ht; apply H0; exact Ht | intros ? ? Ht; exact Ht |].
      sep_normal.
      apply skip_arr_init; auto. }
Qed.
End Map.
