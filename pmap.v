Require Import GPUCSL.
Section Map.
Local Notation TID := (Var 0).
Local Notation BID := (Var 1).
Local Notation ARR := (Var 2).
Local Notation X := (Var 3).
Local Notation Y := (Var 4).
Local Notation I := (Var 5).

Variable ntrd : nat.
Variable nblk : nat.
Variable len : nat.
Hypothesis len_neq_0 : len <> 0.

Variable f : nat -> Z.

Local Close Scope exp_scope.

Local Notation nt_gr := (ntrd * nblk).

Definition inv (i : nat) (arr : Z) :=
  Ex ix, 
    !(ARR === arr) **
    !(I === Enum' (ix * nt_gr + i)) **
    !(Apure (ix * nt_gr + i < len + nt_gr)%nat) **
    nth i (distribute nt_gr (Gl ARR) (ix * nt_gr) (fun i => f i + 1)%Z (nt_step nt_gr) 0) emp **
    nth i (distribute nt_gr (Gl ARR) (len - (ix * nt_gr)) (fun i => f i) (nt_step nt_gr) (ix * nt_gr)) emp.

Definition map_ker (i : nat) (arr : Z) :=
  I ::= (TID +C BID *C Z.of_nat ntrd);;
  WhileI  (inv i arr) (I < Z.of_nat len) (
    X ::= [Gl ARR +o I] ;;
    [Gl ARR +o I] ::= X + 1%Z ;;
    I ::= I +C Z.of_nat ntrd *C Z.of_nat nblk
  )%exp.

Hypothesis ntrd_neq0 : ntrd <> 0.
Hypothesis nblk_neq0 : nblk <> 0.

Ltac unfold_pures :=
  repeat lazymatch goal with
   | [H : (bexp_to_assn _) ?s (emp_ph loc) |- _] => bexp H
   | [H : _ ?s (emp_ph loc) |- _ ] => unfold_conn_in H; simpl in H
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

Require Import LibTactics.

Notation zf i := (Z_of_fin i).

Lemma nt_gr_neq_0 : nt_gr <> 0.
Proof.
  apply Nat.neq_mul_0; tauto.
Qed.

Require Import Psatz.

Lemma id_lt_nt_gr i j n m : i < n -> j < m -> i + j * n < n * m.
Proof.
  intros.
  assert (i + j * n < n + j * n) by omega.
  assert (n + j * n <= n * m) by nia.
  omega.
Qed.

Lemma nf_lt : forall n (i : Fin.t n), nf i < n.
Proof.
  introv; destruct Fin.to_nat; simpl; omega.
Qed.

Hint Resolve nt_gr_neq_0 id_lt_nt_gr nf_lt.


Lemma map_correct : forall (tid : Fin.t ntrd) (bid : Fin.t nblk) (arr : Z), 
  CSL (fun n => default ntrd) tid
  (!(ARR === arr) ** 
   List.nth (nf tid + nf bid * ntrd) (distribute nt_gr (Gl arr) len f (nt_step nt_gr) 0) emp **
   !(BID === zf bid) ** !(TID === zf tid))
  (map_ker (nf tid + nf bid * ntrd) arr)
  (List.nth (nf tid + nf bid * ntrd) (distribute nt_gr (Gl arr) len (fun x => f x + 1)%Z (nt_step nt_gr) 0) emp).
Proof.
  (* assert (Htid : nat_of_fin tid < ntrd) by (destruct (Fin.to_nat _); simpl in *; auto). *)
  unfold map_ker; introv.
  eapply rule_seq.
  { hoare_forward; intros ? ? H'.
    destruct H' as [v H'].
    subA_normalize_in H'. simpl in H'. exact H'. }
  hoare_forward.
  { unfold inv; eapply Hbackward.
    Focus 2.
    { intros s h H; apply ex_lift_l_in in H as [x H]; sep_split_in H.
      change_in H.
      { unfold_pures.
        sep_rewrite_in skip_arr_unfold' H; [|try first [omega | eauto]..]. 
      2: zify; omega.
      apply H. } 
      sep_combine_in H. ex_intro x H. simpl in H. exact H. } Unfocus.
    
    hoare_forward.
    eapply rule_seq. 
    { autorewrite with sep. eapply Hbackward. 
      Focus 2.
      { intros s h H.
        sep_split_in H.
        change_in H.
        { assert ((Gl ARR +o (Zn x * (Zn ntrd * Zn nblk) + (zf tid + zf bid * Zn ntrd))%Z ===l
                  Gl ARR +o I)%exp s (emp_ph loc)).
          { unfold_pures; unfold_conn; simpl; f_equal; omega. }
          sep_rewrite_in (mps_eq1) H; [|exact H0]. exact H. }
          sep_combine_in H; exact H. } Unfocus.
      hoare_forward; try (apply inde_distribute; auto; repeat (constructor; prove_indeE)).
      intros ? ? H; apply H. }
    
    eapply rule_seq.
    { hoare_forward.
      intros ? ? H; apply H. }
    
    eapply Hforward.
    { hoare_forward.
      intros ? ? H; destruct H as [v H].
      subA_normalize_in H. simpl in H. ex_intro v H. exact H. }
    
    unfold inv; intros s h H. destruct H as (v & H); simpl in H.
    sep_split_in H. unfold_pures; subst.
    exists (S x); autorewrite with sep.
    sep_split; try now (unfold_conn; simpl; auto; nia).
    sep_rewrite_r skip_arr_fold'; try omega; eauto.
    sep_normal; simpl; repeat sep_cancel.
    autorewrite with sep. repeat sep_cancel.
    cuts_rewrite (len - (nt_gr + x * nt_gr) = len - x * nt_gr - nt_gr); auto.
    zify; omega. }

  { unfold inv; intros s h H. apply ex_lift_l_in in H as [x H]. sep_split_in H. unfold_pures.
    rewrite HP1 in n; rewrite <-Nat2Z.inj_lt in n.
    assert (len - x * nt_gr <= nf tid + nf bid * ntrd) by (zify; omega).
    assert (nf tid + nf bid * ntrd < nt_gr) by auto.
    apply scC in H; sep_rewrite_in nth_dist_nil H; try omega; eauto.
    2: instantiate (1 :=len - x * nt_gr); intros j Hj; unfold nt_step.
    2: rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try (zify; omega).
    rewrite minus_diag in H; simpl in H.
    rewrite nth_nseq in H.
    Lemma distribute_eq e e' stk i nt n f' dist:
      i < nt -> (forall i, dist i < nt) ->
      (e ===l e') stk (emp_ph loc) ->
      forall s, stk ||= nth i (distribute nt e n f' dist s) emp <=>
                        nth i (distribute nt e' n f' dist s) emp.
    Proof.
      induction n; simpl; intros; [split; eauto|].
      rewrite !nth_add_nth; [|rewrite distribute_length; eauto..].
      destruct beq_nat; eauto.
      assert ((e +o Zn s ===l e' +o Zn s) stk (emp_ph loc)).
      { unfold_conn_all; simpl in *; rewrite H1; eauto. }
      rewrite mps_eq1; [|exact H2].
      split; intros; sep_cancel; apply IHn; auto.
    Qed.
    assert ((Gl arr ===l Gl ARR) s (emp_ph loc)) by (unfold_conn; simpl; congruence).
    sep_rewrite distribute_eq; eauto.
    assert (x * nt_gr <= len \/ len < x * nt_gr) as [|] by omega.
    - apply scC in H; sep_rewrite_in nth_dist_ext H; try omega; auto.
      2: instantiate (1 :=len - x * nt_gr); intros j Hj; simpl; unfold nt_step;
         rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try omega.
      cutrewrite (x * nt_gr + (len - x * nt_gr) = len) in H; [|omega].

      destruct leb; sep_normal_in H; sep_cancel.
    - (* apply scC in H; sep_rewrite nth_dist_ext; try omega; auto. *)
      (* cutrewrite (len - x * ntrd = 0) in H; [|omega]. *)
      cutrewrite (x * nt_gr = len + (x * nt_gr - len)) in H; [|omega].
      sep_rewrite_in_r nth_dist_ext H; try omega; eauto.
      destruct leb; sep_normal_in H; sep_cancel.
      unfold nt_step; simpl; intros j Hj Hc.
      assert (len + j + nt_gr < (S x) * nt_gr) by (simpl; omega).
      assert (x * nt_gr + j + (nf tid + nf bid * ntrd) < len + j + nt_gr) by omega.
      let t := (eval simpl in (Nat.mod_add (len + j) 1 nt_gr)) in pose proof t.
      rewrite mult_1_l in H6.
      rewrite (Nat.div_mod (len + j + nt_gr) nt_gr), H6 in H4, H5; auto.
      assert (x * nt_gr  < nt_gr * ((len + j + nt_gr) / nt_gr)) by omega.
      assert (nt_gr * ((len + j + nt_gr) / nt_gr) < S x * nt_gr) by omega.
      rewrite mult_comm in H7; apply Nat.mul_lt_mono_pos_l in H7; try omega.
      rewrite mult_comm in H8; apply Nat.mul_lt_mono_pos_r in H8; omega. }

  {  intros s h H; unfold inv; exists 0; simpl.
     sep_split_in H; unfold_pures; sep_split.
     - unfold_conn; simpl; eauto.
     - unfold_conn; simpl; autorewrite with sep; congruence.
     - unfold_conn. assert (nf tid + nf bid * ntrd < nt_gr) by auto. omega.
     - assert ((Gl ARR ===l Gl arr) s (emp_ph loc)) by (unfold_conn; simpl; congruence).
       sep_rewrite distribute_eq; eauto.
       rewrite <-minus_n_O, nth_nseq; destruct leb; sep_normal; sep_cancel. }
Qed.

(* delete arguments of map_ker *)
Definition map' : cmd.
  pose (map_ker 0) as map'; unfold map_ker, WhileI in map'; exact map'.
Defined.

Definition block_pre := distribute nblk 

End Map.
