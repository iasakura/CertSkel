Require Import GPUCSL.
Require Import scan_lib.
Require Import LibTactics.
Require Import Skel_lemma.

Close Scope Qc_scope.
Close Scope Q_scope.
Section Map.
Coercion Var : string >-> var.
Local Notation TID := (Var "tid").
Local Notation BID := (Var "bid").
Local Notation ARR := (Var "arr").
Local Notation OUT := (Var "out").
Local Notation X := (Var "x").
Local Notation Y := (Var "y").
Local Notation I := (Var "i").
Local Notation Len := (Var "len").

Variable ntrd : nat.
Variable nblk : nat.
Variable len : nat.
Hypothesis len_neq_0 : len <> 0.
Variable arr : Z.
Variable out : Z.
Hypothesis ntrd_neq0 : ntrd <> 0.
Hypothesis nblk_neq0 : nblk <> 0.

Variable f_ini : nat -> Z.
Variable fout : nat -> Z.
Local Close Scope exp_scope.

Local Notation nt_gr := (nblk * ntrd).

Ltac sep_rewrite lem :=
  match goal with
    | [|- ?X _ _] => pattern X
  end; erewrite lem; cbv beta. 
Ltac sep_rewrite_r lem :=
  match goal with
    | [|- ?X _ _] => pattern X
  end; erewrite <-lem; cbv beta. 

Variable aenv : assn.

(* code generators filling the function hole *)
(* func : the argument variable ->
    the command for getting the result and the return expression  *)
Variable func : var -> (cmd * exp).
Variable f_den : Z -> Z.

Import ListNotations.

Hypothesis func_fv :
  forall v, disjoint [I; ARR; OUT; BID; Len] (writes_var (fst (func v))) .
Hypothesis func_no_bar :
  forall v, barriers (fst (func v)) = nil.

(* {v == val} func {ret == f_den val} *)
Hypothesis func_denote : forall (var : var) nt (tid : Fin.t nt) (val : val),
  CSL (fun _ => default nt) tid
    (!(var === val)) (fst (func var)) (!(snd (func var) === f_den val)).
Notation perm_n n := (1 / injZ (Zn n))%Qc.

Section block_verification.
Variable bid : Fin.t nblk.

Notation zf i := (Z_of_fin i).

Section thread_verification.
Variable tid : Fin.t ntrd.

Notation gtid := (nf tid + nf bid * ntrd).

Open Scope string.

Variable dim : nat.

Definition inv :=
  Ex ix, 
    !(ARR === arr) **
    !(OUT === out) **
    !(Len === Zn len) **
    !(I === Enum' (ix * nt_gr + gtid)) **
    !(Apure (ix * nt_gr + gtid < len + nt_gr)%nat) **
    is_array_p (Gl arr) len f_ini 0 (perm_n nt_gr) **
    nth gtid (distribute nt_gr (Gl out) (ix * nt_gr) (fun i => (f_den (f_ini i)))%Z (nt_step nt_gr) 0) emp **
    nth gtid (distribute nt_gr (Gl out) (len - (ix * nt_gr)) (fun i => fout i) (nt_step nt_gr) (ix * nt_gr)) emp.

Notation GTID := (TID +C BID *C Zn ntrd).

Definition map_ker :=
  I ::= (TID +C BID *C Z.of_nat ntrd);;
  WhileI inv (I < Len) (
    X ::= [Gl ARR +o I] ;;
    (fst (func X)) ;; 
    [Gl OUT +o I] ::= (snd (func X)) ;;
    I ::= I +C Z.of_nat ntrd *C Z.of_nat nblk
  )%exp.

Ltac unfold_pures :=
  repeat lazymatch goal with
   | [H : (bexp_to_assn _) ?s (emp_ph loc) |- _] => bexp H
   | [H : _ ?s (emp_ph loc) |- _ ] => unfold_conn_in H; simpl in H
end.

Hint Rewrite Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_succ div_Zdiv : sep.

Lemma nt_gr_neq_0 : nt_gr <> 0.
Proof.
  apply Nat.neq_mul_0; tauto.
Qed.

Require Import Psatz.

Lemma id_lt_nt_gr i j n m : i < n -> j < m -> i + j * n < m * n.
Proof.
  clears_all.
  intros.
  assert (i + j * n < n + j * n) by omega.
  assert (n + j * n <= m * n) by nia.
  omega.
Qed.

Lemma nf_lt : forall n (i : Fin.t n), nf i < n.
Proof.
  clears_all; introv; destruct Fin.to_nat; simpl; omega.
Qed.

Hint Resolve nt_gr_neq_0 id_lt_nt_gr nf_lt.

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

Lemma map_correct : 
  CSL (fun n => default ntrd) tid
  (!(ARR === arr) ** 
   !(OUT === out) **
   !(Len === Zn len) **
   is_array_p (Gl arr) len f_ini 0 (perm_n nt_gr) **
   List.nth (nf tid + nf bid * ntrd) (distribute nt_gr (Gl out) len fout (nt_step nt_gr) 0) emp **
   !(BID === zf bid) ** !(TID === zf tid))

  map_ker

  ( is_array_p (Gl arr) len f_ini 0 (perm_n nt_gr) **
    List.nth (nf tid + nf bid * ntrd) (distribute nt_gr (Gl out) len (fun v=>(f_den (f_ini v)))%Z (nt_step nt_gr) 0) emp).
Proof.
  unfold map_ker.
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
        2: nia.
        sep_rewrite_in (@is_array_unfold (Gl arr) (x * nt_gr + gtid)) H; [|try first [omega | eauto]..].
        2: nia.
        rewrite <-plus_n_O in H.
      apply H. } 
      sep_combine_in H. ex_intro x H. simpl in H. exact H. } Unfocus.
    
    hoare_forward.
    eapply rule_seq. 
    { autorewrite with sep. eapply Hbackward. 
      Focus 2.
      { intros s h H.
        sep_split_in H.
        change_in H.
        { assert ((Gl arr +o (Zn x * (Zn nblk * Zn ntrd) + (zf tid + zf bid * Zn ntrd))%Z ===l
                  Gl arr +o I)%exp s (emp_ph loc)).
          { unfold_pures; unfold_conn; simpl; f_equal; nia. }
          sep_rewrite_in (mps_eq1) H; [|exact H0]. 
          assert ((Gl out +o (Zn x * (Zn nblk * Zn ntrd) + (zf tid + zf bid * Zn ntrd))%Z ===l
                  Gl out +o I)%exp s (emp_ph loc)).
          { unfold_pures; unfold_conn; simpl; f_equal; nia. }
          sep_normal_in H.
          sep_lift_in H 4.
          sep_rewrite_in (mps_eq1) H; [|exact H1]. 
          sep_combine_in H; exact H. }
        exact H. } Unfocus.
      hoare_forward; try (apply inde_distribute; auto; repeat (constructor; prove_indeE)).
      
      intros ? ? H; apply H. }
    
    eapply rule_seq.
    { (* executute the passed function *)
      eapply Hbackward.
      Focus 2.
      { intros s h H.
        sep_normal_in H.
        sep_lift_in H 1.
        exact H. } Unfocus.
      apply rule_frame.
      { apply func_denote. }
      specialize (func_fv X); simpl in func_fv.
      repeat prove_inde;
      first [apply disjoint_indeE | apply disjoint_indelE | apply disjoint_indeB]; simpl; intuition. }
    
    eapply rule_seq.
    { hoare_forward; intros ? ? H; exact H. }

    eapply Hforward.
    { hoare_forward.
      intros ? ? H; destruct H as [v H].
      subA_normalize_in H. simpl in H.
      assert ((subE I v (snd (func X)) === f_den (f_ini (x * nt_gr + gtid))) s (emp_ph loc)).
      { sep_split_in H; unfold_pures; eauto. }
      sep_rewrite_in mps_eq2 H; [|exact H0].
      ex_intro v H. exact H. }
    
    unfold inv; intros s h H. destruct H as (v & H); simpl in H.
    sep_normal_in H; sep_split_in H.
    unfold_pures; subst.
    exists (S x); autorewrite with sep.
    sep_split; try now (unfold_conn; simpl; auto; nia).
    sep_rewrite (@is_array_unfold (Gl (s ARR)) (x * nt_gr + gtid)); try omega; eauto.
    sep_rewrite_r (@skip_arr_fold' (nf tid + nf bid * ntrd) (Gl (s OUT))); try omega; eauto.
    sep_normal; simpl.
    simpl; repeat sep_cancel.
    cuts_rewrite (len - (nt_gr + x * nt_gr) = len - x * nt_gr - nt_gr); [|nia]. 
    repeat autorewrite with sep. repeat sep_cancel. }
  { unfold inv; intros s h H. apply ex_lift_l_in in H as [x H]. sep_split_in H. unfold_pures.
    rewrite HP2, HP3 in n; rewrite <-Nat2Z.inj_lt in n.
    assert (len - x * nt_gr <= nf tid + nf bid * ntrd) by (zify; omega).
    assert (nf tid + nf bid * ntrd < nt_gr) by auto.
    sep_cancel.
    (* apply scC in H; sep_rewrite_in nth_dist_nil H; try omega; eauto. *)
    (* 2: instantiate (1 :=len - x * nt_gr); intros j Hj; unfold nt_step. *)
    (* 2: rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try (zify; omega). *)
    sep_lift_in H2 1; sep_rewrite_in nth_dist_nil H2; try omega; eauto.
    2: instantiate (1 :=len - x * nt_gr); intros j Hj; unfold nt_step.
    2: rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try (zify; omega).
    rewrite minus_diag in H2; simpl in H2.
    rewrite nth_nseq in H2.
    assert (x * nt_gr <= len \/ len < x * nt_gr) as [|] by omega.
    - apply scC in H2; sep_rewrite_in nth_dist_ext H2; try omega; auto.
      2: instantiate (1 :=len - x * nt_gr); intros j Hj; simpl; unfold nt_step;
         rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try omega.
      sep_normal_in H2.
      (* sep_rewrite_in nth_dist_ext H2; try omega; auto. *)
      (* 2: instantiate (1 :=len - x * nt_gr); intros j Hj; simpl; unfold nt_step. *)
      (* 2: rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try omega. *)
      cutrewrite (x * nt_gr + (len - x * nt_gr) = len) in H2; [|omega].
      destruct Compare_dec.leb; sep_normal_in H2; sep_split; try now (unfold_conn; simpl; auto); sep_cancel.
    - (* apply scC in H2; sep_rewrite nth_dist_ext; try omega; auto. *)
      (* cutrewrite (len - x * ntrd = 0) in H2; [|omega]. *)
      cutrewrite (x * nt_gr = len + (x * nt_gr - len)) in H2; [|omega].
      assert (forall j, j < x * nt_gr - len -> nt_step nt_gr (0 + len + j) <> nf tid + nf bid * ntrd).
      { unfold nt_step; simpl; intros j Hj Hc.
        assert (len + j + nt_gr < (S x) * nt_gr) by (simpl; omega).
        assert (x * nt_gr + j + (nf tid + nf bid * ntrd) < len + j + nt_gr) by omega.
        let t := (eval simpl in (Nat.mod_add (len + j) 1 nt_gr)) in pose proof t.
        rewrite mult_1_l in H6.
        rewrite (Nat.div_mod (len + j + nt_gr) nt_gr), H6 in H4, H5; auto.
        assert (x * nt_gr  < nt_gr * ((len + j + nt_gr) / nt_gr)) by omega.
        assert (nt_gr * ((len + j + nt_gr) / nt_gr) < S x * nt_gr) by omega.
        rewrite mult_comm in H7; apply Nat.mul_lt_mono_pos_l in H7; try omega.
        rewrite mult_comm in H8; apply Nat.mul_lt_mono_pos_r in H8; omega. } 
      sep_rewrite_in_r nth_dist_ext H2; try omega; eauto.
      sep_split; auto.
      destruct Compare_dec.leb; sep_normal_in H2; repeat sep_cancel. }

  {  intros s h H; unfold inv; exists 0; simpl.
     sep_split_in H; unfold_pures; sep_split; auto.
     - unfold_conn; simpl; autorewrite with sep; congruence.
     - unfold_conn. assert (nf tid + nf bid * ntrd < nt_gr) by auto. omega.
     - rewrite <-minus_n_O, nth_nseq; destruct Compare_dec.leb; sep_normal; sep_cancel. }
Qed.
End thread_verification.

Require Import Bdiv.
Local Notation init := MyVector.init.
Definition bth_pre :=
  !(ARR === arr) **
  !(OUT === out) **
  !(Len === Zn len) **
  conj_xs (ls_init 0 ntrd (fun i =>
    is_array_p (Gl arr) len f_ini 0 (perm_n nt_gr))) **
  conj_xs (ls_init 0 ntrd (fun i =>
    skip_arr (Gl out) 0 len nt_gr fout (i + nf bid * ntrd))).

Definition tr_pres := init (fun i : Fin.t ntrd =>
  !(ARR === arr) ** 
  !(OUT === out) ** 
  !(Len === Zn len) ** 
  is_array_p (Gl arr) len f_ini 0 (perm_n nt_gr) **
  skip_arr (Gl out) 0 len nt_gr fout (nf i + nf bid * ntrd) **
  !(BID === zf bid)).

Definition bth_post  :=
  conj_xs (ls_init 0 ntrd (fun i =>
    is_array_p (Gl arr) len f_ini 0 (perm_n nt_gr))) **
  conj_xs (ls_init 0 ntrd (fun i  =>
    skip_arr (Gl out) 0 len nt_gr (fun v => f_den (f_ini v))%Z (i + nf bid * ntrd))).

Definition tr_posts := (init (fun i : Fin.t ntrd =>
  is_array_p (Gl arr) len f_ini 0 (perm_n nt_gr) **
  skip_arr (Gl out) 0 len nt_gr (fun v => f_den (f_ini v))%Z (nf i + nf bid * ntrd))).

Definition E : env := fun v =>
  if var_eq_dec v BID then Lo
  else if var_eq_dec v ARR then Lo
  else if var_eq_dec v OUT then Lo
  else if var_eq_dec v Len then Lo
  else Hi.  
Close Scope Qc_scope.
Close Scope Q_scope.
(* delete arguments of map_ker *)
Definition tid0 : Fin.t ntrd.
destruct ntrd; try omega.
exact Fin.F1.
Qed.

Definition map' : cmd.
  pose (map_ker tid0) as map'; unfold map_ker, WhileI in map'; exact map'.
Defined.

Definition bspec : (barrier_spec ntrd) := fun i => (default ntrd).

Lemma precise_false : precise (fun _ _ => False).
Proof.
  unfold precise; intros; tauto.
Qed.

Lemma map_correct_b :
  CSLp ntrd E (bth_pre ** !(BID === zf bid)) map' (bth_post).
Proof.
  applys (>> rule_par bspec tr_pres tr_posts);
  try first [omega | nia | eauto].
  - destruct ntrd; eexists; try omega; eauto.
  - unfold bspec; split; intros; unfold default; simpl; rewrite MyVector.init_spec;
    unfold CSL.low_assn, low_assn, indeP; tauto.
  - split; unfold bspec, default; simpl; rewrite MyVector.init_spec;
    apply precise_false.
  - unfold bth_pre, tr_pres; intros.
    sep_split_in H.
    istar_simplify.
    repeat sep_rewrite (@ls_star).
    repeat sep_rewrite (@ls_pure).
    sep_split.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    repeat sep_cancel.
  - unfold tr_posts, bth_post; intros s h H.
    istar_simplify_in H.
    sep_cancel.
  - intros; unfold tr_pres; rewrite MyVector.init_spec.
    unfold CSL.low_assn.
    repeat prove_low_assn; eauto.
    apply low_assn_skip_arr.
    constructor; eauto.
  - intros; unfold CSL.low_assn, tr_posts; rewrite MyVector.init_spec.
    repeat prove_low_assn. 
    constructor; eauto.
    apply low_assn_skip_arr; constructor; eauto.
  - repeat (match goal with
            | [ |- typing_exp _ _ _ ] => eapply ty_var; apply le_type_refl
            | _ => econstructor
            end); try reflexivity.
    repeat instantiate (1 := Hi).
    apply typing_cmd_Hi; eauto.
    intros.
    lets: (>>disjoint_not_in_r v (func_fv X) H).
    simpl in *.
    unfold E; repeat destruct var_eq_dec; intuition.
  - unfold tr_pres, tr_posts; intros; rewrite !MyVector.init_spec.
    unfold bspec, skip_arr.
    eapply Hbackward.
    eapply Hforward.
    apply map_correct.
    intros.
    apply H.
    intros; sep_normal_in H; sep_normal; sep_cancel.
    (* hmm.. *)
    Grab Existential Variables.
    apply Lo.
    apply Lo.
    apply Lo.
    apply 0.
Qed.

End block_verification.

Definition bl_pres : Vector.t assn nblk :=
  MyVector.init (fun b : Fin.t nblk => (bth_pre b)).
Definition bl_posts : Vector.t assn nblk :=
  MyVector.init (fun b : Fin.t nblk => (bth_post b)).

Definition bid0 : Fin.t nblk.
  destruct nblk; try omega.
  exact Fin.F1.
Qed.

Theorem map_correct_g  :
  CSLg ntrd nblk ntrd_neq0 nblk_neq0
    (!(ARR === arr) ** !(OUT === out) ** !(Len === Zn len) **
     is_array (Gl arr) len f_ini 0 **
     is_array (Gl out) len fout 0)
    (Pr nil (map' bid0))
    (is_array (Gl arr) len f_ini 0 **
     is_array (Gl out) len (fun v => f_den (f_ini v))%Z 0).
Proof.
  applys (>> rule_grid E bl_pres bl_posts).
  - intros s h H.
    unfold bl_pres, bth_pre.
    sep_split_in H.
    istar_simplify.
    repeat sep_rewrite (@ls_star nblk).
    repeat sep_rewrite (@ls_pure nblk); sep_split.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    repeat (sep_rewrite_r is_array_skip_arr); sep_cancel; eauto.
    Lemma conj_xs_init_flatten (l1 l2 : nat) (a : assn) :
      forall (s : nat) (stk : stack),
        stk
          ||= conj_xs
          (ls_init s l1
             (fun i : nat =>
                conj_xs (ls_init 0 l2 (fun j : nat => a)))) <=>
          conj_xs (ls_init (s * l2) (l1 * l2) (fun i : nat => a)).
    Proof.          
      induction l1; simpl.
      - intros; reflexivity.
      - intros; rewrite IHl1.
        rewrite ls_init_app, conj_xs_app; simpl.
        erewrite ls_init_eq.
        cutrewrite (l2 + s * l2 = s * l2 + l2); [|ring].
        rewrite <-plus_n_O.
        reflexivity.
        intros; simpl; auto.
    Qed.
    sep_rewrite conj_xs_init_flatten; simpl.
    lets Heq: (>>is_array_is_array_p_1 __ __ nt_gr); sep_rewrite_in Heq H; eauto.
    nia.
  - unfold bl_pres, bl_posts; intros.
    rewrite !MyVector.init_spec.
    eapply CSLp_backward.
    eapply CSLp_forward.
    apply (map_correct_b bid).
    intros; simpl; sep_normal; eauto.
    intros; simpl in *; sep_normal_in H; eauto.
  - unfold bl_posts, bth_post.
    intros s h H.
    istar_simplify_in H.
    sep_rewrite_in conj_xs_init_flatten H; simpl in H.
    lets Heq: (>>is_array_is_array_p_1 __ __ nt_gr); sep_rewrite Heq; eauto; try nia.
    sep_rewrite is_array_skip_arr; eauto.
  - prove_inde.
  - intros; unfold bl_pres, bth_pre.
    rewrite MyVector.init_spec.
    prove_inde;
    apply inde_conj_xs; rewrite init_length; intros;
    rewrite ls_init_spec; destruct lt_dec; prove_inde;
    apply inde_distribute; prove_indeE.
  - intros bid; unfold bl_pres, bth_pre; rewrite MyVector.init_spec.
    Hint Constructors typing_exp typing_lexp.
    repeat prove_low_assn; eauto; apply low_assn_conj_xs; rewrite init_length; intros;
    rewrite ls_init_spec; destruct lt_dec; try repeat prove_low_assn.
    constructor; eauto.
    apply low_assn_skip_arr; eauto;
    prove_low_assn.
  - intros.
    unfold bl_posts, bth_post.
    rewrite MyVector.init_spec.
    has_no_vars_assn; apply has_no_vars_conj_xs; rewrite init_length; intros; rewrite ls_init_spec;
    repeat has_no_vars_assn.
    apply has_no_vars_is_array_p; repeat constructor.
    apply has_no_vars_skip_arr; repeat constructor.
  - simpl; tauto.
  - unfold E; eauto.
  - unfold E; eauto.
  - eauto.
  - eauto.
  - simpl; eauto.
Qed.
    
End Map.