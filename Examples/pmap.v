Require Import GPUCSL.
Require Import scan_lib.

Section Map.
Local Notation TID := (Var "tid").
Local Notation BID := (Var "bid").
Local Notation ARR := (Var "arr").
Local Notation OUT := (Var "out").
Local Notation X := (Var "x").
Local Notation Y := (Var "y").
Local Notation I := (Var "i").

Variable ntrd : nat.
Variable nblk : nat.
Variable len : nat.
Hypothesis len_neq_0 : len <> 0.

Variable f : nat -> Z.

Local Close Scope exp_scope.

Local Notation nt_gr := (nblk * ntrd).
Notation perm_n n := (1 / injZ (Zn n))%Qc.

Definition inv (i : nat) (arr out : Z) (fout : nat -> Z) :=
  Ex ix, 
    !(ARR === arr) **
    !(OUT === out) **
    !(I === Enum' (ix * nt_gr + i)) **
    (* !(Apure (ix * nt_gr + i < len + nt_gr)%nat) ** *)
    is_array_p (Gl arr) len f 0 (perm_n nt_gr) ** 
    nth i (distribute nt_gr (Gl out) len
      (fun j => if lt_dec j (ix * nt_gr + i)
                then f j + 1 else fout j)%Z (nt_step nt_gr) 0) emp.

Definition map_ker (i : nat) (arr out : Z) (fout : nat -> Z):=
  I ::= (TID +C BID *C Z.of_nat ntrd);;
  WhileI  (inv i arr out fout) (I < Z.of_nat len) (
    X ::= [Gl ARR +o I] ;;
    [Gl OUT +o I] ::= X + 1%Z ;;
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

Lemma id_lt_nt_gr i j n m : i < n -> j < m -> i + j * n < m * n.
Proof.
  intros.
  assert (i + j * n < n + j * n) by omega.
  assert (n + j * n <= m * n) by nia.
  omega.
Qed.

Lemma nf_lt : forall n (i : Fin.t n), nf i < n.
Proof.
  introv; destruct Fin.to_nat; simpl; omega.
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

Lemma mod_same: forall x y z, z <> 0 -> (x + y) mod z = y -> x mod z = 0.
Proof.
  intros.
  lets: (>>Nat.div_mod (x + y) z ___); auto.
  assert (x = z * ((x + y) / z)) by omega.
  rewrite H2, mult_comm, Nat.mod_mul; eauto.
Qed.

Lemma map_correct : forall (tid : Fin.t ntrd) (bid : Fin.t nblk) (arr out : Z) (fout : nat -> Z), 
  CSL (fun n => default ntrd) tid
  (!(ARR === arr) ** 
   !(OUT === out) ** 
   is_array_p (Gl arr) len f 0 (perm_n nt_gr) ** 
   List.nth (nf tid + nf bid * ntrd) (distribute nt_gr (Gl out) len fout (nt_step nt_gr) 0) emp **
   !(BID === zf bid) ** !(TID === zf tid))
  (map_ker (nf tid + nf bid * ntrd) arr out fout)
  ( is_array_p (Gl arr) len f 0 (perm_n nt_gr) ** 
    List.nth (nf tid + nf bid * ntrd) (distribute nt_gr (Gl out) len (fun v=>f v+1)%Z (nt_step nt_gr) 0) emp).
Proof.
  (* assert (Htid : nat_of_fin tid < ntrd) by (destruct (Fin.to_nat _); simpl in *; auto). *)
  unfold map_ker; introv.
  eapply rule_seq.
  { hoare_forward; intros ? ? H'.
    destruct H' as [v H'].
    subA_normalize_in H'. simpl in H'. exact H'. }
  hoare_forward.
  assert (mod_add : forall x y c, y <> 0 -> c < y -> (x * y + c) mod y = c).
  { intros; rewrite plus_comm; rewrite Nat.mod_add, Nat.mod_small; eauto. }
  { unfold inv; eapply Hbackward.
    Focus 2.
    { intros s h H; apply ex_lift_l_in in H as [x H]; sep_split_in H.
      change_in H.
      { unfold_pures.
        lets Heq: (>> skip_arr_forward (x * nt_gr + (nf tid + nf bid * ntrd))).
        sep_rewrite_in Heq H; simpl in *; [|try first [nia; omega | eauto]..].
        sep_rewrite_in (@is_array_unfold (Gl arr) (x * nt_gr + (nf tid + nf bid * ntrd))) H.
        2: nia.
        sep_normal_in H.
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
          { unfold_pures; unfold_conn; simpl; f_equal; omega. }
          sep_rewrite_in (mps_eq1) H; [|exact H0]. 
          assert ((Gl out +o (Zn x * (Zn nblk * Zn ntrd) + (zf tid + zf bid * Zn ntrd))%Z ===l
                  Gl out +o I)%exp s (emp_ph loc)).
          { unfold_pures; unfold_conn; simpl; f_equal; omega. }
          sep_lift_in H 4.
          sep_rewrite_in (mps_eq1) H; [|exact H1]. 
          sep_combine_in H; exact H. }
        exact H. } Unfocus.
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
    sep_normal_in H; sep_split_in H.
    unfold_pures; subst.
    exists (S x); autorewrite with sep.
    sep_split; try now (unfold_conn; simpl; auto).
    unfold_conn; simpl; rewrite HP6; ring.
    (* unfold_conn; simpl; omega. *)
    lets Heq: (>> skip_arr_forward (x * nt_gr + (nf tid + nf bid * ntrd))).
    sep_rewrite Heq; simpl in *; [|try first [omega | eauto]..].
    sep_rewrite (@is_array_unfold (Gl (s ARR)) (x * nt_gr + (nf tid + nf bid * ntrd))).
    2: omega.
    sep_normal; simpl.
    repeat autorewrite with sep. simpl; repeat sep_cancel.
    assert (0 < nt_gr) by (apply Nat.mul_pos_pos; omega).
    destruct lt_dec; try omega; sep_lift 1; sep_cancel.
    sep_rewrite nth_dist_change; eauto.
    apply scC; sep_rewrite nth_dist_change; eauto.
    apply scC; eauto.
    clear H1 h3 H2 h2 h1 H0 h0 H Heq.
    - intros; repeat destruct lt_dec; eauto; try omega. 
      assert (nt_gr - 1 <= j); [|omega].
      cutrewrite (j + (x * nt_gr + (nf tid + nf bid * ntrd) + 1) =
                  ((j + 1) + (nf tid + nf bid * ntrd)) + x * nt_gr) in H0; [|ring].
      unfold nt_step in H0; rewrite Nat.mod_add in H0; eauto.
      apply mod_same in H0; eauto.
      apply Nat.mod_divides in H0 as [[| c] ?]; subst; nia.

      - intros; repeat destruct lt_dec; eauto; try omega. }

  { unfold inv; intros s h H. apply ex_lift_l_in in H as [x H]. sep_split_in H. unfold_pures.
    sep_cancel.
    sep_rewrite nth_dist_change; eauto.
    intros; destruct lt_dec; try omega; zify; omega. }

  {  intros s h H; unfold inv; exists 0; simpl.
     sep_split_in H; unfold_pures; sep_split; auto.
     - unfold_conn; simpl; autorewrite with sep; congruence.
     (* - unfold_conn. assert (nf tid + nf bid * ntrd < nt_gr) by auto. omega. *)
     - sep_cancel.
       sep_rewrite nth_dist_change; eauto.
       intros; destruct lt_dec; try omega.
       unfold nt_step in H2; rewrite Nat.mod_small in H2; try omega.
       assert (nf tid + nf bid * ntrd < nt_gr); eauto; omega. }
Qed.

Require Import Bdiv.
Local Notation init := MyVector.init.
Definition bth_pre (b : Fin.t nblk) (arr out : val) (fout : nat -> Z) :=
  !(ARR === arr) **
  !(OUT === out) **
  conj_xs (ls_init 0 ntrd (fun i =>
    is_array_p (Gl arr) len f 0 (perm_n nt_gr))) ** 
  conj_xs (ls_init 0 ntrd (fun i =>
    skip_arr (Gl out) 0 len nt_gr fout (i + nf b * ntrd))).

Definition tr_pres (b : Fin.t nblk) (arr out : val) fout := init (fun i : Fin.t ntrd =>
  !(ARR === arr) ** 
  !(OUT === out) **
  is_array_p (Gl arr) len f 0 (perm_n nt_gr) ** 
  skip_arr (Gl out) 0 len nt_gr fout (nf i + nf b * ntrd) **
  !(BID === zf b)).

Definition bth_post (b : Fin.t nblk) (arr out : val) := 
  conj_xs (ls_init 0 ntrd (fun i  =>
    is_array_p (Gl arr) len f 0 (perm_n nt_gr))) **
  conj_xs (ls_init 0 ntrd (fun i  =>
    skip_arr (Gl out) 0 len nt_gr (fun v => f v + 1)%Z (i + nf b * ntrd))).

Definition tr_posts (b : Fin.t nblk) (arr out : val) := (init (fun i : Fin.t ntrd =>
  is_array_p (Gl arr) len f 0 (perm_n nt_gr) ** 
  skip_arr (Gl out) 0 len nt_gr (fun v => f v + 1)%Z (nf i + nf b * ntrd))).

Definition E : env := fun v =>
  if var_eq_dec v BID then Lo
  else if var_eq_dec v ARR then Lo
  else if var_eq_dec v OUT then Lo
  else Hi.  

(* delete arguments of map_ker *)
Definition map' : cmd.
  pose (map_ker 0 0%Z 0%Z (fun _:nat => 0%Z)) as map'; unfold map_ker, WhileI in map'; exact map'.
Defined.

Definition bspec : (barrier_spec ntrd) := fun i => (default ntrd).

Lemma precise_false : precise (fun _ _ => False).
Proof.
  unfold precise; intros; tauto.
Qed.

Lemma map_correct_b (b : Fin.t nblk) (arr out : val) (fout : nat -> Z) : 
  CSLp ntrd E (bth_pre b arr out fout ** !(BID === zf b)) map' (bth_post b arr out).
Proof.
  applys (>> rule_par bspec (tr_pres b arr out fout) (tr_posts b arr out));
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
    repeat sep_cancel.
  - unfold tr_posts, bth_post; intros s h H.
    istar_simplify_in H.
    sep_cancel.
  - intros; unfold tr_pres; rewrite MyVector.init_spec.
    unfold CSL.low_assn.
    Hint Constructors typing_exp.
    repeat prove_low_assn; eauto.
    constructor; eauto.
    apply low_assn_skip_arr; eauto.
    constructor; eauto.
  - intros; unfold CSL.low_assn, tr_posts; rewrite MyVector.init_spec.
    repeat prove_low_assn.
    constructor; eauto.
    apply low_assn_skip_arr; constructor; eauto.
  - repeat (econstructor; try instantiate (1 := Hi));
    equates 1; repeat constructor; repeat instantiate (1 := Hi); eauto.
    instantiate (1 := Hi); eauto.
  - unfold tr_pres, tr_posts; intros; rewrite !MyVector.init_spec.
    unfold bspec, skip_arr.
    eapply Hbackward.
    eapply Hforward.
    apply map_correct.
    intros.
    apply H.
    intros; sep_normal_in H; sep_normal; sep_cancel.
    repeat sep_cancel; eauto.
    (* hmm.. *)
    Grab Existential Variables.
    apply Lo.
    apply Lo.
    apply Lo.
    apply Lo.
    apply Lo.
    apply 0.
Qed.

Definition bl_pres (arr out : val) fout : Vector.t assn nblk :=
  init (fun b : Fin.t nblk => (bth_pre b arr out fout)).
Definition bl_posts (arr out : val) : Vector.t assn nblk :=
  init (fun b : Fin.t nblk => (bth_post b arr out)).

Theorem map_correct_g (arr out : val) fout :
  CSLg ntrd nblk ntrd_neq0 nblk_neq0
    (!(ARR === arr) ** !(OUT === out) ** 
     is_array (Gl arr) len f 0 **
     is_array (Gl out) len fout 0)
    (Pr nil map')
    (is_array (Gl arr) len f 0 **
     is_array (Gl out) len (fun v => f v + 1)%Z 0).
Proof.
  applys (>> rule_grid E (bl_pres arr out fout) (bl_posts arr out)).
  - intros s h H.
    unfold bl_pres, bth_pre.
    sep_split_in H.
    istar_simplify.
    repeat sep_rewrite (@ls_star nblk).
    repeat sep_rewrite (@ls_pure nblk); sep_split.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    repeat (sep_rewrite_r is_array_skip_arr); eauto.
    Require Import Skel_lemma.
    sep_rewrite conj_xs_init_flatten.
    sep_rewrite_r is_array_is_array_p_1; eauto.
  - unfold bl_pres, bl_posts; intros.
    rewrite !MyVector.init_spec.
    eapply CSLp_backward.
    eapply CSLp_forward.
    apply (map_correct_b bid arr).
    intros; simpl; sep_normal; eauto.
    intros; simpl in *; sep_normal_in H; eauto.
  - unfold bl_posts, bth_post.
    intros s h H.
    istar_simplify_in H.
    Require Import Skel_lemma.
    sep_rewrite_in conj_xs_init_flatten H.
    sep_rewrite_in_r is_array_is_array_p_1 H; eauto.
    sep_rewrite_in_r scan_lib.is_array_skip_arr H; eauto.
  - prove_inde.
  - intros; unfold bl_pres, bth_pre.
    rewrite MyVector.init_spec.
    prove_inde;
    apply inde_conj_xs; rewrite init_length; intros;
    rewrite ls_init_spec; destruct lt_dec; prove_inde;
    apply inde_distribute; prove_indeE.
  - intros bid; unfold bl_pres, bth_pre; rewrite MyVector.init_spec.
    Hint Constructors typing_exp typing_lexp.
    repeat prove_low_assn; eauto;
    apply low_assn_conj_xs; rewrite init_length; intros;
    rewrite ls_init_spec; destruct lt_dec; try prove_low_assn.
    constructor; eauto.
    apply low_assn_skip_arr; eauto;
    prove_low_assn.
  - intros.
    unfold bl_posts, bth_post.
    rewrite MyVector.init_spec.
    has_no_vars_assn;
    apply has_no_vars_conj_xs;
    rewrite init_length; intros; rewrite ls_init_spec;
    repeat has_no_vars_assn.
    apply has_no_vars_is_array_p; cbv; auto.
    apply has_no_vars_skip_arr; simpl; eauto.
  - simpl; tauto.
  - unfold E; eauto.
  - unfold E; eauto.
  - eauto.
  - eauto.
  - simpl; eauto.
Qed.
    
End Map.