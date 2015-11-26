Require Import GPUCSL.
Require Import scan_lib.
Require Import LibTactics.

Section read_only_lemma.
Fixpoint is_array_p e len f s p :=
  match len with
    | O => emp
    | S len' => (e +o Zn s -->p (p, f s)) ** is_array_p e len' f (S s) p
  end.
Require Import QArith.
Definition injZ (n : Z) : Qc := Q2Qc (inject_Z n).
Require Import Qcanon.
Lemma pts_star_p e1 e2 (p1 p2 : Qc) stk :
  0 < p1 -> p1 <= 1 -> 0 < p2 -> p2 <= 1 -> p1 + p2 <= 1 ->
  stk ||= e1 -->p (p1 + p2, e2) <=>
      (e1 -->p (p1, e2)) ** (e1 -->p (p2, e2)).
Proof.
  unfold_conn; intros Hp1 Hp1' Hp2 Hp2' H12 ph; split; intros Hsat.
  - set (ph' := fun (p' : Qc) l => match PHeap.this ph l with
                               Some (p, x) => Some (p', x)
                             | None => None end).
    assert (forall (p : Qc) , 0 < p -> p <= 1 -> is_pheap (ph' p)).
    { intros p H0 H1 l; unfold ph'.
      rewrite Hsat; destruct (eq_dec _ _); eauto. }
    exists (Pheap (H _ Hp1 Hp1')) (Pheap (H _ Hp2 Hp2')); simpl.
    unfold ph'; simpl; repeat split; intros; repeat (rewrite Hsat; destruct (eq_dec _ _); eauto).
    + unfold pdisj; intros; rewrite Hsat; destruct (eq_dec _ _); eauto.
      repeat split; eauto.
      apply plus_gt_0; eauto.
    + destruct ph as [ph ?]; simpl in *; extensionality l; unfold phplus.
      rewrite Hsat; destruct (eq_dec _ _); eauto.
  - destruct Hsat as (ph1 & ph2 & Hph1 & Hph2 & Hdis & Heq).
    intros; rewrite <-Heq; unfold phplus; rewrite Hph1, Hph2.
    destruct (eq_dec _ _); eauto.
Qed.

Lemma is_array_p_star e n f p1 p2 stk : 
  0 < p1 -> p1 <= 1 -> 0 < p2 -> p2 <= 1 -> p1 + p2 <= 1 ->
  forall s,
  stk ||= is_array_p e n f s (p1 + p2) <=>
      is_array_p e n f s p1 ** is_array_p e n f s p2.
Proof.
  induction n; simpl; intros.
  - rewrite emp_unit_l; reflexivity.
  - rewrite IHn; eauto; rewrite pts_star_p; eauto.
    rewrite <-!sep_assoc; split; intros; repeat sep_cancel.
Qed.

Lemma this_inv q H : this {| this := q; canon := H |} = q. auto. Qed.

Require Import Psatz.

Lemma inject_Z_1 : inject_Z 1 = 1%Q. auto. Qed.

Ltac injZ_simplify :=
  unfold injZ in *;
  repeat rewrite Nat2Z.inj_succ in *;
  repeat rewrite <-Z.add_1_r in *;
  repeat rewrite inject_Z_plus in *;
  repeat rewrite inject_Z_1 in *.

Lemma inject_Z_n_ge0 n  : (0 <= inject_Z (Zn n))%Q.
Proof.
  assert (0 <= Zn n)%Z.
  { cutrewrite (0 = Zn 0)%Z; [|auto].
    apply inj_le; omega. }
  cutrewrite (0 = inject_Z 0)%Q; [|auto].
  rewrite <-Zle_Qle; auto.
Qed.

Lemma inject_Z_Sn_gt0 n : (1 <= inject_Z (Zn (S n)))%Q.
Proof.
  injZ_simplify.
  lets: (inject_Z_n_ge0 n).
  psatz Q 2.
Qed.

Ltac Qc_to_Q :=
  match goal with
  | [q : Qc |- _] => destruct q; Qc_to_Q
  | [|- _] =>
    try applys Qc_is_canon;
    repeat ( unfold Q2Qc, Qcmult, Qcplus, Qcdiv, Qcinv, Qclt, Qcle in *);
    repeat (try rewrite this_inv in *; try rewrite Qred_correct in *)
  end.

Lemma is_array_is_array_p_n e n f s p stk (nt : nat) :
  0 < p -> p <= 1 -> (injZ (Zn nt) * p <= 1) -> (nt <> 0)%nat -> 
  forall st,
  stk ||=
    is_array_p e n f s (injZ (Zn nt) * p) <=>
    conj_xs (ls_init st nt (fun i => is_array_p e n f s p)).
Proof.
  intros Hp0 Hp1 Hnp Hn0; induction nt as [|[|nt]]; intros; try omega.
  - simpl.
    asserts_rewrite (injZ 1 * p = p).
    { apply Qc_is_canon.
      repeat unfold injZ, "!!", "*".
      rewrite !this_inv, !Qred_correct.
      cutrewrite (inject_Z 1 = 1%Q); [|eauto].
      rewrite Qmult_1_l; reflexivity. }
    rewrite emp_unit_r; reflexivity.
  - remember (S nt) as nt'.
    asserts_rewrite (Zn (S nt') = Zn nt' + 1)%Z.
     { rewrite Nat2Z.inj_succ; omega. }
     unfold injZ; rewrite inject_Z_plus; simpl.
     asserts_rewrite (!! (inject_Z (Zn nt') + inject_Z 1) = injZ (Zn nt') + 1).
     { apply Qc_is_canon.
       unfold injZ, "+", "!!".
       rewrite !this_inv.
       rewrite !Qred_correct.
       reflexivity. }
  rewrite Qcmult_plus_distr_l, Qcmult_1_l.

  rewrite is_array_p_star;
    try (subst nt'; injZ_simplify; Qc_to_Q; lets: (inject_Z_n_ge0 nt); lets: (inject_Z_Sn_gt0 nt); psatz Q 3).    
  lets Heq: (>> IHnt (S st)); try omega;
    try (subst nt'; injZ_simplify; Qc_to_Q; lets: (inject_Z_n_ge0 nt); lets: (inject_Z_Sn_gt0 nt); psatz Q 3).
  rewrite Heq; split; intros; repeat sep_cancel.
Qed.

Lemma is_array_p1 e n f stk :
  forall s,
  stk ||= is_array e n f s <=>
      is_array_p e n f s 1.
Proof.
  induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn; reflexivity.
Qed.

Lemma one_div_n n : (n <> 0)%nat -> 1 = injZ (Zn n) * (1 / (injZ (Zn n))).
Proof.
  intros; rewrite Qcmult_div_r; eauto.
  intros Hc.
  cutrewrite (0 = injZ (Zn 0%nat)) in Hc;[| auto].
  unfold injZ in Hc.
  unfold Q2Qc in *; apply (f_equal (fun x => this x)) in Hc.
  rewrite !this_inv in Hc.
  assert (Qred (inject_Z (Zn n)) == Qred (inject_Z (Zn 0))) by (rewrite Hc; reflexivity).
  rewrite !Qred_correct in H0.
  rewrite inject_Z_injective in H0.
  rewrite Nat2Z.inj_iff in H0.
  auto.
Qed.

Lemma is_array_is_array_p_1 e n f s stk (nt : nat) :
  (nt <> 0)%nat ->
  forall st,
  stk ||=
    is_array e n f s <=>
    conj_xs (ls_init st nt (fun i => is_array_p e n f s (1 / (injZ (Zn nt))))).
Proof.    
  intros Hnt st.
  rewrite is_array_p1.
  rewrite (one_div_n nt) at 1; eauto.
  apply is_array_is_array_p_n; eauto;
  unfold injZ; Qc_to_Q; destruct nt; try omega; lets: (inject_Z_Sn_gt0 nt).
  apply Qlt_shift_div_l; lra.
  apply Qle_shift_div_r; try lra.
  lets Heq: Qmult_div_r; unfold Qdiv in Heq; rewrite Heq; lra.
Qed.
End read_only_lemma.

Close Scope Qc_scope.
Close Scope Q_scope.
Section Map.
Local Notation TID := (Var 0).
Local Notation BID := (Var 1).
Local Notation ARR := (Var 2).
Local Notation OUT := (Var 3).
Local Notation X := (Var 4).
Local Notation Y := (Var 5).
Local Notation I := (Var 6).

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

Fixpoint fv (e : exp) :=
  match e with
    | Evar v => v :: nil
    | Enum n => nil
    | e1 +C e2 
    | e1 *C e2
    | e1 -C e2 => fv e1 ++ fv e2
    | e1>>1 => fv e1
  end%exp.

Lemma fv_subE var v e :
  ~List.In var (fv e) -> subE var (Enum v) e = e.
Proof.
  simpl in *; intros; induction e; simpl in *; jauto;
  try rewrite IHe1; try rewrite IHe2; try rewrite IHe; try rewrite in_app_iff in *; eauto.
  destruct var_eq_dec; jauto.
  contradict H; eauto.
Qed.

Variable func : var -> exp.
Variable f_den : Z -> Z.
Hypothesis func_fv :
  forall v u, List.In u (fv (func v)) -> u = v.
Hypothesis func_denote :
  forall v s, edenot (func v) s = f_den (s v).

Section block_verification.
Variable bid : Fin.t nblk.

Notation zf i := (Z_of_fin i).

Section thread_verification.
Variable tid : Fin.t ntrd.

Notation gtid := (nf tid + nf bid * ntrd).

Definition inv :=
  Ex ix, 
    !(ARR === arr) **
    !(OUT === out) **
    !(I === Enum' (ix * nt_gr + gtid)) **
    !(Apure (ix * nt_gr + gtid < len + nt_gr)%nat) **
    nth gtid (distribute nt_gr (Gl arr) (ix * nt_gr) f_ini (nt_step nt_gr) 0) emp **
    nth gtid (distribute nt_gr (Gl arr) (len - (ix * nt_gr)) f_ini (nt_step nt_gr) (ix * nt_gr)) emp **
    nth gtid (distribute nt_gr (Gl out) (ix * nt_gr) (fun i => (f_den (f_ini i)))%Z (nt_step nt_gr) 0) emp **
    nth gtid (distribute nt_gr (Gl out) (len - (ix * nt_gr)) (fun i => fout i) (nt_step nt_gr) (ix * nt_gr)) emp.

Notation GTID := (TID +C BID *C Zn ntrd).

Definition map_ker :=
  I ::= (TID +C BID *C Z.of_nat ntrd);;
  WhileI inv (I < Z.of_nat len) (
    X ::= [Gl ARR +o I] ;;
    [Gl OUT +o I] ::= func X;;
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
   List.nth (nf tid + nf bid * ntrd) (distribute nt_gr (Gl arr) len f_ini (nt_step nt_gr) 0) emp **
   List.nth (nf tid + nf bid * ntrd) (distribute nt_gr (Gl out) len fout (nt_step nt_gr) 0) emp **
   !(BID === zf bid) ** !(TID === zf tid))
  map_ker
  ( List.nth (nf tid + nf bid * ntrd) (distribute nt_gr (Gl arr) len f_ini (nt_step nt_gr) 0) emp **
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
        sep_rewrite_in (@skip_arr_unfold' (nf tid + nf bid * ntrd) (Gl out)) H; [|try first [omega | eauto]..].
        2: nia.
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
          sep_lift_in H 3.
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
      subA_normalize_in H. simpl in H.
      assert ((subE I v (func X) === func X) s (emp_ph loc)).
      { unfold_conn.
        rewrite fv_subE; eauto.
        intros Hc; apply func_fv in Hc; congruence. }
      sep_rewrite_in mps_eq2 H; [|exact H0].
      ex_intro v H. exact H. }
    
    unfold inv; intros s h H. destruct H as (v & H); simpl in H.
    sep_normal_in H; sep_split_in H.
    unfold_pures; subst.
    exists (S x); autorewrite with sep.
    sep_split; try now (unfold_conn; simpl; auto; nia).
    sep_rewrite_r skip_arr_fold'; try omega; eauto.
    sep_rewrite_r (@skip_arr_fold' (nf tid + nf bid * ntrd) (Gl (s OUT))); try omega; eauto.
    sep_normal; simpl.
    simpl; repeat sep_cancel.
    cuts_rewrite (len - (nt_gr + x * nt_gr) = len - x * nt_gr - nt_gr); [|nia]. 
    repeat autorewrite with sep. repeat sep_cancel.
    assert ((func X === f_den (f_ini (x * nt_gr + gtid))) s (emp_ph loc)).
    { unfold_conn; simpl.
      rewrite func_denote, HP; eauto. }
    sep_rewrite_in mps_eq2 H2; [|exact H3].
    sep_cancel. }
  { unfold inv; intros s h H. apply ex_lift_l_in in H as [x H]. sep_split_in H. unfold_pures.
    rewrite HP2 in n; rewrite <-Nat2Z.inj_lt in n.
    assert (len - x * nt_gr <= nf tid + nf bid * ntrd) by (zify; omega).
    assert (nf tid + nf bid * ntrd < nt_gr) by auto.
    apply scC in H; sep_rewrite_in nth_dist_nil H; try omega; eauto.
    2: instantiate (1 :=len - x * nt_gr); intros j Hj; unfold nt_step.
    2: rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try (zify; omega).
    sep_normal_in H.
    sep_lift_in H 2; sep_rewrite_in nth_dist_nil H; try omega; eauto.
    2: instantiate (1 :=len - x * nt_gr); intros j Hj; unfold nt_step.
    2: rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try (zify; omega).
    rewrite minus_diag in H; simpl in H.
    rewrite nth_nseq in H.
    (* assert ((Gl arr ===l Gl ARR) s (emp_ph loc)) by (unfold_conn; simpl; congruence). *)
    (* sep_rewrite distribute_eq; eauto. *)
    assert (x * nt_gr <= len \/ len < x * nt_gr) as [|] by omega.
    - apply scC in H; sep_rewrite_in nth_dist_ext H; try omega; auto.
      2: instantiate (1 :=len - x * nt_gr); intros j Hj; simpl; unfold nt_step;
         rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try omega.
      sep_normal_in H.
      sep_lift_in H 2; sep_rewrite_in nth_dist_ext H; try omega; auto.
      2: instantiate (1 :=len - x * nt_gr); intros j Hj; simpl; unfold nt_step;
         rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try omega.
      cutrewrite (x * nt_gr + (len - x * nt_gr) = len) in H; [|omega].
      destruct Compare_dec.leb; sep_normal_in H; sep_split; try now (unfold_conn; simpl; auto); sep_cancel.
    - (* apply scC in H; sep_rewrite nth_dist_ext; try omega; auto. *)
      (* cutrewrite (len - x * ntrd = 0) in H; [|omega]. *)
      cutrewrite (x * nt_gr = len + (x * nt_gr - len)) in H; [|omega].
      assert (forall j, j < x * nt_gr - len -> nt_step nt_gr (0 + len + j) <> nf tid + nf bid * ntrd).
      { unfold nt_step; simpl; intros j Hj Hc.
        assert (len + j + nt_gr < (S x) * nt_gr) by (simpl; omega).
        assert (x * nt_gr + j + (nf tid + nf bid * ntrd) < len + j + nt_gr) by omega.
        let t := (eval simpl in (Nat.mod_add (len + j) 1 nt_gr)) in pose proof t.
        rewrite mult_1_l in H5.
        rewrite (Nat.div_mod (len + j + nt_gr) nt_gr), H5 in H3, H4; auto.
        assert (x * nt_gr  < nt_gr * ((len + j + nt_gr) / nt_gr)) by omega.
        assert (nt_gr * ((len + j + nt_gr) / nt_gr) < S x * nt_gr) by omega.
        rewrite mult_comm in H6; apply Nat.mul_lt_mono_pos_l in H6; try omega.
        rewrite mult_comm in H7; apply Nat.mul_lt_mono_pos_r in H7; omega. } 
      sep_rewrite_in_r nth_dist_ext H; try omega; eauto.
      sep_rewrite_in_r nth_dist_ext H; try omega; eauto.
      sep_split; auto.
      destruct Compare_dec.leb; sep_normal_in H; repeat sep_cancel. }

  {  intros s h H; unfold inv; exists 0; simpl.
     sep_split_in H; unfold_pures; sep_split; auto.
     - unfold_conn; simpl; autorewrite with sep; congruence.
     - unfold_conn. assert (nf tid + nf bid * ntrd < nt_gr) by auto. omega.
     - (* assert ((Gl ARR ===l Gl arr) s (emp_ph loc)) by (unfold_conn; simpl; congruence). *)
       (* sep_rewrite distribute_eq; eauto. *)
       rewrite <-minus_n_O, nth_nseq; destruct Compare_dec.leb; sep_normal; sep_cancel. }
Qed.
End thread_verification.

Require Import Bdiv.
Local Notation init := MyVector.init.
Definition bth_pre :=
  !(ARR === arr) **
  !(OUT === out) **
  conj_xs (ls_init 0 ntrd (fun i =>
    skip_arr (Gl arr) 0 len nt_gr f_ini (i + nf bid * ntrd))) **
  conj_xs (ls_init 0 ntrd (fun i =>
    skip_arr (Gl out) 0 len nt_gr fout (i + nf bid * ntrd))).

Definition tr_pres := init (fun i : Fin.t ntrd =>
  !(ARR === arr) ** 
  !(OUT === out) ** 
  skip_arr (Gl arr) 0 len nt_gr f_ini (nf i + nf bid * ntrd) **
  skip_arr (Gl out) 0 len nt_gr fout (nf i + nf bid * ntrd) **
  !(BID === zf bid)).

Definition bth_post  := 
  conj_xs (ls_init 0 ntrd (fun i  =>
    skip_arr (Gl arr) 0 len nt_gr f_ini (i + nf bid * ntrd))) **
  conj_xs (ls_init 0 ntrd (fun i  =>
    skip_arr (Gl out) 0 len nt_gr (fun v => f_den (f_ini v))%Z (i + nf bid * ntrd))).

Definition tr_posts := (init (fun i : Fin.t ntrd =>
  skip_arr (Gl arr) 0 len nt_gr f_ini (nf i + nf bid * ntrd) **
  skip_arr (Gl out) 0 len nt_gr (fun v => f_den (f_ini v))%Z (nf i + nf bid * ntrd))).

Definition E : env := fun v =>
  if var_eq_dec v BID then Lo
  else if var_eq_dec v ARR then Lo
  else if var_eq_dec v OUT then Lo
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
    repeat sep_cancel.
  - unfold tr_posts, bth_post; intros s h H.
    istar_simplify_in H.
    sep_cancel.
  - intros; unfold tr_pres; rewrite MyVector.init_spec.
    unfold CSL.low_assn.
    Hint Constructors typing_exp.
    repeat prove_low_assn; eauto;
    apply low_assn_skip_arr;
    constructor; eauto.
  - intros; unfold CSL.low_assn, tr_posts; rewrite MyVector.init_spec.
    prove_low_assn; apply low_assn_skip_arr; constructor; eauto.
  - repeat econstructor.
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
    apply Lo.
    apply 0.
    apply Lo.
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
    (!(ARR === arr) ** !(OUT === out) ** 
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
    repeat (sep_rewrite_r is_array_skip_arr); eauto.
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
    repeat sep_rewrite is_array_skip_arr; eauto.
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
    rewrite ls_init_spec; destruct lt_dec; try prove_low_assn;
    apply low_assn_skip_arr; eauto;
    prove_low_assn.
  - intros.
    unfold bl_posts, bth_post.
    rewrite MyVector.init_spec.
    has_no_vars_assn;
    apply has_no_vars_conj_xs;
    rewrite init_length; intros; rewrite ls_init_spec;
    repeat has_no_vars_assn;
    apply has_no_vars_skip_arr; simpl; eauto.
  - simpl; tauto.
  - unfold E; eauto.
  - unfold E; eauto.
  - eauto.
  - eauto.
  - simpl; eauto.
Qed.
    
End Map.