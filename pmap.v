Require Import GPUCSL.
Require Import scan_lib.

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

Local Notation nt_gr := (nblk * ntrd).

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
        { assert ((Gl ARR +o (Zn x * (Zn nblk * Zn ntrd) + (zf tid + zf bid * Zn ntrd))%Z ===l
                  Gl ARR +o I)%exp s (emp_ph loc)).
          { unfold_pures; unfold_conn; simpl; f_equal; nia. }
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

Require Import Bdiv.
Local Notation init := MyVector.init.
Definition bth_pre (b : Fin.t nblk) (arr : val) :=
  !(ARR === arr) **
  conj_xs (ls_init 0 ntrd (fun i =>
    skip_arr (Gl arr) 0 len nt_gr f (i + nf b * ntrd))).

Definition tr_pres (b : Fin.t nblk) (arr : val) := init (fun i : Fin.t ntrd =>
  !(ARR === arr) ** 
  skip_arr (Gl arr) 0 len nt_gr f (nf i + nf b * ntrd) **
  !(BID === zf b)).

Definition bth_post (b : Fin.t nblk) (arr : val) := 
  conj_xs (ls_init 0 ntrd (fun i  =>
    skip_arr (Gl arr) 0 len nt_gr (fun v => f v + 1)%Z (i + nf b * ntrd))).

Definition tr_posts (b : Fin.t nblk) (arr : val) := (init (fun i : Fin.t ntrd =>
  skip_arr (Gl arr) 0 len nt_gr (fun v => f v + 1)%Z (nf i + nf b * ntrd))).

Definition E : env := fun v =>
  if var_eq_dec v BID then Lo
  else if var_eq_dec v ARR then Lo
  else Hi.  

(* delete arguments of map_ker *)
Definition map' : cmd.
  pose (map_ker 0 0%Z) as map'; unfold map_ker, WhileI in map'; exact map'.
Defined.

Definition bspec : (barrier_spec ntrd) := fun i => (default ntrd).

Lemma precise_false : precise (fun _ _ => False).
Proof.
  unfold precise; intros; tauto.
Qed.

Lemma map_correct_b (b : Fin.t nblk) (arr : val) : 
  CSLp ntrd E (bth_pre b arr ** !(BID === zf b)) map' (bth_post b arr).
Proof.
  applys (>> rule_par bspec (tr_pres b arr) (tr_posts b arr)); try first [omega | nia | eauto].
  - destruct ntrd; eexists; try omega; eauto.
  - unfold bspec; split; intros; unfold default; simpl; rewrite MyVector.init_spec;
    unfold CSL.low_assn, low_assn, indeP; tauto.
  - split; unfold bspec, default; simpl; rewrite MyVector.init_spec;
    apply precise_false.
  - unfold bth_pre, tr_pres; intros.
    sep_split_in H.
    (* simplify the conclusion *)
    apply sc_v2l.
    rewrite (vec_to_list_init0 _ emp).
    erewrite ls_init_eq0.
    Focus 2.
    { intros i Hi.
      destruct (Fin.of_nat i ntrd) as [|Hex] eqn:Heq; [|destruct Hex; omega].
      rewrite (Fin_nat_inv Heq). reflexivity. } Unfocus.
    repeat sep_rewrite (@ls_star ntrd).
    repeat sep_rewrite (@ls_pure ntrd); sep_split.
    (* crush conditions for variables *)
    apply ls_emp'; rewrite init_length; intros; rewrite ls_init_spec.
    unfold TrueP; destruct lt_dec; eauto.
    apply ls_emp'; rewrite init_length; intros; rewrite ls_init_spec.
    unfold TrueP; destruct lt_dec; eauto.
    
    (* simplify the hypothesis *)
    apply H.
    (* rewrite (vec_to_list_init0 _ emp) in H. *)
    (* erewrite ls_init_eq0 in H. *)
    (* Focus 2. *)
    (* { intros i Hi. *)
    (*   destruct (Fin.of_nat i ntrd) as [|Hex] eqn:Heq; [|destruct Hex; omega]. *)
    (*   rewrite (Fin_nat_inv Heq). reflexivity. } Unfocus. *)
    (* eauto. *)
  - unfold tr_posts, bth_post; intros s h H.
    apply sc_v2l in H.
    rewrite (vec_to_list_init0 _ emp) in H.
    erewrite ls_init_eq0 in H.
    Focus 2.
    { intros i Hi.
      destruct (Fin.of_nat i ntrd) as [|Hex] eqn:Heq; [|destruct Hex; omega].
      rewrite (Fin_nat_inv Heq). reflexivity. } Unfocus.
    apply H.
  - intros; unfold tr_pres; rewrite MyVector.init_spec.
    unfold CSL.low_assn.
    Hint Constructors typing_exp.
    repeat prove_low_assn; eauto.
    apply low_assn_skip_arr.
    constructor; eauto.
  - intros; unfold CSL.low_assn, tr_posts; rewrite MyVector.init_spec.
    apply low_assn_skip_arr.
    constructor; eauto.
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

Definition bl_pres (arr : val) : Vector.t assn nblk :=
  init (fun b : Fin.t nblk => (bth_pre b arr)).
Definition bl_posts (arr : val) : Vector.t assn nblk :=
  init (fun b : Fin.t nblk => (bth_post b arr)).

Lemma CSLp_backward (P' P : assn) n E C Q : 
  CSLp n E P C Q -> (P' |= P) -> CSLp n E P' C Q.
Proof.
  unfold CSLp; intros Hcsl Hp; intros.
  exploit Hcsl.
  eauto.
  eauto.
  unfold sat_k in *.
  instantiate (1:=h).
  instantiate (1:=leqks).
  destruct low_eq_repr.
  apply Hp; eauto.
  intros; eauto.
Qed.  

Lemma safe_gl_forward n m E ks h (Q Q' : assn) : 
  @safe_nk n E m ks h Q -> 
  (Q |= Q') ->
  @safe_nk n E m ks h Q'.
Proof.
  revert h ks; induction m; simpl; intros h ks Hsafe Hq; eauto.
  simpl in Hsafe; destructs Hsafe.
  repeat split; eauto.
  - intros; unfold sat_k in *.
    exploit H; eauto.
    intros [x ?]; exists x.
    destruct low_eq_repr; apply Hq; eauto.
  - exploit H2; eauto.
    intros; jauto.
  - exploit H2; eauto.
    intros; jauto.
  - intros; exploit H3; eauto.
    intros (h'' & ? & ? & ?); exists h''; repeat split; eauto.
Qed.  

Lemma CSLp_forward P n E C (Q Q' : assn) : 
  CSLp n E P C Q -> (Q |= Q') -> CSLp n E P C Q'.
Proof.
  unfold CSLp; intros; applys safe_gl_forward; eauto.
Qed.

Theorem map_correct_g (arr : val) :
  CSLg ntrd nblk ntrd_neq0 nblk_neq0
    (!(ARR === arr) ** 
     is_array (Gl arr) len f 0)
    (Pr nil map')
    (is_array (Gl arr) len (fun v => f v + 1)%Z 0).
Proof.
  applys (>> rule_grid E (bl_pres arr) (bl_posts arr)).
  - intros s h H.
    unfold bl_pres, bth_pre.
    sep_split_in H; eauto.
    
    (* simplifying the conclusion *)
    apply sc_v2l.
    rewrite (vec_to_list_init0 _ emp).
    erewrite ls_init_eq0.
    Focus 2.
    { intros i Hi.
      destruct (Fin.of_nat i nblk) as [|Hex] eqn:Heq; [|destruct Hex; omega].
      rewrite (Fin_nat_inv Heq).
      reflexivity. } Unfocus.
    repeat sep_rewrite (@ls_star nblk).
    repeat sep_rewrite (@ls_pure nblk); sep_split.
    { apply ls_emp'; rewrite init_length; intros; rewrite ls_init_spec.
      destruct lt_dec; eauto.
      tauto. }
    (* applys (>> equiv_from_nth emp). *)
    (* Focus 2. *)
    (* { intros i Hi stk. *)
    (*   instantiate (1 := (ls_init 0 nblk *)
    (*     (fun i0 : nat => *)
    (*        conj_xs *)
    (*          (ls_init 0 ntrd *)
    (*             (fun i1 => *)
    (*                skip_arr (Gl arr) 0 len nt_gr f (i1 + i0 * ntrd)))))). *)
    (*   rewrite !ls_init_spec; destruct lt_dec. *)
    (*   rewrite sc_v2l. *)
    (*   rewrite (vec_to_list_init0 _ emp). *)
    (*   erewrite ls_init_eq0. *)
    (*   Focus 2. *)
    (*   { intros j Hj. *)
    (*     destruct (Fin.of_nat j ntrd) as [|Hex] eqn:Heq; [|destruct Hex; omega]. *)
    (*     simpl. *)
    (*     rewrite (Fin_nat_inv Heq). *)
    (*     reflexivity. } Unfocus. *)
    (*   reflexivity. *)
    (*   reflexivity. } Unfocus. *)
    (* rewrite !init_length; eauto. *)
    Lemma conj_xs_init_flatten l1 l2 f_ini :
      forall s stk,
        stk ||=
          conj_xs (ls_init s l1 (fun i =>
            conj_xs (ls_init 0 l2 (fun j => f_ini (j + i * l2))))) <=>
          conj_xs (ls_init (s * l2) (l1 * l2) (fun i => f_ini i)).
    Proof.
      induction l1; simpl; [reflexivity|].
      introv.
      Lemma ls_init_app {T : Type} l1 l2 (f_ini : nat -> T) :
        forall s, 
          ls_init s (l1 + l2) f_ini = ls_init s l1 f_ini ++ ls_init (s + l1) l2 f_ini.
      Proof.
        induction l1; simpl.
        - introv; rewrite <-plus_n_O; reflexivity.
        - introv; f_equal.
          rewrite IHl1; do 2 f_equal; ring.
      Qed.
      rewrite ls_init_app, conj_xs_app.
      apply star_proper.
      eapply equiv_from_nth; rewrite !init_length; eauto.
      - intros i Hi stk'; repeat rewrite (@ls_init_spec _ _ _ emp); destruct lt_dec.
        cutrewrite (0 + i + s * l2 = s * l2 + i); [|ring]; reflexivity.
        reflexivity.
      - rewrite IHl1.
        cutrewrite (S s * l2 = s * l2 + l2); [|ring]; reflexivity.
    Qed.
    Lemma conj_xs_init_flatten0 l1 l2 f_ini :
      forall stk,
        stk ||=
          conj_xs (ls_init 0 l1 (fun i =>
            conj_xs (ls_init 0 l2 (fun j => f_ini (j + i * l2))))) <=>
          conj_xs (ls_init 0 (l1 * l2) (fun i => f_ini i)).      
    Proof.
      cutrewrite (0 = 0 * l2); [|omega].
      introv; rewrite <-conj_xs_init_flatten.
      reflexivity.
    Qed.
    Lemma is_array_skip_arr E n m len' f_ini :
      n <> 0 -> m <> 0 ->
      forall stk, stk ||= 
        is_array E len' f_ini 0 <=>
        conj_xs (ls_init 0 n (fun i =>
          conj_xs (ls_init 0 m (fun j =>
            skip_arr E 0 len' (n * m) f_ini (j + i * m))))).
    Proof.
      intros.
      rewrite conj_xs_init_flatten0.
      lets Heq: (>>distribute_correct (n * m) (nt_step (n * m))); rewrite Heq; clear Heq.
      2: unfold nt_step; intros; apply Nat.mod_upper_bound; nia.
      eapply (@equiv_from_nth emp).
      rewrite init_length, distribute_length; ring.
      rewrite distribute_length; intros i Hi stk'.
      rewrite ls_init_spec; destruct lt_dec; try omega.
      reflexivity.
    Qed.
    apply is_array_skip_arr; eauto.
  - unfold bl_pres, bl_posts; intros.
    rewrite !MyVector.init_spec.
    eapply CSLp_backward.
    eapply CSLp_forward.
    apply (map_correct_b bid arr).
    intros; simpl; sep_normal; eauto.
    intros; simpl in *; sep_normal_in H; eauto.
  - unfold bl_posts, bth_post.
    intros s h H.
    apply sc_v2l in H.
    rewrite (vec_to_list_init0 _ emp) in H.
    erewrite ls_init_eq0 in H.
    Focus 2.
    { intros i Hi.
      destruct (Fin.of_nat i nblk) as [|Hex] eqn:Heq; [|destruct Hex; omega].
      rewrite (Fin_nat_inv Heq).
      reflexivity. } Unfocus.
    apply is_array_skip_arr in H; eauto.
  - prove_inde.
  - intros; unfold bl_pres, bth_pre.
    rewrite MyVector.init_spec.
    Lemma inde_conj_xs assns vs :
      (forall i, i < length assns -> inde (nth i assns emp) vs) ->
      inde (conj_xs assns) vs.
    Proof.
      induction assns; simpl; try omega.
      - intros; unfold_conn; unfold inde; eauto; simpl; tauto.
      - intros H.
        apply inde_sconj; eauto.
        + specialize (H 0); simpl in H; apply H; omega.
        + apply IHassns; intros i Hi; specialize (H (S i)); simpl in H; apply H; omega.
    Qed.
    prove_inde.
    apply inde_conj_xs; rewrite init_length; intros.
    rewrite ls_init_spec; destruct lt_dec; prove_inde.
    apply inde_distribute; prove_indeE.
  - intros bid; unfold bl_pres, bth_pre; rewrite MyVector.init_spec.
    Hint Constructors typing_exp typing_lexp.
    repeat prove_low_assn; eauto.
    Lemma low_assn_conj_xs assns E :
      (forall i, i < length assns -> low_assn E (nth i assns emp)) ->
      low_assn E (conj_xs assns) .
    Proof.
      induction assns; simpl; intros; repeat prove_low_assn.
      specialize (H 0); apply H; omega.
      apply IHassns; intros i; specialize (H (S i)); intros; apply H; omega.
    Qed.
    apply low_assn_conj_xs; rewrite init_length; intros.
    rewrite ls_init_spec; destruct lt_dec.
    apply low_assn_skip_arr; eauto.
    prove_low_assn.
  - intros.
    unfold bl_posts, bth_post.
    rewrite MyVector.init_spec.
    Lemma has_no_vars_conj_xs assns :
      (forall i, i < length assns -> has_no_vars (nth i assns emp)) ->
      has_no_vars (conj_xs assns).
    Proof.
      induction assns; simpl; intros; repeat has_no_vars_assn.
      apply (H 0); omega.
      apply IHassns; intros i; specialize (H (S i)); simpl in *.
      intros; apply H; omega.
    Qed.
    apply has_no_vars_conj_xs.
    rewrite init_length; intros; rewrite ls_init_spec.
    repeat has_no_vars_assn.
    apply has_no_vars_skip_arr; simpl; eauto.
  - simpl; tauto.
  - unfold E; eauto.
  - unfold E; eauto.
  - eauto.
  - eauto.
  - simpl; eauto.
Qed.
    
End Map
.