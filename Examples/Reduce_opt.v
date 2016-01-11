Require Import GPUCSL.
Require Import scan_lib.
Require Import LibTactics Psatz.

Section Reduce0.

Variable e_b : nat.
Variable ntrd : nat.
Variable l : nat.
Variable f_in : nat -> Z.

Hypothesis l_neq_0 : l <> 0.
Hypothesis ntrd_neq_0 : ntrd <> 0.
Hypothesis max_th_size : ntrd <= 2 ^ e_b.
Hypothesis l_leq_ntrd : l <= ntrd.
Hypothesis eb_neq_0 : e_b <> 0.
Section simfun.

Definition s n := 2 ^ (e_b - n).

Fixpoint f n i :=
  match n with
  | O => f_in i
  | S n => if Sumbool.sumbool_and _ _ _ _ (lt_dec (i + s (S n)) l) (lt_dec i (s (S n))) 
           then (f n i + f n (i + s (S n))%nat)%Z
           else f n i
  end.

Lemma sn_decr n : s (S n) <= s n.
Proof.
  apply Nat.pow_le_mono_r; omega.
Qed.

Lemma sum_of_split s n m f g:
  s <= m -> m < s + n ->
  sum_of s n (fun i => if lt_dec i m then f i else g i) =
  (sum_of s (m - s) f + sum_of m (n - (m - s)) g)%Z.
Proof.
  revert s m; induction n.
  - intros s m Hsm Hmn; assert (Heq : (m - s) = 0) by omega; rewrite Heq; simpl; eauto.
  - intros s m Hsm Hmn; remember (S n - (m - s)); simpl.
    assert (s = m \/ s < m) as [Hsm' | Hsm'] by omega; subst.
    + destruct lt_dec; try omega.
      rewrite minus_diag, <-minus_n_O; simpl.
      f_equal; erewrite sum_of_eq; eauto.
      intros i Hi; destruct lt_dec; omega.
    + destruct lt_dec; try omega.
      assert (exists ms, m - s = S ms) as [ms Hms] by (exists (m - s - 1); omega); rewrite Hms.
      simpl.
      rewrite IHn; try omega.
      rewrite Zplus_assoc; repeat f_equal; omega.
Qed.

Lemma sn_double n : S n <= e_b -> s (S n) + s (S n) = s n.
Proof.
  intros Hsneb. unfold s.
  assert (Heq : e_b - n = S (e_b - S n)) by omega; rewrite Heq; simpl; eauto. 
Qed.

Lemma f_inv n :
  S n <= e_b ->
  sum_of 0 (min l (s (S n))) (f (S n)) = sum_of 0 (min l (s n)) (f n).
Proof.
  intros Hsneb.
  simpl.
  lets Hsn : (>>sn_double n ___); try omega.
  assert (l <= s (S n) \/ s (S n) < l < s n \/ s n <= l) as [HsSnl | [HsSnl | HsSnl] ] by omega.  
  - erewrite (sum_of_eq (min l (s (S n)))).
    Focus 2.
    { simpl; intros i Hi.
      assert (i <= l) by nia.
      destruct Sumbool.sumbool_and; try omega.
      reflexivity. } Unfocus.
    rewrite !min_l; omega.
  - erewrite (sum_of_eq (min l (s (S n)))).
    Focus 2.
    { simpl; intros i Hi.
      instantiate (1 := fun i => if lt_dec i (min (l - s (S n)) (s (S n)))
                        then (f n i + f n (i + s (S n))%nat)%Z
                        else f n i); simpl.
      destruct Sumbool.sumbool_and, lt_dec; rewrite Nat.min_glb_lt_iff in *; omega.
    } Unfocus.
    rewrite sum_of_split; try omega.
    2: simpl; rewrite Nat.min_glb_lt_iff; repeat rewrite Nat.min_lt_iff; split; try omega.
    rewrite <-minus_n_O.
    rewrite (min_l _ (s n)); try omega.
    rewrite min_l; try omega.
    rewrite min_r; try omega.
    cutrewrite (s (S n) - (l - s (S n)) = s n - l); [|omega].
    rewrite <-shift_values; simpl.
    rewrite Z.add_shuffle0.
    assert (Heq : l = (l - s (S n)) + s (S n)) by omega; rewrite Heq at 5.
    rewrite <-Zplus_assoc; rewrite sum_of_concat; f_equal; clear Heq.
    assert (Heq : s (S n) = s n - l + (l - s (S n))) by omega; rewrite Heq.
    rewrite <-plus_n_O.
    rewrite sum_of_concat; f_equal.
    rewrite <-Heq; f_equal; omega.
  - repeat rewrite min_r; try omega.
    erewrite (sum_of_eq (s (S n))).
    Focus 2.
    { simpl; intros i Hi.
      destruct Sumbool.sumbool_and; try omega.
      reflexivity. } Unfocus.
    rewrite <-Hsn; rewrite sum_of_concat.
    rewrite <-shift_values; f_equal.
    f_equal; omega.
Qed.

Lemma fn_ok n :
  n <= e_b ->
  sum_of 0 (min l (s n)) (f n) = sum_of 0 l f_in.
Proof.
  induction n; simpl.
  - unfold s; rewrite <-minus_n_O, min_l; try omega.
    intros; apply sum_of_eq; intros; eauto.
  - intros; rewrite f_inv; eauto.
    apply IHn; omega.
Qed.    

Lemma feb_ok : f e_b 0 = sum_of 0 l f_in.
Proof.
  rewrite <-(fn_ok e_b); eauto.
  unfold s; rewrite minus_diag; simpl.
  rewrite min_r; try omega; simpl; omega.
Qed.

End simfun.

Local Notation x0 := (Var "x0").
Local Notation x1 := (Var "x1").
Local Notation x2 := (Var "x2").
Local Notation sdata := (Var "sdata").
Local Notation len := (Var "len").
Local Notation tid := (Var "tid").

Definition reduce_body n s :=
  (Cbarrier (n - 1) ;;
   Cif (Band (tid +C Zn s <C len) (tid <C Zn s)) (
     x0 ::= [ Sh sdata +o (tid + Zn s) ];;
     x2 ::= x1 +C x0 ;;
     x1 ::= x2 ;;
     [ Sh sdata +o tid] ::= x1
   ) Cskip
  )%exp.

Fixpoint reduce_aux t m :=
  match m with
  | O => Cskip
  | S m =>
    reduce_body t (s t) ;; reduce_aux (S t) m 
  end.

Definition reduce := reduce_aux 1 e_b.  

Notation perm_n n := (1 / injZ (Zn n))%Qc.

Definition Binv (fc : nat -> Z) n i :=
  (if Sumbool.sumbool_and _ _ _ _ (lt_dec (i + s (S n)) l) (lt_dec i (s (S n))) then
    Sh sdata +o (Zn i) -->p (1, fc i) **
    (Sh sdata +o (Zn i + Zn (s (S n)))%Z -->p (1, fc (i + (s (S n)))))
   else emp) **
  (if Nat.eq_dec i 0 then
    is_array (Sh sdata) (min (s (S n)) ntrd - min (l - s (S n)) (s (S n))) fc (min (l - s (S n)) (s (S n))) **
    is_array (Sh sdata) (ntrd - (min (l - s (S n)) (s (S n)) + s (S n))) fc
                        (min (l - s (S n)) (s (S n)) + s (S n))
   else emp).

Lemma sep_comm P Q stk :
  stk ||= P ** Q <=> Q ** P.
Proof.
  split; intros; repeat sep_cancel.
Qed.

Lemma is_array_change (e : loc_exp) (f1 f2 : nat -> Z) n :
  forall s, (forall x, x < n -> f1 (x + s) = f2(x + s)) ->
            forall stc,
              stc ||= is_array e n f1 s <=> is_array e n f2 s.
Proof.
  induction n; simpl; intros s Hf; try reflexivity.
  intros stc; rewrite IHn.
  cutrewrite (f1 s = f2 s); [reflexivity|].
  pose proof (Hf 0); rewrite plus_O_n in H; rewrite H; omega.
  intros x Hx; rewrite <-Nat.add_succ_comm; apply Hf; omega.
Qed.

Lemma is_array_concat e f f1 f2 len1 len2 : forall s stc,
    (forall off, off < len1 + len2 ->
     f (s + off) = if lt_dec off len1 then f1 (s + off) else f2 (s + off)) ->
    stc||=
       is_array e (len1 + len2) f s <=>
       is_array e len1 f1 s ** is_array e len2 f2 (s + len1).
Proof.
  induction len1; simpl; intros s stc H.
  - rewrite emp_unit_l, <-plus_n_O.
    rewrite is_array_change; [reflexivity|..].
    intros; rewrite plus_comm; eauto.
  - intros. rewrite <-Nat.add_succ_comm, <-sep_assoc, IHlen1.
    cutrewrite (f s = f1 s); [reflexivity|].
    cutrewrite (s = s + 0); [apply H; omega|omega].
    intros off ?; cutrewrite (S s + off = s + S off); [rewrite H; repeat destruct lt_dec|]; omega.
Qed.

Lemma Binv_ok fc n stk:
  stk ||= @Bdiv.Aistar_v ntrd (MyVector.init (fun i => Binv fc n (nf i))) <=>
          is_array (Sh sdata) ntrd fc 0.
Proof.
  unfold Binv.
  rewrite sc_v2l; rewrite (vec_to_list_init0 _ emp); erewrite ls_init_eq0.
  2: intros i Hi; destruct (Fin.of_nat i ntrd) as [|[? Hex]] eqn:Heq; try omega.
  2: apply Fin_nat_inv in Heq; rewrite Heq; reflexivity.
  rewrite ls_star.
  rewrite sep_comm.
  rewrite <-(firstn_skipn 1) at 1.
  rewrite firstn_init, skipn_init.
  rewrite min_l; try omega; simpl.
  rewrite <-!sep_assoc.
  erewrite ls_init_eq'.
  Focus 2. {
    intros i Hi; destruct Nat.eq_dec; try omega.
    cutrewrite (emp = id (fun _ => emp) (1 + i)); eauto. } Unfocus.
  unfold id.
  rewrite init_emp_emp; rewrite emp_unit_l.
  rewrite <-(firstn_skipn (min (l - s (S n)) (s (S n)))) at 1.
  rewrite firstn_init, skipn_init, conj_xs_app, <-plus_n_O.
  erewrite (ls_init_eq' _ _ (min (l - s (S n)) (s (S n)))).
  Focus 2. {
    intros i Hi; destruct Sumbool.sumbool_and.
    assert (l - s (S n) < s (S n) \/ s (S n) <= l - s (S n)) as [H | H]by omega.
    rewrite min_l in *; try omega.
    rewrite min_r in *; try omega.
    cutrewrite (emp = id (fun _ => emp) (min (l - s (S n)) (s (S n)) + i)); eauto. } Unfocus.
  unfold id.
  rewrite init_emp_emp; rewrite emp_unit_r.
  assert (l <= s (S n) \/ s (S n) < l) as [HsSnl | HsSnl ] by omega.
  - remember (min (s (S n)) ntrd) as msnt.
    rewrite !min_l; try  omega.
    cutrewrite (l - s (S n) = 0); [|omega]; simpl.
    rewrite <-!minus_n_O.
    assert (s (S n) <= ntrd \/ ntrd < s (S n)) as [H | H] by omega.
    + rewrite min_l in Heqmsnt; subst msnt; try omega.
      assert (Heq : ntrd = s (S n) + (ntrd - s (S n))) by omega; rewrite Heq at 2.
      rewrite is_array_concat; simpl; [rewrite emp_unit_r; reflexivity|intros; destruct lt_dec; eauto].
    + rewrite min_r in Heqmsnt; subst msnt; try omega.
      cutrewrite (ntrd - s (S n) = 0); [|omega].
      simpl; rewrite !emp_unit_r; reflexivity.
  - assert (l - s (S n)  <= s (S n) \/ s (S n) <= l - s (S n)) as [Hsnl | Hsnl] by omega.
    + rewrite !min_l; try omega.
      erewrite ls_init_eq0.
      Focus 2. { intros i Hi; destruct Sumbool.sumbool_and; try omega; reflexivity. } Unfocus.
      rewrite ls_star.
      Lemma is_array_distr e n (f' : nat -> Z) :
        forall s stk,
          stk ||= conj_xs (ls_init s n (fun i => e +o Zn i -->p (1, f' i))) <=>
              is_array e n f' s.
      Proof.
        induction n; intros s stk; simpl.
        - reflexivity.
        - rewrite IHn; reflexivity.
      Qed.
      Lemma is_array_distr_off e n off (f' : nat -> Z) :
        forall s stk,
          stk ||= conj_xs (ls_init s n (fun i => e +o (Zn i + Zn off)%Z -->p (1, f' (i + off)))) <=>
              is_array e n f' (s + off).
      Proof.
        induction n; intros s stk; simpl.
        - reflexivity.
        - rewrite IHn.
          rewrite Nat2Z.inj_add; reflexivity.
      Qed.
      rewrite is_array_distr.
      rewrite is_array_distr_off; simpl.
      cutrewrite (l - s (S n) + s (S n) = l); [|omega].
      assert (Heq : ntrd = (l - s (S n)) + (s (S n) - (l - s (S n))) + (l - s (S n)) + (ntrd - l))
        by lia.
      rewrite Heq at 2.
      repeat (rewrite is_array_concat; [|intros; destruct lt_dec; reflexivity]).
      cutrewrite (l - s (S n) + (s (S n) - (l - s (S n))) = s (S n)); [|lia].
      cutrewrite (s (S n) + (l - s (S n)) = l); [|lia].
      simpl; rewrite <-!sep_assoc; split; intros; repeat sep_cancel.
    + repeat rewrite (min_l _ ntrd); try omega.
      2: rewrite Nat.min_le_iff; try omega.
      repeat rewrite min_r; try omega.
      rewrite minus_diag; simpl; rewrite emp_unit_l.
      erewrite ls_init_eq0.
      Focus 2. { intros i Hi; destruct Sumbool.sumbool_and; try omega; reflexivity. } Unfocus.
      rewrite ls_star, is_array_distr, is_array_distr_off; simpl.
      assert (Heq : ntrd = s (S n) + s (S n) + (ntrd - (s (S n) + s (S n)))) by lia.
      rewrite Heq at 2; clear Heq.
      repeat (rewrite is_array_concat; [|intros; destruct lt_dec; reflexivity]).
      simpl; rewrite <-!sep_assoc.
      split; intros; repeat sep_cancel.
Qed.

Definition BSpre n i :=
  match n with
  | O => (Sh sdata +o (Zn i)) -->p (1, f_in i)
  | S n => Binv (f (S n)) n i
  end.

Definition BSpost n i := Binv (f n) n i.

Definition BS n := (@MyVector.init _ ntrd (fun i =>(BSpre n (nf i))),
                    @MyVector.init _ ntrd (fun i =>(BSpost n (nf i)))).

Lemma reduce_body_ok n i:
  CSL BS i
    (!(tid === Zn (nf i)) **
     !(len === Zn l) **
     !(x1 === f n (nf i)) **
     BSpre n (nf i))
    (reduce_body (S n) (s (S n)))
    (!(tid === Zn (nf i)) **
     !(len === Zn l) **
     !(x1 === f (S n) (nf i)) **
     BSpre (S n) (nf i)).
Proof.
  remember (S n) as sn.
  unfold reduce_body.
  eapply rule_seq; simpl.
  { subst sn; simpl; rewrite <-minus_n_O; unfold BS.
    hoare_forward.
    - intros s h H; sep_cancel; eauto.
    - simpl; rewrite MyVector.init_spec.
      unfold BSpost, Binv.
      intros s h H; sep_normal_in H; eauto. }
  hoare_forward; eauto.
  { eapply Hbackward.
    Focus 2. {
      intros st h H.
      sep_split_in H.
      change_in H.
      { unfold_pures.
        destruct Z_lt_dec; try congruence.
        destruct Sumbool.sumbool_and; unfold lt in *; try omega.
        sep_normal_in H.
        assert ((Sh sdata +o Zn (nf i) ===l Sh sdata +o tid) st (emp_ph loc)).
        { unfold_conn_all; simpl in *; f_equal; zify; unfold lt in *; omega. }
        sep_rewrite_in mps_eq1 H; [|exact H0].
        assert ((Sh sdata +o (Zn (nf i) + Zn (s (S n)))%Z ===l
                 Sh sdata +o (tid +C Zn (s (S n)))) st (emp_ph loc)).
        { unfold_conn_all; simpl in *; f_equal; zify; unfold lt in *; omega. }
        sep_lift_in H 1.
        sep_rewrite_in mps_eq1 H; [|subst sn; exact H1].
        apply H. }
      sep_combine_in H; exact H. } Unfocus.
    eapply rule_seq; [hoare_forward; eauto|].
    eapply rule_seq.
    { hoare_forward.
      intros s h [? H]; subA_normalize_in H. simpl in H. apply H. }
    eapply rule_seq; [hoare_forward|].
    intros s h [v H]; subA_normalize_in H. simpl in H.
    ex_intro v H; simpl in H; apply H.
    repeat hoare_forward.
    intros s h H; ex_intro x H; exact H. }
  { eapply rule_skip. }
  intros st h [[v H] | H]; sep_split_in H; unfold_pures; sep_split; eauto; sep_cancel.
  - unfold_conn; subst sn; simpl; eauto.
    destruct Sumbool.sumbool_and; unfold lt in *; try omega.
    destruct Z_lt_dec; try congruence; try omega.
  - unfold BSpre, Binv; subst sn; simpl.
    destruct Z_lt_dec; try congruence; try omega.
    destruct Sumbool.sumbool_and; unfold lt in *; try omega.
    sep_normal_in H; sep_normal.
    repeat sep_cancel.
    destruct Sumbool.sumbool_and; try omega.
    repeat sep_cancel.
    destruct Nat.eq_dec; eauto.
    sep_rewrite is_array_change; [sep_rewrite sep_comm; sep_rewrite is_array_change|].
    sep_rewrite sep_comm; eauto.
    intros; destruct Sumbool.sumbool_and; try lia.
    intros; destruct Sumbool.sumbool_and; try lia.
  - unfold_conn; subst sn; simpl; eauto.
    destruct Sumbool.sumbool_and; unfold lt in *; try lia.
    destruct Z_lt_dec; simpl in *; try congruence; try lia.
  - unfold BSpre, Binv; subst sn; simpl.
    destruct Z_lt_dec; simpl in *; try congruence; try omega.
    destruct Sumbool.sumbool_and; unfold lt in *; try omega.
    sep_normal_in H; sep_normal.
    destruct Nat.eq_dec; eauto.
    sep_rewrite is_array_change; [sep_rewrite sep_comm; sep_rewrite is_array_change|].
    sep_rewrite sep_comm; eauto.
    intros; destruct Sumbool.sumbool_and; try lia.
    intros; destruct Sumbool.sumbool_and; try lia.
  - unfold_conn; subst sn; simpl; eauto.
    destruct Sumbool.sumbool_and; unfold lt in *; try lia.
  - unfold BSpre, Binv; subst sn; simpl.
    destruct Sumbool.sumbool_and; unfold lt in *; try omega.
    sep_normal_in H; sep_normal.
    destruct Nat.eq_dec; eauto.
    sep_rewrite is_array_change; [sep_rewrite sep_comm; sep_rewrite is_array_change|].
    sep_rewrite sep_comm; eauto.
    intros; destruct Sumbool.sumbool_and; try lia.
    intros; destruct Sumbool.sumbool_and; try lia.
Qed.

Lemma reduce_aux_ok i t m :
  CSL BS i
    (!(tid === Zn (nf i)) **
     !(len === Zn l) **
     !(x1 === f t (nf i)) **
     BSpre t (nf i))
    (reduce_aux (S t) m)
    (!(tid === Zn (nf i)) **
     !(len === Zn l) **
     !(x1 === f (t + m) (nf i)) **
     BSpre (t + m) (nf i)).
Proof.
  revert t; induction m; simpl; intros t.
  - rewrite <-plus_n_O; apply rule_skip.
  - eapply rule_seq; eauto.
    apply reduce_body_ok.
    cutrewrite (t + S m = S t + m); [|omega]; eauto.
Qed.
Require Import Program.
Lemma reduce_ok0 i :
  CSL BS i
    (!(tid === Zn (nf i)) **
     !(len === Zn l) **
     !(x1 === f_in (nf i)) **
     (Sh sdata +o (Zn (nf i)) -->p (1, f_in (nf i))))
    reduce
    (!(tid === Zn (nf i)) **
     !(len === Zn l) **
     !(x1 === f e_b (nf i)) **
     if Nat.eq_dec (nf i) 0 then is_array (Sh sdata) ntrd (f e_b) 0 else emp).
Proof.
  unfold reduce.
  eapply rule_conseq; eauto using reduce_aux_ok.
  simpl; intros st h H.
  repeat sep_cancel.
  clear h H h0 H0 h1 H1.
  unfold BSpre, Binv in *.
  unfold s in *.
  destruct e_b; try omega; remember (S n) as e_b'.
  rewrite minus_diag in *; simpl in *.
  clear Heqe_b' n.
  destruct Nat.eq_dec.
  2: destruct Sumbool.sumbool_and; try omega; sep_normal_in H2; eauto.
  rewrite e in *; simpl in *.
  destruct Sumbool.sumbool_and; try lia.
  - destruct ntrd; try omega.
    rewrite min_r in H2; try omega; simpl in H2; sep_normal_in H2.
    simpl; sep_cancel.
    destruct n; simpl in *; try omega; repeat sep_cancel.
    rewrite <-minus_n_O in H0; eauto.
  - destruct ntrd; sep_normal_in H2; try omega.
    assert (l = 1) by omega; subst.
    simpl in *.
    rewrite <-minus_n_O in H2; sep_normal_in H2; sep_cancel.
Qed.

Theorem BS_ok b :
  Bdiv.Aistar_v (fst (BS b)) |= Bdiv.Aistar_v (snd (BS b)). 
Proof.
  unfold BS, BSpre, BSpost; simpl.
  intros s h H.
  destruct b.
  - istar_simplify_in H.
    apply is_array_distr in H.
    apply Binv_ok; simpl.
    eauto.
  - apply Binv_ok.
    apply Binv_ok in H; eauto.
Qed.
End Reduce0.