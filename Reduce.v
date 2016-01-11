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

Section simfun.

Definition s n := 2 ^ (e_b - n).

Fixpoint f n i :=
  match n with
  | O => f_in i
  | S n => if lt_dec (i + s (S n)) l
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

Lemma f_inv n :
  S n <= e_b ->
  sum_of 0 (min l (s (S n))) (f (S n)) = sum_of 0 (min l (s n)) (f n).
Proof.
  intros Hsneb.
  simpl.
  assert (Hsn : s (S n) + s (S n) = s n).
  { unfold s.
    assert (Heq : e_b - n = S (e_b - S n)) by omega; rewrite Heq; simpl; eauto. }
  assert (l <= s (S n) \/ s (S n) < l < s n \/ s n <= l) as [HsSnl | [HsSnl | HsSnl] ] by omega.
  - erewrite (sum_of_eq (min l (s (S n)))).
    Focus 2.
    { simpl; intros i Hi.
      assert (i <= l) by nia.
      destruct lt_dec; try omega.
      reflexivity. } Unfocus.
    rewrite !min_l; omega.
  - erewrite (sum_of_eq (min l (s (S n)))).
    Focus 2.
    { simpl; intros i Hi.
      instantiate (1 := fun i => if lt_dec i (l - s (S n))
                        then (f n i + f n (i + s (S n))%nat)%Z
                        else f n i); simpl.
      repeat destruct lt_dec; try omega. } Unfocus.
    rewrite sum_of_split; try omega.
    2: simpl; rewrite Nat.min_glb_lt_iff; split; try omega.
    rewrite <-minus_n_O.
    rewrite (min_l _ (s n)); try omega.
    rewrite min_r; try omega.
    cutrewrite (s (S n) - (l - s (S n)) = s n - l);[|omega].
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
      destruct lt_dec; try omega.
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
  (Cbarrier (n * 2 - 2) ;;
   Cif (tid +C Zn s <C len) (
     x0 ::= [ Sh sdata +o (tid + Zn s) ];;
     x2 ::= x1 +C x0 ;;
     x1 ::= x2   
   ) Cskip;;
   Cbarrier (n * 2 - 1) ;;
   [ Sh sdata +o tid] ::= x1)%exp.

Fixpoint reduce_aux t m :=
  match m with
  | O => Cskip
  | S m =>
    reduce_body t (s t) ;; reduce_aux (S t) m 
  end.

Definition reduce := reduce_aux 1 e_b.  

Lemma even_odd_dec m :
  {n | m = 2 * n} + {n | m = 2 * n + 1}.
Proof.
  rewrite (Nat.div_mod m 2); try omega.
  destruct (m mod 2) as [| [| ?]] eqn:Heq.
  - left; exists (m / 2); omega.
  - right; exists (m / 2); omega.
  - assert (m mod 2 <= 1) by (lets: (Nat.mod_upper_bound m 2); omega).
    omega.
Defined.
Notation perm_n n := (1 / injZ (Zn n))%Qc.
Definition BSpre i n := 
  match even_odd_dec n with
  | inl (exist m _) => (Sh sdata +o (Zn i)) -->p (1,  f m i)
  | inr (exist m _) => is_array_p (Sh sdata) ntrd (f m) 0 (perm_n ntrd)
  end.

Definition BSpost i n := 
  match even_odd_dec n with
  | inl (exist m _) => is_array_p (Sh sdata) ntrd (f m) 0 (perm_n ntrd)
  | inr (exist m _) => (Sh sdata +o (Zn i)) -->p (1,  f m i)
  end.

Definition BS n := (@MyVector.init _ ntrd (fun i =>(BSpre (nf i) n)),
                    @MyVector.init _ ntrd (fun i =>(BSpost (nf i) n))).

Lemma reduce_body_ok n i:
  CSL BS i
    (!(tid === Zn (nf i)) **
     !(len === Zn l) **
     !(x1 === f n (nf i)) **
     (Sh sdata +o (Zn (nf i)) -->p (1, f n (nf i))))
    (reduce_body (S n) (s (S n)))
    (!(tid === Zn (nf i)) **
     !(len === Zn l) **
     !(x1 === f (S n) (nf i)) **
     (Sh sdata +o (Zn (nf i)) -->p (1, f (S n) (nf i)))).
Proof.
  remember (S n) as sn.
  unfold reduce_body.
  eapply rule_seq; simpl.
  { subst sn; simpl; rewrite <-minus_n_O; unfold BS, BSpre, BSpost.
    hoare_forward.
    - destruct even_odd_dec as [[m ?] |[m ?]]; try now (repeat intros ?; omega).
      assert (n = m) by omega; subst m; intros s h H; sep_normal; repeat sep_cancel.
      apply H0.
    - simpl; rewrite MyVector.init_spec.
      destruct even_odd_dec as [[m ?] |[m ?]]; try now (repeat intros ?; omega).
      intros s h H; eauto.
      assert (n = m) by omega; subst m; eauto. }
  eapply rule_seq.
  { hoare_forward; eauto.
    - eapply Hbackward.
      Focus 2. {
        intros st h H.
        sep_split_in H.
        change_in H.
        { unfold_pures.
          lets Heq: (>>is_array_unfold ((nf i) + s (S n))).
          sep_rewrite_in Heq H; clear Heq; try (unfold lt in *; subst sn; omega).
          assert ((Sh sdata +o Zn (nf i + s (S n) + 0) ===l
                               Sh sdata +o (tid +C Zn (s (S n)))) st (emp_ph loc)).
          { unfold_conn_all; simpl in *; f_equal; zify; unfold lt in *; omega. }
          sep_rewrite_in mps_eq1 H; [|exact H0].
          apply H. }
        sep_combine_in H; exact H. } Unfocus.
      eapply rule_seq; [hoare_forward; eauto|].
      eapply rule_seq.
      { hoare_forward.
        intros s h [? H]; subA_normalize_in H. simpl in H. apply H. }
      hoare_forward.
      intros s h [v H]; subA_normalize_in H. simpl in H.
      ex_intro v H; simpl in H; apply H.
    - apply rule_skip. }
  eapply Hforward.
  { apply rule_disj.
    - repeat hoare_forward.
      unfold BS, BSpre, BSpost; simpl; eapply rule_seq; [hoare_forward|eauto].
      destruct even_odd_dec as [[m H]|[m H]]; try now (repeat intros ?; omega).
      assert (n = m) by omega; subst m; clear H.
      intros st h H.
      sep_split_in H; sep_normal_in H; sep_normal; unfold lt in *.
      lets Heq: (>>is_array_unfold ((nf i) + s (S n))).
      sep_rewrite Heq; clear Heq; try (unfold lt in *; unfold_pures; subst sn; omega).
      unfold lt in *; sep_normal_in H; sep_normal; repeat sep_cancel.
      assert ((Sh sdata +o Zn (nf i + s (S n) + 0) ===l
               Sh sdata +o (tid +C Zn (s (S n)))) st (emp_ph loc)).
      { unfold_conn_all; simpl in *; f_equal; zify; unfold lt in *; omega. }
      sep_rewrite mps_eq1; [|exact H2].
      sep_combine_in H1; sep_cancel.
      simpl; rewrite MyVector.init_spec.
      destruct even_odd_dec as [[m H]|[m H]]; try now (repeat intros ?; omega).
      assert (n = m) by omega; subst m; clear H; eauto.

      hoare_forward; eauto.
      intros st h H.
      ex_intro x H; apply H.
    - unfold BS, BSpre, BSpost; simpl; eapply rule_seq; [hoare_forward|eauto].
      destruct even_odd_dec as [[m H]|[m H]]; try now (repeat intros ?; omega).
      assert (n = m) by omega; subst m; clear H.
      intros st h H.
      sep_normal_in H; sep_cancel; eauto.
      simpl; rewrite MyVector.init_spec.
      destruct even_odd_dec as [[m H]|[m H]]; try now (repeat intros ?; omega).
      assert (n = m) by omega; subst m; clear H.
      eauto.
      hoare_forward; eauto. }
  intros st h [[v H] | H]; sep_split_in H; unfold_pures; sep_split; eauto; sep_cancel.
  - unfold_conn; subst sn; simpl.
    destruct lt_dec; try (zify; unfold lt in *; omega).
    rewrite <-plus_n_O in *; unfold lt in *; omega.
  - subst sn; simpl.
    destruct lt_dec; try (zify; unfold lt in *; omega).
    rewrite <-plus_n_O in *; unfold lt in *; sep_cancel.
  - unfold_conn; subst sn; simpl.
    destruct lt_dec; try (zify; unfold lt in *; omega).
  - subst sn; simpl.
    destruct lt_dec; try (zify; unfold lt in *; omega).
    sep_cancel.
Qed.

Lemma reduce_aux_ok i t m :
  CSL BS i
    (!(tid === Zn (nf i)) **
     !(len === Zn l) **
     !(x1 === f t (nf i)) **
     (Sh sdata +o (Zn (nf i)) -->p (1, f t (nf i))))
    (reduce_aux (S t) m)
    (!(tid === Zn (nf i)) **
     !(len === Zn l) **
     !(x1 === f (t + m) (nf i)) **
     (Sh sdata +o (Zn (nf i)) -->p (1, f (t + m) (nf i)))).
Proof.
  revert t; induction m; simpl; intros t.
  - rewrite <-plus_n_O; apply rule_skip.
  - eapply rule_seq; eauto.
    apply reduce_body_ok.
    cutrewrite (t + S m = S t + m); [|omega]; eauto.
Qed.

Theorem reduce_ok i :
  CSL BS i
    (!(tid === Zn (nf i)) **
     !(len === Zn l) **
     !(x1 === f_in (nf i)) **
     (Sh sdata +o (Zn (nf i)) -->p (1, f_in (nf i))))
    reduce
    (!(tid === Zn (nf i)) **
     !(len === Zn l) **
     !(x1 === f e_b (nf i)) **
     (Sh sdata +o (Zn (nf i)) -->p (1, f e_b (nf i)))).
Proof.
  unfold reduce.
  eapply rule_conseq; eauto using reduce_aux_ok.
Qed.


Lemma is_array_distr e n (f' : nat -> Z) :
  forall s stk,
    stk ||= conj_xs (ls_init s n (fun i => e +o Zn i -->p (1, f' i))) <=>
        is_array e n f' s.
Proof.
  induction n; intros s stk; simpl.
  - reflexivity.
  - rewrite IHn; reflexivity.
Qed.

Theorem BS_ok b :
  Bdiv.Aistar_v (fst (BS b)) |= Bdiv.Aistar_v (snd (BS b)). 
Proof.
  unfold BS, BSpre, BSpost; simpl.
  intros s h H.
  destruct (even_odd_dec b) as [[m Hb] | [m Hb]]; subst b.
  - istar_simplify_in H.
    apply is_array_distr in H.
    apply sc_v2l; rewrite (vec_to_list_init0 _ emp); erewrite ls_init_eq0.
    2: intros i Hi; destruct (Fin.of_nat i ntrd) as [|[? Hex]]; try omega.
    2: cutrewrite (is_array_p (Sh sdata) ntrd (f m) 0 (perm_n ntrd) =
                   id (fun i : nat => is_array_p (Sh sdata) ntrd (f m) 0 (perm_n ntrd)) i); eauto.
    unfold id.
    apply is_array_is_array_p_1; eauto.
  - istar_simplify.
    apply is_array_distr.
    apply sc_v2l in H; rewrite (vec_to_list_init0 _ emp) in H; erewrite ls_init_eq0 in H.
    2: intros i Hi; destruct (Fin.of_nat i ntrd) as [|[? Hex]]; try omega.
    2: cutrewrite (is_array_p (Sh sdata) ntrd (f m) 0 (perm_n ntrd) =
                   id (fun i : nat => is_array_p (Sh sdata) ntrd (f m) 0 (perm_n ntrd)) i); eauto.
    unfold id in H.
    apply is_array_is_array_p_1 in H; eauto.
Qed.
End Reduce0.