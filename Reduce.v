Require Import GPUCSL.
Require Import scan_lib.
Require Import LibTactics Psatz.

Section Reduce.

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
  | S m => reduce_body t (s t) ;; reduce_aux (S t) m
  end.

Definition reduce := reduce_aux 1 e_b.  

Lemma even_odd_dec m :
  {exists n, m = 2 * n} + {exists n, m = 2 * n + 1}.
Proof.
  rewrite (Nat.div_mod m 2); try omega.
  destruct (m mod 2) as [| [| ?]] eqn:Heq.
  - left; exists (m / 2); omega.
  - right; exists (m / 2); omega.
  - assert (m mod 2 <= 1) by (lets: (Nat.mod_upper_bound m 2); omega).
    omega.
Defined.

