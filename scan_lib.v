Require Import GPUCSL.
Set Implicit Arguments.

Fixpoint sum_of (s len : nat) (f : nat -> Z) :=
  match len with
    | O => 0
    | S len => f s + sum_of (S s) len f
  end%Z.

Fixpoint skip_sum (skip : nat) (s len : nat) (f : nat -> Z) (i : nat) :=
  match len with
    | O => 0%Z
    | S len => 
      if Nat.eq_dec (s mod skip) i then f s + skip_sum skip (S s) len f i
      else skip_sum skip (S s) len f i
  end%Z.

Eval compute in skip_sum 3 0 10 (fun i => Z.of_nat i) 3.
Eval compute in skip_sum 3 4 10 (fun i => Z.of_nat i) 3.

Notation " p '>>1'" := (Ediv2 p) (at level 40, left associativity) : exp_scope.

Definition dbl s := if Nat.eq_dec s 0 then 1 else s * 2.

Definition ceil2 n := if Nat.eq_dec n 0 then 1 else n.

Lemma ceil2_dbl (s : nat):  ceil2 s + s <= dbl s.
Proof.
  destruct s; unfold dbl; destruct Nat.eq_dec; simpl; omega.
Qed.
Lemma ceil2_neq_0 (s : nat) : ceil2 s <> 0.
Proof.
  unfold ceil2; destruct Nat.eq_dec; simpl; omega.
Qed.

Hint Resolve ceil2_neq_0.

Lemma dbl_neq_0 (s : nat) : dbl s <> 0.
Proof.
  unfold dbl; destruct Nat.eq_dec; simpl; omega.
Qed.

Hint Resolve dbl_neq_0.

Definition arr_val_compat (len : nat) (f : nat -> Z) (sum : Z) :=
  match len with
    | O => f 0 = sum
    | _ => sum_of 0 len f = sum
  end.

Lemma arr_compat_same (len : nat) (fc : nat -> Z) :
  len <> 0 -> arr_val_compat len fc (sum_of 0 len fc).
Proof.
  induction len; simpl in *; auto; omega.
Qed.

Lemma sum_of_concat (l1 : nat) (fc : nat -> Z) : forall s l2,
  sum_of s (l1 + l2) fc = (sum_of s l1 fc + sum_of (l1 + s) l2 fc)%Z.
Proof.
  induction l1; [simpl; auto|].
  intros s l2; simpl. rewrite IHl1.
  rewrite plus_n_Sm; omega.
Qed.
   
Lemma shift_values (l1 : nat) (fc : nat -> Z) : forall s sft,
  (sum_of s l1 fc + sum_of (s + sft) l1 fc = sum_of s l1 (fun i => fc i + fc (i + sft)%nat))%Z.
Proof.
  induction l1; intros; simpl; auto.
  cutrewrite (S (s + sft) = S s + sft); [|omega].
  cutrewrite (
    (fc s + sum_of (S s) l1 fc + (fc (s + sft)%nat + sum_of (S s + sft) l1 fc)) =
    (fc s + (fc (s + sft)%nat + (sum_of (S s) l1 fc + sum_of (S s + sft) l1 fc))))%Z; [|ring].
  rewrite (IHl1 (S s) (sft)). omega.
Qed.

Lemma sum_of_eq (len : nat) (f1 f2 : nat -> Z) : forall s,
   (forall i, s <= i < s + len -> f1 i = f2 i) ->
   sum_of s len f1 = sum_of s len f2.
Proof.
  induction len; intros; simpl; auto.
  rewrite IHlen, (H s); auto; intros; try omega.
  apply H; omega.
Qed.

Lemma shift_arr (len : nat) (fc : nat -> Z) : forall s, 
   sum_of s (len * 2) fc = sum_of s len (fun i => if lt_dec i (s + len) then fc i + fc (i + len)%nat else fc i)%Z.
Proof.
  cutrewrite (len * 2 = len + len); [|omega].
  intros s; rewrite sum_of_concat.
  rewrite (plus_comm len s), shift_values.
  apply sum_of_eq; intros; destruct lt_dec; omega.
Qed.

Corollary shift_arr0 (len : nat) (fc : nat -> Z) : 
  sum_of 0 (len * 2) fc = sum_of 0 len (fun i => if lt_dec i len then fc i + fc (i + len)%nat else fc i)%Z.
Proof.
  apply shift_arr.
Qed.

Lemma skip_sum_nil next fc i : forall s (skip len : nat),
  (forall j, j < next -> (s + j) mod skip <> i) ->
  skip_sum skip s len fc i = skip_sum skip (s + next) (len - next) fc i.
Proof.
  induction next; intros s skip len Hj; simpl.
  - rewrite <-plus_n_O, <-minus_n_O; auto.
  - destruct len; auto.
    cutrewrite (s + S next = S s + next); [|omega].
    cutrewrite (S len - S next = len - next); [|omega].
    rewrite <-IHnext.
    + simpl; destruct Nat.eq_dec; auto.
      specialize (Hj 0); rewrite <-plus_n_O in Hj; apply Hj in e; [tauto|omega].
    + intros j Hjn; cutrewrite (S s + j = s + S j); [|omega]; apply Hj; omega.
Qed.

Lemma skip_sum_unfold (skip len : nat) fc i : forall s,
  skip <> 0 ->
  (i < len)%nat -> (i < skip)%nat ->
  skip_sum skip (s * skip) len fc i =
  (fc (i + s * skip)%nat + skip_sum skip (S s * skip)%nat (len - skip)%nat fc i)%Z.
Proof.
  intros s Hskip Hil His.
  rewrite skip_sum_nil with (next:=i). 
  2: intros; rewrite plus_comm, Nat.add_mod; auto.
  2: rewrite Nat.mod_mul; auto; rewrite <-plus_n_O, Nat.mod_mod; auto; rewrite Nat.mod_small; omega.
  assert (exists li, len - i = S li) as [li Hli] by (exists (len - i - 1); omega).
  rewrite (plus_comm (s * skip));
  rewrite Hli; simpl; destruct Nat.eq_dec as [He | He].
  2 : rewrite Nat.mod_add in He; auto; rewrite Nat.mod_small in He; omega.
  f_equal.
  rewrite skip_sum_nil with (next:= skip - S i).
  lazymatch goal with [|- context [skip_sum _ ?X _ _ _]] => cutrewrite (X = skip + s * skip); [|omega] end.
  cutrewrite (li - (skip - S i) = len - skip); [|omega]; auto.
  intros j Hj. 
  lazymatch goal with [|- context [?X mod _]] => cutrewrite (X = (S i + j) + s * skip); [|omega] end.
  rewrite Nat.mod_add; auto; rewrite Nat.mod_small; omega.
Qed.

Lemma skip_sum_double skip f' i :
  skip <> 0 -> i < skip ->
  forall len s,
  (skip_sum (skip * 2) (s * (skip * 2)) len f' i +
   skip_sum (skip * 2) (s * (skip * 2)) len f' (i + skip) =
   skip_sum skip       (s * (skip * 2)) len f' i)%Z.
Proof.
  induction len using lt_wf_ind.
  intros s; destruct (lt_dec i len).
  - rewrite skip_sum_unfold; try omega.
    assert (Heq : s * (skip * 2) = (2 * s) * skip); [ring | rewrite Heq at 3; clear Heq].
    destruct (lt_dec (i + skip) len).
    + rewrite (@skip_sum_unfold _ _ _ (i + skip)); try omega.
      rewrite (@skip_sum_unfold skip); try omega.
      rewrite (@skip_sum_unfold skip); try omega.
      cutrewrite (2 * s * skip = s * (skip * 2)); [|ring].
      cutrewrite (i + S (2 * s) * skip = i + skip + s * (skip * 2)); [|ring].
      cutrewrite (len - skip - skip = len - skip * 2); [|omega].
      cutrewrite (S (S (2 * s)) * skip = S s * (skip * 2)); [|ring].
      assert (Hlen : len - skip * 2 < len) by omega.
      erewrite <-(H1 (len - skip * 2) Hlen (S s)); ring.
    + rewrite (@skip_sum_unfold skip); try omega.
      rewrite (@skip_sum_nil len _ (i + skip)).
      2: intros j Hj Heq.
      2 : cutrewrite (s * (skip * 2) + j = j + s * (skip * 2)) in Heq; [|omega];
          rewrite Nat.mod_add in Heq; try omega; rewrite Nat.mod_small in Heq; try omega.
      rewrite minus_diag; simpl.
      rewrite (@skip_sum_nil (len - skip * 2)). 
      2: intros j Hj Heq.
      2 : cutrewrite (skip * 2 + s * (skip * 2) + j = j + (S s) * (skip * 2)) in Heq; [|omega];
          rewrite Nat.mod_add in Heq; try omega; rewrite Nat.mod_small in Heq; try omega.
      rewrite minus_diag; simpl.
      rewrite (@skip_sum_nil (len - skip)).
      2: intros j Hj Heq.
      2 : cutrewrite (skip + (s + (s + 0)) * skip + j = j + (S (s + (s + 0))) * skip) in Heq; [|ring];
          rewrite Nat.mod_add in Heq; try omega; rewrite Nat.mod_small in Heq; try omega.
      rewrite minus_diag; simpl.
      ring_simplify; f_equal; ring.
  - rewrite (@skip_sum_nil len).
    2: intros j Hj Heq;
      rewrite plus_comm, Nat.mod_add in Heq; try omega; rewrite Nat.mod_small in Heq; try omega.
    rewrite minus_diag; simpl.
    rewrite (@skip_sum_nil len).
    2: intros j Hj Heq;
      rewrite plus_comm, Nat.mod_add in Heq; try omega; rewrite Nat.mod_small in Heq; try omega.
    rewrite minus_diag; simpl.
    rewrite (@skip_sum_nil len).
    2: intros j Hj Heq.
    2: cutrewrite (s * (skip * 2) + j = j + s * 2 * skip) in Heq; [|ring];
       rewrite Nat.mod_add in Heq; try omega; rewrite Nat.mod_small in Heq; try omega.
    rewrite minus_diag; simpl; omega.
Qed.


Lemma arr_val_compat_n0 len g sum : len <> 0 ->
  (arr_val_compat len g sum <-> sum_of 0 len g = sum).
Proof.
  destruct len; simpl; split; auto; omega.
Qed.

Lemma dbl_inv (e : nat) : dbl ((2 ^ e / 2)) = 2 ^ e.
Proof.
  destruct e; [simpl; auto|].
  cutrewrite (2 ^ S e = 2 ^ e * 2); [rewrite Nat.div_mul; auto|simpl; omega].
  unfold dbl; destruct Nat.eq_dec; try omega.
  apply Nat.pow_nonzero in e0; auto; tauto.
Qed.

Lemma skip_sum_sum fc : forall len s,
  skip_sum 1 s len fc 0 = sum_of s len fc.
Proof.
  induction len; simpl; auto.
  intros s.
  rewrite IHlen; auto.
Qed.


Lemma div_mult (n m : nat) : m <> 0 -> n / m * m <= n.
Proof.
  intros Hm0.
  destruct n.
  rewrite Nat.div_0_l; simpl; omega.
  unfold "/"; destruct m; [omega|].
  destruct (divmod (S n) m 0 m) eqn:Heq; simpl.
  pose proof (divmod_spec (S n) m 0 m (le_n m)); rewrite Heq in *.
  rewrite mult_0_r, minus_diag, <-!plus_n_O in H.
  destruct H; rewrite mult_comm; omega.
Qed.

Lemma dbl_mono (n m : nat) : n < m -> dbl n < dbl m.
Proof.
  unfold dbl; repeat destruct Nat.eq_dec; omega.
Qed.

Lemma dbl_pow (n : nat) : dbl (2 ^ n) = 2 ^ (S n).
Proof.
  assert (2 ^ n <> 0) by (apply Nat.pow_nonzero; auto).
  unfold dbl; destruct Nat.eq_dec; simpl; omega. 
Qed.
Hint Rewrite dbl_pow : sep.

Lemma pow_divS (n m : nat) : (n <> 0) -> n ^ (S m) / n = n ^ m.
Proof.
  intros; cutrewrite (n ^ (S m) = n * n ^ m); [|auto].
  rewrite mult_comm, Nat.div_mul; omega.
Qed.

Hint Rewrite div_Zdiv Zdiv2_div dbl_inv pow_divS : sep.

Lemma ceil2_pow (n : nat) : ceil2 (2 ^ n) = 2 ^ n.
Proof.
  assert (2 ^ n <> 0) by (apply Nat.pow_nonzero; auto).
  unfold ceil2; destruct Nat.eq_dec; simpl; omega. 
Qed.
Hint Rewrite ceil2_pow : sep.
Hint Resolve Nat.pow_nonzero.
Hint Rewrite minus_diag Z.add_0_r : sep.
Hint Rewrite <-plus_n_O : sep.

Lemma skip_sum1 (skip : nat) (fc : nat -> Z) (i : nat) :
  skip <> 0 -> i < skip ->
  skip_sum skip 0 skip fc i = fc i.
Proof.
  intros Hskip0 Hiskip.
  cutrewrite (0 = 0 * skip); [|auto].
  rewrite skip_sum_unfold; auto; rewrite minus_diag; simpl; autorewrite with sep; auto.
Qed.

Ltac unfold_pures :=
  repeat lazymatch goal with
    | [H : (bexp_to_assn _) ?s emp_ph |- _] => bexp H
    | [H : _ ?s emp_ph |- _ ] => unfold_conn_in H; simpl in H
  end.
  
Import Vector.VectorNotations.

Lemma vs_exists {T : Type} {n : nat} (P : T -> Fin.t n -> assn) : 
  n <> 0 -> 
  forall s, s ||= Bdiv.Aistar_v (MyVector.init (fun i : Fin.t n => Ex x : T, P x i)) <=>
       Ex vs : Vector.t T n, Bdiv.Aistar_v (MyVector.init (fun i => P vs[@i] i)).
Proof.
  induction n as [|[|n]]; simpl; intros Hn0 s h; try omega.
  - split; intros H.
    + apply ex_lift_l_in in H; destruct H as [x H].
      exists [x]; simpl; auto.
    + apply ex_lift_l; destruct H as [x H].
      exists x[@Fin.F1]; auto.
  - split; intros H.
    + apply ex_lift_l_in in H; destruct H as [x0 H].
      set (P' := fun (x : T) (i : Fin.t (S n)) => P x (Fin.FS i)).
      lazymatch type of H with
      | (_ ** ?X) s h =>
        cutrewrite (X = Bdiv.Aistar_v
           (MyVector.init (fun i : Fin.t (S n) => Ex x : T, P' x i))) in H; [|unfold P'; auto]
      end.
      sep_rewrite_in IHn H; [|omega].
      apply ex_lift_r_in in H; destruct H as [xs H].
      exists (x0 :: xs); simpl; sep_cancel.
    + destruct H as [xs H].
      apply ex_lift_l.
      Require Import Program.
      dependent destruction xs; exists h0; sep_cancel.
      set (P' := fun (x : T) (i : Fin.t (S n)) => P x (Fin.FS i)).
      lazymatch goal with
      | [|- ?X s h] =>
        cutrewrite (X = Bdiv.Aistar_v
           (MyVector.init (fun i : Fin.t (S n) => Ex x : T, P' x i))); [|unfold P'; auto]
      end.
      lazymatch goal with
        | [|- ?X s h] => pattern X
      end.
      rewrite IHn; [|omega].
      exists xs; simpl; sep_cancel.
Qed.

Fixpoint ls_init {T : Type} s (n : nat) (f : nat -> T) := 
  match n with
    | O => nil
    | S n => f s :: ls_init (S s) n f
  end%list.

Lemma ls_init_eq {T : Type} (fc fc' : nat -> T) n: forall s s',
  (forall i, i < n -> fc (s + i) = fc' (s' + s + i)) -> 
  ls_init s n fc = ls_init (s' + s) n fc'.
Proof.
  induction n; simpl; intros s s' H; auto.
  cutrewrite (s' + s = s' + s + 0); [|omega].
  rewrite <-H; f_equal; (omega || auto).
  cutrewrite (S (s' + s + 0) = s' + S s); [apply IHn|omega].
  intros i Hi.
  cutrewrite (S s + i = s + S i); [|omega].
  cutrewrite (s' + S s + i = s' + s + S i); [|omega].
  apply H; omega.
Qed.

Lemma ls_init_eq' {T : Type} (fc fc' : nat -> T) n: forall s,
  (forall i, i < n -> fc (s + i) = fc' (s + i)) -> 
  ls_init s n fc = ls_init s n fc'.
Proof.
  intros; cutrewrite (s = 0 + s); auto; apply ls_init_eq; simpl.
  apply H.
Qed.

Lemma vs_star {n : nat} (P Q : Fin.t n -> assn) : 
  forall s, s ||= Bdiv.Aistar_v (MyVector.init (fun i => P i ** Q i)) <=>
    Bdiv.Aistar_v (MyVector.init (fun i => P i)) **
    Bdiv.Aistar_v (MyVector.init (fun i => Q i)).
Proof.
  induction n; [simpl; intros |].
  - split; intros; [sep_rewrite_in_r emp_unit_l H | sep_rewrite_in emp_unit_l H]; auto.
  - intros s; split; simpl; intros H.
    + sep_normal_in H; sep_normal; repeat sep_cancel.
      sep_rewrite_in IHn H0; auto.
    + sep_normal_in H; sep_normal; repeat sep_cancel.
      sep_rewrite_in_r IHn H0; auto.
Qed.

Lemma pure_emp_in (P : assn) (s : stack) (h : pheap) :
  !(P) s h -> P s emp_ph /\ emp s h.
Proof.
  unfold_conn; simpl; destruct 1.
  apply emp_emp_ph_eq in H; subst; split; auto.
Qed.

Lemma phplus_emp (ph1 ph2 : pheap) :
  phplus ph1 ph2 = emp_ph -> ph1 = emp_ph /\ ph2 = emp_ph.
Proof.
  destruct ph1 as [ph1 ?], ph2 as [ph2 ?]; unfold emp_ph; simpl; intros H.
  split; apply pheap_eq; extensionality x; apply (f_equal (fun f => f x)) in H;
  unfold phplus in H; destruct (ph1 x) as [[? ?]|], (ph2 x) as [[? ?]|];
  unfold emp_h in *; congruence.
Qed.

Lemma emp_star (P Q : assn) s:
  (P ** Q) s emp_ph <-> P s emp_ph /\ Q s emp_ph.
Proof.
  unfold_conn; split; intros.
  - destruct H as (? & ? & ? & ? & ? & ?).
    apply phplus_emp in H2 as [? ?]; subst; tauto.
  - exists emp_ph emp_ph; repeat split; tauto.
Qed.      

Lemma pure_star (P Q : assn) : forall s, s ||= !(P ** Q) <=> !(P) ** !(Q).
Proof.
  intros s; split; intros H.
  - sep_split;
    apply pure_emp_in in H; destruct H;
    apply emp_star in H.
    + tauto.
    + apply pure_emp; tauto.
  - apply pure_emp; [apply emp_star|];
    sep_split_in H; apply pure_emp_in in H; tauto.
Qed.

Lemma vs_pure {n : nat} (P : Fin.t n -> assn) :  forall s,
  s ||= Bdiv.Aistar_v (MyVector.init (fun i => !(P i))) <=>
        !(Bdiv.Aistar_v (MyVector.init (fun i => P i))).
Proof.
  induction n; [simpl; intros|].
  - split; intros; simpl.
    apply pure_emp; [apply emp_emp_ph|auto].
    unfold_conn_all; destruct H; auto.
  - intros s; split; simpl; intros H.
    + apply pure_star; sep_cancel.
      apply IHn; auto.
    + apply pure_star in H; sep_cancel.
      apply IHn; auto.
Qed.

Lemma vs_emp {n : nat} (P : Vector.t assn n) s i : 
  Bdiv.Aistar_v P s emp_ph -> P[@i] s emp_ph.
Proof.
  induction n; intros; [inversion i|].
  dependent destruction i; dependent destruction P; simpl in *; apply emp_star in H as [H1 H2]; auto.
Qed.
    
Ltac sep_rewrite lem :=
  match goal with
    | [|- ?X _ _] => pattern X
  end; erewrite lem; cbv beta. 

(* separating conjunction on a vector <-> a list *)
Lemma sc_v2l (n : nat) (ass : Vector.t assn n) :
  forall s,
  s ||= Bdiv.Aistar_v ass  <=> conj_xs (Vector.to_list ass).
Proof.
  dependent induction ass; intros s; simpl; [reflexivity|].
  fold (Vector.to_list ass).
  rewrite <-IHass; reflexivity.
Qed.

(* assert (forall i : nat, i = i) by (intros; auto). *)
Ltac fun_rewrite_in lem H :=
  match type of H with
  | context f [?X] => 
    lazymatch type of X with
      | _ -> _ =>
        erewrite (@functional_extensionality _ _ X) in H; [|intros; rewrite lem; reflexivity]
  end
end.

Ltac fun_rewrite lem H :=
  match goal with
    | [|- context f [?X]] => 
      lazymatch type of X with
        | _ -> _ =>
          erewrite (@functional_extensionality _ _ X); [|intros; rewrite lem; reflexivity]
  end
end.

Lemma vec_to_list_init {T : Type} (n : nat) (fc : Fin.t n -> T) (d : T) : forall s,
  Vector.to_list (MyVector.init fc) = 
  ls_init s n (fun i => match Fin.of_nat (i - s) n with
                          | inleft idx => fc idx
                          | _ => d
                        end).
Proof.
  induction n; [reflexivity|].
  simpl; unfold ls_init, Vector.to_list; simpl; intros s.
  f_equal; [rewrite minus_diag; reflexivity|].
  
  fold (Vector.to_list (MyVector.init (fun i => fc (Fin.FS i)))); rewrite (IHn _ s).
  fold (@ls_init T (S s) n).
  cutrewrite (S s = 1 + s); [apply ls_init_eq|]; auto; intros i.
  cutrewrite (s + i - s = i); [|omega].
  cutrewrite (1 + s + i - s = S i); [|omega].
  intros H.
  simpl; destruct Fin.of_nat; reflexivity.
Qed.

Lemma vec_to_list_init0 {T : Type} (n : nat) (fc : Fin.t n -> T) (d : T) :
  Vector.to_list (MyVector.init fc) = 
  ls_init 0 n (fun i => match Fin.of_nat i n with
                          | inleft idx => fc idx
                          | _ => d
                        end).
Proof.
  rewrite (@vec_to_list_init _ _ _ d 0); f_equal; extensionality x.
  destruct (minus_n_O x); (omega || auto).
Qed.  

Lemma ls_init_eq0 {T : Type} (n : nat) (fc fc' : nat -> T) :
  (forall i, i < n -> fc i = fc' i) ->
  ls_init 0 n fc = ls_init 0 n fc'.
Proof.
  intros; rewrite (@ls_init_eq _ _ fc' n 0 0); auto.
Qed.

Lemma Fin_nat_inv (n : nat) (t : Fin.t n) : forall i,
  Fin.of_nat i n = inleft t -> ` (Fin.to_nat t) = i.
Proof.
  induction n; [inversion t|].
  destruct i; simpl; [inversion 1; reflexivity|].
  destruct (Fin.of_nat i n) eqn:Heq.
  apply IHn in Heq.
  inversion 1; subst; simpl; destruct (Fin.to_nat); auto.
  inversion 1.
Qed.

Lemma ls_exists {T : Type} (d : T) {n : nat} (P : T -> nat -> assn) : 
  forall b s, s ||= conj_xs (ls_init b n (fun i => Ex x : T, P x i)) <=>
     Ex vs : list T, !(pure (length vs = n)) ** conj_xs (ls_init b n (fun i => P (nth (i - b) vs d) i)).
Proof.
  induction n as [|n]; simpl; intros b s h; try omega.
  - split; intros H.
    exists (@nil T); sep_split; cbv; auto.
    destruct H as [vs H]; sep_split_in H; auto.
  - split; intros H.
    + apply ex_lift_l_in in H; destruct H as [x0 H].
      sep_rewrite_in IHn H.
      apply ex_lift_r_in in H; destruct H as [xs H].
      sep_split_in H.
      exists (x0 :: xs)%list; sep_split.
      unfold_conn; unfold_conn_in HP; simpl; omega.
      rewrite minus_diag; simpl; sep_cancel.
      erewrite ls_init_eq'; [apply H0|].
      intros.
      cutrewrite (S b + i - b = S i); [|omega]; cutrewrite (S b + i - S b = i); [|omega]; auto.
    + destruct H; sep_split_in H; rewrite minus_diag in H.
      apply ex_lift_l; exists (nth 0 x d).
      sep_cancel.
      destruct x; [inversion HP|].
      apply IHn; exists x; sep_split; auto; [unfold_conn_in HP; simpl in HP; unfold_conn; omega|].
      erewrite ls_init_eq'; [apply H0|].
      intros.
      cutrewrite (S b + i - S b = i); [|omega].
      cutrewrite (S b + i - b = S i); [|omega].
      simpl. reflexivity.
Qed.

Lemma ls_exists0 {T : Type} (d : T) {n : nat} (P : T -> nat -> assn) : 
  forall s, s ||= conj_xs (ls_init 0 n (fun i => Ex x : T, P x i)) <=>
     Ex vs : list T, !(pure (length vs = n)) ** conj_xs (ls_init 0 n (fun i => P (nth i vs d) i)).
Proof.
  intros.
  rewrite ls_exists; split; [intros [vs H]; exists vs; sep_cancel;
  [erewrite ls_init_eq'; [apply H|]..]..]; intros; simpl; auto.
  simpl; rewrite <-minus_n_O; reflexivity.
  rewrite <-minus_n_O; reflexivity.
Qed.

Lemma ls_pure {n : nat} (P : nat -> assn) :  forall b s,
  s ||= conj_xs (ls_init b n (fun i => !(P i))) <=>
        !(conj_xs (ls_init b n (fun i => P i))).
Proof.
  induction n; [simpl; intros|].
  - split; intros; simpl.
    apply pure_emp; [apply emp_emp_ph|auto].
    unfold_conn_all; destruct H; auto.
  - intros s; split; simpl; intros H.
    + apply pure_star; sep_cancel.
      apply IHn; auto.
    + apply pure_star in H; sep_cancel.
      apply IHn; auto.
Qed.

Definition TrueP (s : stack) (h : pheap) := True.

Lemma ls_emp (P : list assn) s : forall i,
  conj_xs P s emp_ph -> (nth i P TrueP) s emp_ph.
Proof.
  induction P; intros; destruct i; simpl in *; unfold TrueP; auto.
  apply emp_star in H; tauto.
  apply IHP; apply emp_star in H; tauto.
Qed.

Lemma ls_emp' (P : list assn) s :
  (forall i, i < length P -> (nth i P TrueP) s emp_ph) -> conj_xs P s emp_ph.
Proof.
  induction P; intros; simpl; [apply emp_emp_ph|].
  apply emp_star; split.
  - specialize (H 0); simpl in H; apply H; omega.
  - apply IHP; intros i Hi; specialize (H (S i)); simpl in H; apply H; omega.
Qed.

Lemma ls_init_spec {T : Type} (n : nat) (fc : nat -> T) d: forall i,
  forall b, nth i (ls_init b n fc) d = if lt_dec i n then fc (b + i) else d.
Proof.
  induction n; simpl; intros [|i] b; auto.
  destruct (lt_dec 0 (S n)); f_equal; try omega.
  rewrite IHn; destruct (lt_dec i n), (lt_dec (S i) (S n)); try omega; auto.
  f_equal; omega.
Qed.

Lemma ls_star {n : nat} (P Q : nat -> assn) : 
  forall b s, s ||= conj_xs (ls_init b n (fun i => P i ** Q i)) <=>
    conj_xs (ls_init b n (fun i => P i)) **
    conj_xs (ls_init b n (fun i => Q i)).
Proof.
  induction n; [simpl; intros |].
  - split; intros; [sep_rewrite_in_r emp_unit_l H | sep_rewrite_in emp_unit_l H]; auto.
  - intros s; split; simpl; intros H.
    + sep_normal_in H; sep_normal; repeat sep_cancel.
      sep_rewrite_in IHn H0; auto.
    + sep_normal_in H; sep_normal; repeat sep_cancel.
      sep_rewrite_in_r IHn H0; auto.
Qed.

Lemma init_length {T : Type} (n : nat) (fc : nat -> T) :
  forall b,length (ls_init b n fc) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma ls_init_nth {T : Type} (ls : list T) (d : T) : forall n b, 
  length ls = n ->
  ls_init b n (fun i => nth (i - b) ls d) = ls.
Proof.
  induction ls; simpl; intros n b H.
  - subst; simpl; auto.
  - subst; simpl; rewrite minus_diag; f_equal.
    erewrite ls_init_eq'; [apply IHls; auto|].
    intros i Hi; cutrewrite (S b + i - b = S i); [|omega]; simpl.
    cutrewrite (b + i - b = i); [|omega]; auto.
Qed.

Lemma firstn_init {T : Type} (fc : nat -> T) : forall n b m,
  firstn m (ls_init b n fc) = ls_init b (min m n) fc.
Proof.
  induction n; intros; simpl.
  - destruct m; simpl; auto.
  - destruct m; simpl; auto.
    f_equal; apply IHn.
Qed.

Lemma skipn_init {T : Type} (fc : nat -> T) : forall n b m,
  skipn m (ls_init b n fc) = ls_init (m + b) (n - m) fc.
Proof.
  induction n; destruct m; simpl; auto.
  rewrite IHn; f_equal; omega.
Qed.


Lemma nt_step_lt (i s : nat) : s <> 0 -> nt_step s i < s.
Proof.
  intros; unfold nt_step; apply Nat.mod_upper_bound; auto.
Qed.

Hint Resolve nt_step_lt.

Lemma init_emp_emp (n : nat) : forall b s,
  s ||= conj_xs (ls_init b n (fun _ => emp)) <=> emp.
Proof.
  induction n; simpl; intros; [reflexivity|].
  split; intros H.
  sep_rewrite_in IHn H. sep_rewrite_in emp_unit_l H; auto.
  sep_rewrite IHn; sep_rewrite emp_unit_l; auto.
Qed.
