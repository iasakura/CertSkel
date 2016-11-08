Require Import GPUCSL.
Set Implicit Arguments.
Require Import Bdiv.
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
  destruct (Nat.divmod (S n) m 0 m) eqn:Heq; simpl.
  pose proof (Nat.divmod_spec (S n) m 0 m (le_n m)); rewrite Heq in *.
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
    | [H : (bexp_to_assn _) ?s (emp_ph loc) |- _] => bexp H
    | [H : _ ?s (emp_ph loc) |- _ ] => unfold_conn_in H; simpl in H
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
      dependent destruction xs; exists h0; simpl in H; sep_cancel.
      set (P' := fun (x : T) (i : Fin.t (S n)) => P x (Fin.FS i)).
      lazymatch goal with
      | [|- ?X s ?h] =>
        cutrewrite (X = Bdiv.Aistar_v
           (MyVector.init (fun i : Fin.t (S n) => Ex x : T, P' x i))); [|unfold P'; auto]
      end.
      lazymatch goal with
        | [|- ?X s ?h] => pattern X
      end.
      rewrite IHn; [|omega].
      exists xs; simpl in *; sep_cancel.
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
      sep_rewrite_in IHn H1; auto.
    + sep_normal_in H; sep_normal; repeat sep_cancel.
      sep_rewrite_in_r IHn H1; auto.
Qed.

Lemma phplus_emp (ph1 ph2 : pheap) :
  phplus ph1 ph2 = (emp_ph loc) -> ph1 = (emp_ph loc) /\ ph2 = (emp_ph loc).
Proof.
  destruct ph1 as [ph1 ?], ph2 as [ph2 ?]; unfold emp_ph; simpl; intros H.
  split; apply pheap_eq; extensionality x; apply (f_equal (fun f => f x)) in H;
  unfold phplus in H; destruct (ph1 x) as [[? ?]|], (ph2 x) as [[? ?]|];
  unfold emp_h in *; congruence.
Qed.

Lemma emp_star (P Q : assn) s:
  (P ** Q) s (emp_ph loc) <-> P s (emp_ph loc) /\ Q s (emp_ph loc).
Proof.
  unfold_conn; split; intros.
  - destruct H as (? & ? & ? & ? & ? & ?).
    apply phplus_emp in H2 as [? ?]; subst; tauto.
  - exists (emp_ph loc), (emp_ph loc); repeat split; tauto.
Qed.      

Lemma pure_star (P Q : assn) : forall s, s ||= !(P ** Q) <=> !(P) ** !(Q).
Proof.
  intros s; split; intros H.
  - sep_split;
    apply pure_emp_in in H; destruct H; eauto;
    apply emp_star in H; tauto.
  - sep_split_in H;
    [apply pure_emp; [apply emp_star|]..]; eauto.
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
  Bdiv.Aistar_v P s (emp_ph loc) -> P[@i] s (emp_ph loc).
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
  rewrite ls_exists.
  split; intros [vs H]; exists vs; sep_split; sep_split_in H; eauto;
  [erewrite ls_init_eq'; [apply H|];
   intros; simpl in *;
   try rewrite <-!minus_n_O in *; auto..].
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
  conj_xs P s (emp_ph loc) -> (nth i P TrueP) s (emp_ph loc).
Proof.
  induction P; intros; destruct i; simpl in *; unfold TrueP; auto.
  apply emp_star in H; tauto.
  apply IHP; apply emp_star in H; tauto.
Qed.

Lemma ls_emp' (P : list assn) s :
  (forall i, i < length P -> (nth i P TrueP) s (emp_ph loc)) -> conj_xs P s (emp_ph loc).
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
      sep_rewrite_in IHn H1; auto.
    + sep_normal_in H; sep_normal; repeat sep_cancel.
      sep_rewrite_in_r IHn H1; auto.
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

Lemma low_assn_emp G : low_assn G emp.
Proof.
  intros s1 s2 h Hl; split; intros H; exact H.
Qed.

Lemma low_assn_mp G E1 E2 q :
  typing_lexp G E1 Lo ->
  typing_exp G E2 Lo ->
  low_assn G (E1 -->p (q, E2)).
Proof.
  intros H1 H2 s1 s2 h Hl.
  simpl; unfold_conn; split; simpl; intros H.
  erewrite (@low_eq_eq_lexp G E1), (@low_eq_eq_exp G E2); eauto.
  apply low_eq_sym; auto.
  apply low_eq_sym; auto.
  erewrite (@low_eq_eq_lexp G E1), (@low_eq_eq_exp G E2); eauto.
Qed.

Lemma low_assn_star G P Q : 
  low_assn G P -> low_assn G Q ->
  low_assn G (P ** Q).
Proof.
  intros HP HQ; unfold "**"; intros s1 s2 h Hl; simpl.
  specialize (HP s1 s2); specialize (HQ s1 s2); simpl in *.
  split; intros (ph1 & ph2 & H); exists ph1, ph2.
  rewrite HP, HQ in H; [exact H|auto..].
  rewrite HP, HQ; [exact H|auto..].
Qed.

Lemma low_assn_is_array G E n f : forall s,
  typing_lexp G E Lo ->
  CSL.low_assn G (is_array E n f s).
Proof.
  induction n; simpl in *; intros s He.
  - apply low_assn_emp.
  - apply low_assn_star.
    apply low_assn_mp.
    cutrewrite (Lo = join Lo Lo); [|eauto].
    induction E;
      [constructor; repeat constructor; inversion He; subst; eauto..].
    constructor; eauto.
    constructor.
    apply IHn; auto.
Qed.

Lemma low_assn_is_array_p G E n f p : forall s,
  typing_lexp G E Lo ->
  CSL.low_assn G (is_array_p E n f s p).
Proof.
  induction n; simpl in *; intros s He.
  - apply low_assn_emp.
  - apply low_assn_star.
    apply low_assn_mp.
    cutrewrite (Lo = join Lo Lo); [|eauto].
    induction E;
      [constructor; repeat constructor; inversion He; subst; eauto..].
    constructor; eauto.
    constructor.
    apply IHn; auto.
Qed.

Lemma low_assn_ex {T : Type} G (P : T -> assn) :
  (forall x, low_assn G (P x)) ->
  low_assn G (Ex x, P x).
Proof.
  unfold low_assn, indeP.
  intros Hl s1 s2 h Hlow; simpl.
  split; intros [x H]; exists x; simpl in *.
  rewrite Hl.
  exact H.
  apply low_eq_sym; eauto.
  rewrite Hl.
  exact H.
  eauto.
Qed.

Lemma low_assn_pure G P :
  low_assn G (pure P).
Proof.
  intros s1 s2 h Hlow; simpl. unfold Apure; split; auto.
Qed.

Lemma low_assn_ban G P :
  low_assn G P ->
  low_assn G !(P).
Proof.
  intros Hl s1 s2 h Hlow; simpl.
  unfold ban, "//\\"; intros.
  unfold low_assn, indeP in Hl; simpl in Hl.
  rewrite Hl; eauto.
  split; intros H; exact H.
Qed.

Lemma low_assn_eeq E1 E2 G:
  typing_exp G E1 Lo ->
  typing_exp G E2 Lo ->
  low_assn G (E1 === E2).
Proof.
  intros H1 H2; unfold_conn; intros s1 s2 h Hlow; simpl.
  erewrite (@low_eq_eq_exp G E1); eauto.
  erewrite (@low_eq_eq_exp G E2); eauto.
  split; auto.
Qed.

Definition val := Z.

Definition skip_arr (e : loc_exp) st len skip f_ini i :=
  nth i (distribute skip e len f_ini (nt_step skip) st) emp. 

Lemma low_assn_skip_arr G E n skip f_ini i : forall st,
  typing_lexp G E Lo ->
  low_assn G (skip_arr E st n skip f_ini i).
Proof.
  assert (skip = 0 \/ skip <> 0) as [|] by omega.
  - subst; unfold skip_arr; induction n; simpl in *; intros s He.
    destruct i; apply low_assn_emp.
    unfold nt_step; simpl.
    rewrite nth_overflow; [apply low_assn_emp|].
    assert (length (distribute 0 E n f_ini (fun _ : nat => 0) (S s)) = 0).
    { rewrite distribute_length; eauto. }
    lazymatch goal with [|- context [match ?X with _ => _ end]] => destruct X end;
      simpl in *; try omega.
  - unfold skip_arr; induction n; simpl in *; intros s He.
    + rewrite nth_nseq; destruct leb; apply low_assn_emp.
    + assert (i < skip \/ skip <= i) as [|] by omega.
      rewrite nth_add_nth; [|try rewrite distribute_length; unfold nt_step; eauto..].
      destruct beq_nat.
      apply low_assn_star; eauto.
      apply low_assn_mp.
      cutrewrite (Lo = join Lo Lo); [|eauto].
      repeat constructor; eauto.
      constructor.
      eauto.
      rewrite nth_overflow; eauto.
      apply low_assn_emp.
      rewrite add_nth_length, distribute_length; eauto.
Qed.

Ltac prove_low_assn :=
  match goal with
    | [|- low_assn _ (Ex _, _) ] => apply low_assn_ex; intros
    | [|- low_assn _ (_ ** _) ] => apply low_assn_star
    | [|- low_assn _ ( !(_) ) ] => apply low_assn_ban
    | [|- low_assn _ ( _ === _) ] => apply low_assn_eeq
    | [|- low_assn _ (pure _) ] => apply low_assn_pure
    | [|- low_assn _ (if ?X then _ else _) ] => destruct X
    | [|- low_assn _ (is_array _ _ _ _) ] => apply low_assn_is_array
    | [|- low_assn _ (is_array_p _ _ _ _ _) ] => apply low_assn_is_array_p
    | [|- low_assn _ emp ] => apply low_assn_emp
    | [|- low_assn _ (_ -->p (_, _)) ] => apply low_assn_mp
    | [|- low_assn _ (is_array _ _ _ _ _ _) ] => apply low_assn_is_array
    | _ => now (unfold low_assn, indeP; intros; tauto)
  end.

Lemma has_no_vars_emp : has_no_vars emp.
Proof.
  intros s1 s2 h Hl; split; intros H; exact H.
Qed.

Fixpoint has_no_vars_E (e : exp) :=
  match e with
    | Evar _ => False
    | Enum _ => True
    | Emin e1 e2 | Eeq e1 e2 | Elt e1 e2 | (e1 +C e2) | (e1 *C e2) | (e1 -C e2) => has_no_vars_E e1 /\ has_no_vars_E e2
    | (e1 >>1) => has_no_vars_E e1
  end.

Lemma has_no_vars_E_correct (e : exp) s1 s2 :
  has_no_vars_E e ->
  edenot e s1 = edenot e s2.
Proof.
  induction e; simpl; try tauto; 
  try now (destruct 1; intros; erewrite IHe1, IHe2; eauto).
  intros; erewrite IHe; eauto.
Qed.

Fixpoint has_no_vars_lE (e : loc_exp) :=
  match e with
    | Addr _ e => has_no_vars_E e
    | (e1 +o e2) => has_no_vars_lE e1 /\ has_no_vars_E e2
  end.

Lemma has_no_vars_lE_correct (e : loc_exp) s1 s2:
  has_no_vars_lE e ->
  ledenot e s1 = ledenot e s2.
Proof.
  induction e; simpl; intros;
  try f_equal; eauto using has_no_vars_E_correct.
  destruct H as [H1 H2]; erewrite (IHe); eauto.
  destruct (ledenot e s2); do 2 f_equal; eauto using has_no_vars_E_correct.
Qed.

Lemma has_no_vars_mp E1 E2 q :
  has_no_vars_lE E1 ->
  has_no_vars_E E2 ->
  has_no_vars (E1 -->p (q, E2)).
Proof.
  intros H1 H2 s1 s2 h Hl.
  simpl; unfold_conn; split; simpl; intros H;
  erewrite has_no_vars_lE_correct, has_no_vars_E_correct; eauto.
Qed.

Lemma has_no_vars_star P Q : 
  has_no_vars P -> has_no_vars Q ->
  has_no_vars (P ** Q).
Proof.
  intros HP HQ; unfold "**"; intros s1 s2 h Hl; simpl.
  specialize (HP s1 s2); specialize (HQ s1 s2); simpl in *.
  split; intros (ph1 & ph2 & H); exists ph1, ph2.
  rewrite HP, HQ in H; [exact H|auto..].
  rewrite HP, HQ; [exact H|auto..].
Qed.

Lemma has_no_vars_is_array E n f : forall s,
  has_no_vars_lE E ->
  has_no_vars (is_array E n f s).
Proof.
  induction n; simpl in *; intros s He.
  - apply has_no_vars_emp.
  - apply has_no_vars_star.
    apply has_no_vars_mp; simpl; eauto.
    apply IHn; auto.
Qed.

Lemma has_no_vars_is_array_p p E n f : forall s,
  has_no_vars_lE E ->
  has_no_vars (is_array_p E n f s p).
Proof.
  induction n; simpl in *; intros s He.
  - apply has_no_vars_emp.
  - apply has_no_vars_star.
    apply has_no_vars_mp; simpl; eauto.
    apply IHn; auto.
Qed.

Lemma has_no_vars_ex {T : Type} (P : T -> assn) :
  (forall x, has_no_vars (P x)) ->
  has_no_vars (Ex x, P x).
Proof.
  unfold has_no_vars, indeP.
  intros Hl s1 s2 h Hlow; simpl.
  split; intros [x H]; exists x; simpl in *.
  rewrite Hl; eauto.
  apply <-Hl; eauto.
Qed.

Lemma has_no_vars_pure P :
  has_no_vars (pure P).
Proof.
  intros s1 s2 h Hlow; simpl. unfold Apure; split; auto.
Qed.

Lemma has_no_vars_ban P :
  has_no_vars P ->
  has_no_vars !(P).
Proof.
  intros Hl s1 s2 h Hlow; simpl.
  unfold ban, "//\\"; intros.
  unfold has_no_vars, indeP in Hl; simpl in Hl.
  rewrite Hl; eauto.
  split; intros H; exact H.
Qed.

Lemma has_no_vars_eeq E1 E2:
  has_no_vars_E E1 ->
  has_no_vars_E E2 ->
  has_no_vars (E1 === E2).
Proof.
  intros H1 H2; unfold_conn; intros s1 s2 h Hlow; simpl.
  erewrite (@has_no_vars_E_correct E1); eauto.
  erewrite (@has_no_vars_E_correct E2); eauto.
  split; intros H; eauto.
Qed.

Lemma has_no_vars_skip_arr E n skip f_ini i : forall st,
  has_no_vars_lE E ->
  has_no_vars (skip_arr E st n skip f_ini i).
Proof.
  assert (skip = 0 \/ skip <> 0) as [|] by omega.
  - subst; unfold skip_arr; induction n; simpl in *; intros s He.
    destruct i; apply has_no_vars_emp.
    unfold nt_step; simpl.
    rewrite nth_overflow; [apply has_no_vars_emp|].
    assert (length (distribute 0 E n f_ini (fun _ : nat => 0) (S s)) = 0).
    { rewrite distribute_length; eauto. }
    lazymatch goal with [|- context [match ?X with _ => _ end]] => destruct X end;
      simpl in *; try omega.
  - unfold skip_arr; induction n; simpl in *; intros s He.
    + rewrite nth_nseq; destruct leb; apply has_no_vars_emp.
    + assert (i < skip \/ skip <= i) as [|] by omega.
      rewrite nth_add_nth; [|try rewrite distribute_length; unfold nt_step; eauto..].
      destruct beq_nat; eauto.
      apply has_no_vars_star; eauto.
      apply has_no_vars_mp; simpl; eauto.
      rewrite nth_overflow; eauto.
      apply has_no_vars_emp.
      rewrite add_nth_length, distribute_length; eauto.
Qed.

Ltac has_no_vars_assn :=
  match goal with
    | [|- has_no_vars (Ex _, _) ] => apply has_no_vars_ex; intros
    | [|- has_no_vars (_ ** _) ] => apply has_no_vars_star
    | [|- has_no_vars ( !(_) ) ] => apply has_no_vars_ban
    | [|- has_no_vars ( _ === _) ] => apply has_no_vars_eeq
    | [|- has_no_vars (pure _) ] => apply has_no_vars_pure
    | [|- has_no_vars (if ?X then _ else _) ] => destruct X
    | [|- has_no_vars (is_array _ _ _ _) ] => apply has_no_vars_is_array
    | [|- has_no_vars (is_array _ _ _ _ _) ] => apply has_no_vars_is_array_p
    | [|- has_no_vars emp ] => apply has_no_vars_emp
    | [|- has_no_vars (is_array _ _ _ _ _ _) ] => apply has_no_vars_is_array
    | _ => now (unfold has_no_vars, indeP; intros; tauto)
  end.

Lemma mps_precise E1 E2 E2' q st : forall h1 h2 h1' h2' ,
  (E1 -->p (q, E2)) st h1 ->
  (E1 -->p (q, E2')) st h1' ->
  pdisj h1 h2 -> pdisj h1' h2' -> phplus h1 h2 = phplus h1' h2' ->
  h1 = h1'.
Proof.
  intros; unfold_conn_all.
  destruct h1 as [h1 ?], h1' as [h1' ?]; simpl in *.
  apply pheap_eq; extensionality x.
  apply (f_equal (fun f => f x)) in H3; unfold phplus in H3.
  specialize (H1 x); specialize (H2 x).
  rewrite H, H0 in *.
  destruct (eq_dec x (ledenot E1 st)); eauto.
  destruct (h2 x) as [[? ?]|], (h2' x) as [[? ?]|]; try eauto; inversion H3; congruence.
Qed.

Lemma is_array_precise E f f' st n : forall s (h1 h2 h1' h2' : pheap),
  (is_array E n f s) st h1 ->
  (is_array E n f' s) st h1' ->
  pdisj h1 h2 -> pdisj h1' h2' -> phplus h1 h2 = phplus h1' h2' ->
  h1 = h1'.
Proof.
  induction n; simpl; intros.
  - apply emp_emp_ph_eq in H; apply emp_emp_ph_eq in H0; congruence.
  - destruct H as (ph1 & ph2 & ? & ? & ? & ?).
    destruct H0 as (ph1' & ph2' & ? & ? & ? & ?).
    assert (ph1 = ph1').
    { assert (pdisj ph1 (phplus ph2 h2)).
      { apply pdisj_padd_expand; eauto. rewrite H6; eauto. }
      assert (pdisj ph1' (phplus ph2' h2')).
      { apply pdisj_padd_expand; eauto. rewrite H9; eauto. }
      eapply mps_precise; [exact H | exact H0 | exact H10 | exact H11 | ..].
      rewrite <-H6 in H1.
      rewrite <-H9 in H2.
      apply pdisj_padd_expand in H1; eauto.
      apply pdisj_padd_expand in H2; eauto.
      rewrite <-!padd_assoc; try tauto.
      rewrite H9, H6; eauto. }
    cut (PHeap.this h1 = PHeap.this h1').
    { intros; destruct h1, h1'; apply pheap_eq; simpl in *; eauto. }
    rewrite <-H6, <-H9; rewrite H10; repeat f_equal.
    rewrite <-H9, <-H6 in H3.
    rewrite (@phplus_comm _ ph1 ph2) in H3; eauto.
    rewrite (@phplus_comm _ ph1' ph2') in H3; eauto.
    rewrite <-H6, (@phplus_comm _ ph1 ph2) in H1; eauto.
    apply pdisj_padd_expand in H1; eauto.
    rewrite <-H9, (@phplus_comm _ ph1' ph2') in H2; eauto.
    apply pdisj_padd_expand in H2; eauto.
    destruct H1, H2.
    eapply IHn.
    eauto. eauto.
    instantiate (1 := (phplus_pheap H11)); simpl; eauto.
    instantiate (1 := (phplus_pheap H12)); simpl; eauto.
    simpl.
    repeat (rewrite <-padd_assoc; eauto).
Qed.

Ltac sep_destruct_in H :=
  match type of H with
    | ((Ex _, _) _ _) => destruct H as [? H]; sep_destruct_in H
    | _ => sep_split_in H
  end.

Ltac prove_precise :=
  match goal with
    | [|- precise _] =>
      intros h1 h2 h1' h2' s Hsat Hsat' Hdis Hdis' Heq; simpl in *;
      sep_destruct_in Hsat; sep_destruct_in Hsat'; unfold_pures;
      repeat match goal with
        | [ H : s ?X = Zn _, H': s ?X = Zn _ |- _ ] => rewrite H', Nat2Z.inj_iff in H
      end; subst;
      try (match type of Hsat with
        | (if ?X then _ else _) _ _ => destruct X
      end; sep_split_in Hsat; sep_split_in Hsat')
  end.
Hint Resolve is_array_precise precise_emp.
Require Import TLC.LibTactics Psatz.
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

Lemma CSLp_backward (P' P : assn) n E C Q : 
  CSLp n E P C Q -> (P' |= P) -> CSLp n E P' C Q.
Proof.
  unfold CSLp; intros Hcsl Hp; intros.
  forwards: (Hcsl ks h leqks); eauto. 
  unfold sat_k in *.
  destruct low_eq_repr; eauto.
Qed.  

Lemma safe_gl_forward n m E ks h (Q Q' : assn) : 
  @safe_nk n E m ks h Q -> 
  (Q |= Q') ->
  @safe_nk n E m ks h Q'.
Proof.
  revert h ks; induction m; simpl; intros h ks Hsafe Hq; eauto.
  simpl in Hsafe; destructs Hsafe.
  repeat split; auto.
  - intros; unfold sat_k in *.
    forwards [x ?]: H; eauto.
    exists x.
    destruct low_eq_repr; apply Hq; eauto.
  - forwards: H2; jauto.
  - forwards: H2; jauto.
  - intros; forwards: H3; eauto.
    destruct H7 as (ph'' & ? & ? & ?); exists ph''; repeat split; eauto.
Qed.  

Lemma CSLp_forward P n E C (Q Q' : assn) : 
  CSLp n E P C Q -> (Q |= Q') -> CSLp n E P C Q'.
Proof.
  unfold CSLp; intros; applys safe_gl_forward; eauto.
Qed.

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

Lemma low_assn_conj_xs assns E :
  (forall i, i < length assns -> low_assn E (nth i assns emp)) ->
  low_assn E (conj_xs assns) .
Proof.
  induction assns; simpl; intros; repeat prove_low_assn.
  specialize (H 0); apply H; omega.
  apply IHassns; intros i; specialize (H (S i)); intros; apply H; omega.
Qed.

Lemma has_no_vars_conj_xs assns :
  (forall i, i < length assns -> has_no_vars (nth i assns emp)) ->
  has_no_vars (conj_xs assns).
Proof.
  induction assns; simpl; intros; repeat has_no_vars_assn.
  apply (H 0); omega.
  apply IHassns; intros i; specialize (H (S i)); simpl in *.
  intros; apply H; omega.
Qed.


Ltac default T :=
  lazymatch T with
    | nat => constr:(0)
    | Z => constr:(0%Z)
    | ?T1 -> ?T2 => let t := default T2 in constr:(fun _ : T1 => t)
  end.

Ltac ex_elim H :=
  lazymatch type of H with
    | conj_xs (ls_init _ _ (fun _ : nat => Ex _ : ?T, _)) _ _ =>
      let t := default T in
      sep_rewrite_in (@ls_exists0 _ t) H
  end.

Ltac istar_simplify_in H :=
  apply sc_v2l in H; rewrite (vec_to_list_init0 _ emp) in H; erewrite ls_init_eq0 in H;
  [|let i := fresh "i" in
    let Hi := fresh in
    let Hex := fresh in
    let Heq := fresh in
    intros i Hi;
    lazymatch goal with
      [|- match ?X with inleft _ => _ | inright _ => _ end = _] =>
      destruct X as [|Hex] eqn:Heq; [|destruct Hex; omega]
    end;
    rewrite (Fin_nat_inv Heq); reflexivity];
  match goal with _ => idtac end;
  (repeat (let vs := fresh "vs" in
          ex_elim H; destruct H as [vs H]; sep_split_in H));
  (repeat sep_rewrite_in (@ls_star) H);
  (repeat sep_rewrite_in (@ls_pure) H; sep_split_in H).
 

Ltac istar_simplify :=
  apply sc_v2l; rewrite (vec_to_list_init0 _ emp); erewrite ls_init_eq0;
  [|let i := fresh "i" in
    let Hi := fresh in
    let Hex := fresh in
    let Heq := fresh in
    intros i Hi;
    lazymatch goal with
      [|- match ?X with inleft _ => _ | inright _ => _ end = _] =>
      destruct X as [|Hex] eqn:Heq; [|destruct Hex; omega]
    end;
    rewrite (Fin_nat_inv Heq); reflexivity];
  match goal with _ => idtac end.

Ltac rewrite_body lem tac :=
      erewrite ls_init_eq0; [|intros ? ?; rewrite lem; try tac; reflexivity ].
Ltac rewrite_body_in lem tac H :=
  erewrite ls_init_eq0 in H; [|intros ? ?; rewrite lem; try tac; reflexivity ].

Section read_only_lemma.
Require Import QArith.
Definition injZ (n : Z) : Qc := Q2Qc (inject_Z n).
Require Import Qcanon.
Require Import PHeap.
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

Lemma this_inv q H : Qcanon.this {| Qcanon.this := q; canon := H |} = q. auto. Qed.

Require Import Psatz.

Lemma inject_Z_1 : inject_Z 1 = 1%Q. auto. Qed.

Ltac injZ_simplify :=
  unfold injZ in *;
  repeat rewrite Nat2Z.inj_succ in *;
  repeat rewrite <-Z.add_1_r in *;
  repeat rewrite inject_Z_plus in *;
  repeat rewrite inject_Z_1 in *.

Lemma inject_Z_n_ge0 n  : (0 <= inject_Z (Z.of_nat n))%Q.
Proof.
  assert (0 <= Z.of_nat n)%Z.
  { cutrewrite (0 = Z.of_nat 0)%Z; [|auto].
    apply inj_le; omega. }
  cutrewrite (0 = inject_Z 0)%Q; [|auto].
  rewrite <-Zle_Qle; auto.
Qed.

Lemma inject_Z_Sn_gt0 n : (1 <= inject_Z (Z.of_nat (S n)))%Q.
Proof.
  injZ_simplify.
  lets: (>>inject_Z_n_ge0 n).
  lra.
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
    is_array_p e n f s (injZ (Z.of_nat nt) * p) <=>
    conj_xs (ls_init st nt (fun i => is_array_p e n f s p)).
Proof.
  intros Hp0 Hp1 Hnp Hn0; induction nt as [|[|nt]]; intros; try omega.
  - simpl.
    asserts_rewrite (injZ 1 * p = p).
    { apply Qc_is_canon.
      repeat unfold injZ, Q2Qc, "*".
      rewrite !this_inv, !Qred_correct.
      cutrewrite (inject_Z 1 = 1%Q); [|eauto].
      rewrite Qmult_1_l; reflexivity. }
    rewrite emp_unit_r; reflexivity.
  - remember (S nt) as nt'.
    asserts_rewrite (Zn (S nt') = Zn nt' + 1)%Z.
     { rewrite Nat2Z.inj_succ; omega. }
     unfold injZ; rewrite inject_Z_plus; simpl.
     asserts_rewrite (Q2Qc (inject_Z (Zn nt') + inject_Z 1) = injZ (Zn nt') + 1).
     { apply Qc_is_canon.
       unfold injZ, "+", Q2Qc.
       rewrite !this_inv.
       rewrite !Qred_correct.
       reflexivity. }
     rewrite Qcmult_plus_distr_l, Qcmult_1_l; eauto.
     rewrite is_array_p_star, IHnt; [|clear IHnt; subst nt'; unfold injZ in *; injZ_simplify; Qc_to_Q; eauto; pose proof (inject_Z_n_ge0 nt); try lra..].
     split; intros; repeat sep_cancel; eauto.
     sep_cancel; eauto.
     assert (0 <= inject_Z (Zn nt) * this)%Q by (apply Qmult_le_0_compat; lra).
     lra.
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
  unfold Q2Qc in *; apply (f_equal (fun x => Qcanon.this x)) in Hc.
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
  rewrite (@one_div_n nt) at 1; eauto.
  apply is_array_is_array_p_n; eauto;
  unfold injZ; Qc_to_Q; destruct nt; try omega; lets: (inject_Z_Sn_gt0 nt).
  apply Qlt_shift_div_l; lra.
  apply Qle_shift_div_r; try lra.
  lets Heq: Qmult_div_r; unfold Qdiv in Heq; rewrite Heq; lra.
Qed.
Open Scope nat_scope.
Lemma is_array_unfold Arr len' f p : forall s len,
  len' < len ->
  forall stc, 
    stc ||= is_array_p Arr len f s p <=>
        is_array_p Arr len' f s p **
        (Arr +o (Zn (len' + s))%Z -->p (p, f (len' + s))) **
        is_array_p Arr (len - len' - 1) f (S (len' + s)) p.
Proof.
  induction len'; intros s len Hlen stc.
  - destruct len; try omega; simpl.
    rewrite <-minus_n_O, emp_unit_l; reflexivity.
  - destruct len; [inversion Hlen|]; simpl.
    rewrite IHlen'; try omega.
    rewrite <-plus_n_Sm; simpl; rewrite sep_assoc; autorewrite with sep. reflexivity.
Qed.

Lemma skip_arr_forward ix i e f n nt (Hnt0 : nt <> 0) : forall s, 
  ix < n -> (s + ix) mod nt = i ->
  forall stc, stc ||= nth i (distribute nt e n f (nt_step nt) s) emp <=>
                  nth i (distribute nt e ix f (nt_step nt) s) emp **
                  (e +o Enum' (s + ix) -->p (1,  Enum (f (s + ix)))) **
                  nth i (distribute nt e (n - ix - 1) f (nt_step nt) (s + ix + 1)) emp.
Proof.
  intros s Hix0 Hix1 stc.
  revert ix Hix0 s Hix1; induction n; [intros; simpl; try omega|]; intros ix Hix0 s Hix1.
  cutrewrite (S n - ix - 1 = n - ix); [|omega].
  assert (i < nt) by (subst; apply Nat.mod_bound_pos; omega).
  simpl; rewrite nth_add_nth; [|rewrite distribute_length; eauto..].
  destruct (beq_nat _ _) eqn:Heq;
    [rewrite beq_nat_true_iff in Heq | rewrite beq_nat_false_iff in Heq].
  - destruct ix; simpl.
    + rewrite <-plus_n_O, <-minus_n_O.
      cutrewrite (s + 1 = S s); [|omega].
      rewrite nth_nseq; destruct (Compare_dec.leb _ _); rewrite emp_unit_l;
      split; intros; repeat sep_cancel.
    + rewrite nth_add_nth; [|rewrite distribute_length; try omega..].
      rewrite Heq at 2; rewrite <-beq_nat_refl.
      rewrite <-plus_n_Sm in Hix1.
      lets H':(>>IHn ix (S s)); try omega; rewrite H'; clear H'; eauto.
      cutrewrite (S s + ix = s + S ix); [|omega].
      cutrewrite (n - ix - 1 = n - S ix); [|omega].
      rewrite !sep_assoc; reflexivity.
  - destruct ix; simpl.
    + unfold nt_step in *; rewrite <-plus_n_O in *; congruence.
    + rewrite nth_add_nth; [|rewrite distribute_length; try omega; eauto..].
      lets H': (>>beq_nat_false_iff ___); apply H' in Heq; rewrite Heq; clear H'.
      rewrite <-plus_n_Sm in Hix1.
      lets H':(>>IHn ix (S s)); try omega; rewrite H'; clear H'; eauto.
      cutrewrite (S s + ix = s + S ix); [|omega].
      cutrewrite (n - ix - 1 = n - S ix); [|omega].
      rewrite !sep_assoc; reflexivity.
Qed.

End read_only_lemma.
Section tid_lemma.
Close Scope Qc.
Close Scope Q.
Lemma id_lt_nt_gr i j n m : (i < n -> j < m -> i + j * n < m * n)%nat.
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
End tid_lemma.
Hint Resolve id_lt_nt_gr nf_lt Nat.neq_mul_0.

Lemma mod_between n m q r :
  (m <> 0 -> r < m -> q * m + r < n < S q * m + r -> n mod m <> r)%nat.
Proof.
  intros Hm Hrm Hbetween; rewrite (Nat.div_mod n m) in Hbetween; auto.
  intros Heq; rewrite Heq in Hbetween; clear Heq.
  assert (q * m < m * (n / m) < S q * m)%nat by omega.
  assert (q < n / m < S q)%nat by nia.
  omega.
Qed.
