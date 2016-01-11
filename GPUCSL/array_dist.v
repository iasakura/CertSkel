Set Implicit Arguments.
Unset Strict Implicit.

Require Import NPeano.
Require Import Arith.
Require Import List MyList.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Require Import Omega.

Require Import assertion_lemmas.
Require Import assertions.

Fixpoint add_nth (n : nat) (t : assn) (xss : list assn) :=
  match xss with
    | [] => []
    | xs :: xss => 
      match n with
        | 0 => (t ** xs) :: xss
        | S n => xs :: add_nth n t xss
      end
  end.

Require Import Lang.
Require Import Qcanon.

Notation "le +o e" := (loc_offset le e) (at level 50, left associativity).

Fixpoint is_array (e : loc_exp) (n : nat) (f : nat -> Z) (s : nat) :=
  match n with
    | 0 => Aemp
    | S n' => e +o Enum (Z.of_nat s) -->p (1%Qc, Enum (f s)) **
                       is_array e n' f (S s)
  end.

Fixpoint distribute (d : nat) (e : loc_exp) (n : nat) (f : nat -> Z) (dist : nat -> nat) (s : nat) :=
  match n with
    | O => nseq d emp
    | S n => add_nth (dist s) (e +o Enum (Z.of_nat s) -->p (1%Qc, Enum (f s))) (distribute d e n f dist (S s))
  end.

Open Scope nat_scope.

Lemma conj_xs_add_nth (d : nat) : forall a assns,
  (d < length assns) -> forall s, s ||= conj_xs (add_nth d a assns) <=> a ** conj_xs assns.
Proof.
  induction d; simpl in *; intros a assns Hdas s.
  - destruct assns; simpl in *; [omega|].
    rewrite sep_assoc; reflexivity.
  - destruct assns as [|a' assns]; simpl in *; [omega|].
    rewrite IHd; [|omega].
    split; intros; repeat sep_cancel.
Qed.

Lemma add_nth_length n t : forall xs,
  length (add_nth n t xs) = length xs.
Proof.
  induction n; destruct xs; simpl in *; try omega.
  rewrite IHn; omega.
Qed.

Lemma distribute_length (d : nat) (e : loc_exp) (n : nat) (f : nat -> Z) (dist : nat -> nat) :
  forall i, length (distribute d e n f dist i) = d.
Proof.
  induction n; simpl; intros.
  - apply length_nseq.
  - rewrite add_nth_length; auto.
Qed.

Notation Enum' x := (Enum (Z.of_nat x)).

Lemma distribute_correct (d : nat) (e : loc_exp) (n : nat) (f : nat -> Z) (dist : nat -> nat) :
  forall s, (forall x, dist x < d) ->
  forall st, st ||= is_array e n f s <=> conj_xs (distribute d e n f dist s).
Proof.
  induction n; intros s Hdist; simpl; intros.
  - rewrite nseq_emp_emp; reflexivity.
  - rewrite conj_xs_add_nth, IHn; [reflexivity| auto| rewrite distribute_length;auto ].
Qed.

Definition nt_step (nt n : nat) := n mod nt.

Definition nt_dist_nth (i : nat) e n f nt (s : nat) :=
  nth i (distribute nt e n f (nt_step nt)s ) emp.

Definition skip_array_body (e : loc_exp) (nt : nat) (f : nat -> exp) (Hnt0 : nt <> 0) :
  forall x, (forall y, y < x -> nat -> assn) -> nat -> assn.
  refine (fun rest rec x =>
            match 0 <? (rest - x) as b return 0 <? (rest - x) = b -> assn with 
              | true => fun Heq => (e +o Enum' x -->p (1%Qc, f x)) ** rec (rest - nt) _ (x + nt)
              | false => fun _ => emp
            end eq_refl); abstract (apply Nat.ltb_lt in Heq; omega).
Defined.

Definition skip_array nt e f (Hnt0 : nt <> 0) : nat -> nat -> assn :=
  Fix lt_wf (fun _ => nat -> assn) (skip_array_body e f Hnt0).

Lemma three_neq_0 : 3 <> 0. auto. Defined.
Goal skip_array (Sh (Enum 0)) (fun i => Enum' i) three_neq_0 10 3 = 
((Sh (Enum 0) +o Enum' 0 -->p (1%Qc, Enum' 0)) **
 (Sh (Enum 0) +o Enum' 2 -->p (1%Qc, Enum' 2))).
Proof.
  unfold skip_array, Fix, skip_array_body. simpl.
Abort.

Hint Unfold nt_step.
Hint Resolve Nat.mod_upper_bound.

Lemma leb_le_false: forall n m : nat, (n <=? m) = false <-> m < n.
Proof.
  split; intros.
  assert (~ n <= m) by (intros Hc; apply Nat.leb_le in Hc; congruence); omega.
  assert (~(n <=? m = true)) by (intros Hc; apply Nat.leb_le in Hc; omega); destruct (_ <=? _); congruence.
Qed.

Lemma ltb_lt_false: forall n m : nat, (n <? m) = false <-> m <= n.
Proof.
  split; intros.
  assert (~ n < m) by (intros Hc; apply Nat.ltb_lt in Hc; congruence); omega.
  assert (~(n <? m = true)) by (intros Hc; apply Nat.ltb_lt in Hc; omega); destruct (_ <? _); congruence.
Qed.

Lemma nth_add_nth (i j : nat) (a : assn) (l : list assn) (d : assn) :
  i < length l -> j < length l ->
  nth i (add_nth j a l) d = if beq_nat i j then a ** nth i l d else nth i l d.
Proof.
  revert i l; induction j; intros i l; destruct l, i; simpl in *; eauto; try omega.
  intros; apply IHj; omega.
Qed.

Lemma nth_dist_next i e f nt (Hnt0 : nt <> 0) dist : forall next s n,
  i < nt ->
  (forall i, dist i < nt) ->
  dist (s + next) = i -> next < n ->
  (forall j, j < next -> dist (s + j) <> i) ->
  forall st, st ||= nth i (distribute nt e n f dist s) emp <=> 
              (e +o Enum' (s + next) -->p (1%Qc, Enum (f (s + next)))) **
              nth i (distribute nt e (n - S next) f dist (S (s + next))) emp.
Proof.
  induction next; intros s n Hint Hdistnt Hdnx Hnxn Hltnx stc.
  - destruct n; [omega|].
    rewrite <-plus_n_O in Hdnx.
    simpl; rewrite nth_add_nth; [|rewrite distribute_length; omega..].
    subst. rewrite <-beq_nat_refl.
    rewrite <-plus_n_O, <-minus_n_O; reflexivity.
  - destruct n; [omega|]; simpl.
    rewrite nth_add_nth; [|rewrite distribute_length; auto..].
    assert (Heq : beq_nat i (dist s) = false); [| rewrite Heq; clear Heq].
    { specialize (Hltnx 0); rewrite <-plus_n_O in Hltnx.
      apply Nat.eqb_neq; intros Hc; rewrite Hc in Hltnx; apply Hltnx; auto; omega. }
    assert (Heq : s + S next = S s + next) by omega; rewrite Heq in *; clear Heq.
    rewrite IHnext; auto; [reflexivity|..].
    + omega.
    + intros j Hj.
      assert (S j < S next) by omega.
      cutrewrite (S s + j = s + S j); [|omega].
      apply Hltnx; auto.
Qed.

Lemma nth_dist_nil i e f nt (Hnt0 : nt <> 0) dist : forall next s n,
  i < nt ->
  (forall i, dist i < nt) ->
  (forall j, j < next -> dist (s + j) <> i) ->
  forall stc, stc ||= nth i (distribute nt e n f dist s) emp <=> 
  nth i (distribute nt e (n - next) f dist (s + next)) emp.
Proof.
  induction next; intros s n Hint Hdist Hndist stc.
  - rewrite <-minus_n_O, <-plus_n_O; reflexivity.
  - destruct n; simpl; [reflexivity|].
    rewrite nth_add_nth; [|rewrite distribute_length; auto..].
    assert (Heq : beq_nat i (dist s) = false); [|rewrite Heq; clear Heq].
    { apply Nat.eqb_neq; intros Hc; rewrite Hc in Hndist.
      apply (Hndist 0); [omega|f_equal; omega]. }
    rewrite IHnext; [rewrite <-plus_n_Sm; reflexivity|auto..].
    intros j Hj.
    cutrewrite (S s + j = s + S j); [|omega]; apply Hndist; omega.
Qed.

Lemma nt_step_ok (nt : nat) (Hnt0 : nt <> 0) : forall n, nt_step nt n < nt.
Proof.
  intros; apply Nat.mod_upper_bound; auto.
Qed.

Lemma skip_arr_init i e f n nt (Hnt0 : nt <> 0) :
  i < nt ->
  forall stc, stc ||= nth i (distribute nt e n f (nt_step nt) 0) emp <=>
                  nth i (distribute nt e (n - i) f (nt_step nt) i) emp.
Proof.
  intros Hint; cutrewrite (i = 0 + i); [|auto]; apply nth_dist_nil; auto.
  - intros; apply nt_step_ok; auto.
  - intros j Hji; unfold nt_step; simpl.
    rewrite Nat.mod_small; omega.
Qed.

Hint Resolve nt_step_ok.

Lemma skip_arr_unfold i e f n nt (Hnt0 : nt <> 0) : forall s, 
  i < nt -> 0 < n ->
  forall stc, stc ||= nth i (distribute nt e n f (nt_step nt) (s * nt + i)) emp <=>
                  ((e +o Enum' (s * nt + i) -->p (1,  Enum (f (s * nt + i)))) **
                   nth i (distribute nt e (n - nt) f (nt_step nt) (S s * nt + i)) emp).
Proof.
  intros s Hint Hn0 stc.
  etransitivity.
  { apply nth_dist_next with (next := 0); auto.
    - unfold nt_step.
      rewrite <-plus_n_O, plus_comm, Nat.mod_add; [rewrite Nat.mod_small; auto| auto].
    - intros; omega. }
  rewrite <-plus_n_O.
  match goal with [|- ?stc ||= _ ** ?X <=> _ ** ?Y] => assert (H : stc ||= X <=> Y); [|rewrite H; reflexivity] end.
  etransitivity; [apply nth_dist_nil with (next := nt - 1); auto|].
  { intros j Hjnt; unfold nt_step.
    rewrite plus_Snm_nSm, <-plus_assoc, plus_comm, Nat.mod_add; auto.
    intros Hc.
    pose proof (Nat.div_mod (i + S j) nt Hnt0) as Heq; rewrite Hc in Heq.
    assert (S j = nt * ((i + S j) / nt)) by omega.
    destruct ((i + S j ) / nt) as [|n']; rewrite mult_comm in H; simpl in H; try omega.
    destruct (n' * nt) as [|n'']; omega. }
  cutrewrite (n - 1 - (nt - 1) = n - nt); [|omega].
  simpl; generalize (s * nt); intros n0.
  cutrewrite (S (n0 + i + (nt - 1)) = nt + n0 + i); [|omega].
  reflexivity.
Qed.

Lemma skip_arr_unfold' i e f n nt (Hnt0 : nt <> 0) : forall s, 
  i < nt -> i < n ->
  forall stc, stc ||= nth i (distribute nt e n f (nt_step nt) (s * nt)) emp <=>
   ((e +o Enum' (s * nt + i) -->p (1,  Enum (f (s * nt + i)))) **
    nth i (distribute nt e (n - nt) f (nt_step nt) (S s * nt)) emp).
Proof.
  intros s Hint Hn0.
  etransitivity.
  { apply nth_dist_next with (next := i); auto.
    - unfold nt_step.
      rewrite <-plus_comm, Nat.mod_add; [rewrite Nat.mod_small; auto| auto]. 
    - intros j Hji; unfold nt_step.
      rewrite <-plus_comm, Nat.mod_add; [rewrite Nat.mod_small; omega| auto]. }
  match goal with [|- ?stc ||= _ ** ?X <=> _ ** ?Y] => assert (H : stc ||= X <=> Y); [|rewrite H; reflexivity] end.
  etransitivity; [apply nth_dist_nil with (next := nt - S i); auto|].
  { intros j Hjnt; unfold nt_step.
    rewrite plus_Snm_nSm, <-plus_assoc, plus_comm, Nat.mod_add; auto.
    intros Hc.
    pose proof (Nat.div_mod (i + S j) nt Hnt0) as Heq; rewrite Hc in Heq.
    assert (S j = nt * ((i + S j) / nt)) by omega.
    destruct ((i + S j ) / nt) as [|n']; rewrite mult_comm in H; simpl in H; try omega.
    destruct (n' * nt) as [|n'']; omega. }
  cutrewrite (n - S i - (nt - S i) = n - nt); [|omega].
  simpl; generalize (s * nt); intros n0.
  cutrewrite (S (n0 + i + (nt - S i)) = nt + n0); [|omega].
  reflexivity.
Qed.

Lemma distribute_snoc i e f nt (Hnt : nt <> 0) dist : forall n s,
  i < nt ->
  (forall i, dist i < nt) ->
  forall stc, stc ||= nth i (distribute nt e (S n) f dist s) emp <=>
  nth i (add_nth (dist (s + n)) (e +o Enum' (s + n) -->p (1%Qc, Enum (f (s + n))))
           (distribute nt e n f dist s)) emp.
Proof.
  induction n; intros s Hit Hdist; [simpl|].
  - rewrite !nth_add_nth; [| rewrite length_nseq || rewrite distribute_length..]; auto.
    simpl_nth; destruct (leb _ _); rewrite <-!plus_n_O; destruct (beq_nat _ _); reflexivity.
  - remember (S n) as Sn.
    simpl; rewrite nth_add_nth; [|rewrite distribute_length; auto..].
    destruct (beq_nat i (dist s)) eqn:His.
    + intros; rewrite IHn; auto.
      cutrewrite (S s + n = s + Sn); [|omega]; rewrite !nth_add_nth; [|rewrite distribute_length; auto..].
      destruct (beq_nat i (dist (s + Sn))); rewrite HeqSn; simpl.
      * rewrite nth_add_nth; [|rewrite distribute_length; auto..]; rewrite His.
        split; intros H; repeat sep_cancel.
      * rewrite nth_add_nth; [|rewrite distribute_length; auto..]; rewrite His.
        split; intros H; repeat sep_cancel.
    + intros; rewrite IHn; auto.
      cutrewrite (S s + n = s + Sn); [|omega]; rewrite !nth_add_nth; [|rewrite distribute_length; auto..].
      destruct (beq_nat i (dist (s +Sn))) eqn:Hisn.
      * rewrite HeqSn; simpl; rewrite nth_add_nth; [|rewrite distribute_length; auto..].
        rewrite His; split; intros; sep_cancel.
      * rewrite HeqSn; simpl; rewrite nth_add_nth; [|rewrite distribute_length; auto..].
        rewrite His; split; intros; sep_cancel.
Qed.

Hint Extern 1 (_ <  length (distribute _ _ _ _ _ _) ) =>
  rewrite distribute_length; auto.

Lemma nth_dist_snoc i e f nt (Hnt0 : nt <> 0) dist : forall next n s,
  i < nt ->
  (forall i, dist i < nt) ->
  dist (s + n + next) = i -> 
  (forall j, j < next -> dist (s + n + j) <> i) ->
  forall stc, stc ||= 
  nth i (distribute nt e n f dist s) emp ** 
  (e +o Enum' (s + n + next) -->p (1%Qc, Enum (f (s + n + next))))
  <=> nth i (distribute nt e (S (n + next)) f dist s) emp.
Proof.
  induction next; intros n s Hint Hdist Hdisti Hj stc.
  - rewrite <-!plus_n_O in *.
    rewrite distribute_snoc; auto; rewrite nth_add_nth; auto.
    symmetry in Hdisti; rewrite (proj2 (beq_nat_true_iff _ _) Hdisti).
    split; intros; repeat sep_cancel.
  - cutrewrite (S (n + S next) = S (S n + next)); [|omega].
    rewrite <-IHnext; auto.
    + cutrewrite (s + S n + next = s + n + S next); [|omega].
      rewrite distribute_snoc; auto; rewrite nth_add_nth; auto.
      assert (H : beq_nat i (dist (s + n)) = false); [|rewrite H; clear H].
      { apply Nat.eqb_neq; intros Hc.
        apply (Hj 0); [omega| rewrite <-plus_n_O; auto]. }
      split; intros; repeat sep_cancel.
    + cutrewrite (s + S n + next = s + n + S next); [|omega]; auto.
    + intros j Hjnext.
      cutrewrite (s + S n + j = s + n + S j); [|omega]; apply Hj; omega.
Qed.

Lemma nth_dist_ext' i e f nt (Hnt0 : nt <> 0) dist : forall n s,
  i < nt ->
  (forall i, dist i < nt) ->
  dist (s + n) <> i ->
  forall stc, 
  stc ||= nth i (distribute nt e n f dist s) emp <=> 
      nth i (distribute nt e (S n) f dist s) emp.
Proof.
  induction n; intros s Hint Hdisi Hdisneq stc.
  - simpl; rewrite nth_add_nth; simpl_nth.
    rewrite <-plus_n_O in Hdisneq.
    rewrite (proj2 (Nat.eqb_neq i (dist s))); auto; reflexivity.
  - remember (S (S n)) as n'; simpl; rewrite nth_add_nth; auto.
    assert (dist (S s + n) <> i) by (rewrite <-plus_n_Sm in Hdisneq; simpl; auto).
    destruct (beq_nat i (dist s)) eqn:His; rewrite IHn; auto;
    subst; remember (S n); simpl; rewrite nth_add_nth; auto; rewrite His; reflexivity.
Qed.    

Lemma nth_dist_ext i e f nt (Hnt0 : nt <> 0) dist : forall next s n,
  i < nt ->
  (forall i, dist i < nt) ->
  (forall j, j < next -> dist (s + n + j) <> i) ->
  forall stc, stc ||=
  nth i (distribute nt e n f dist s) emp <=> 
  nth i (distribute nt e (n + next) f dist s) emp.
Proof.
  induction next; intros s n Hint Hdist Hdisti stc.
  - rewrite <-plus_n_O; reflexivity.
  - rewrite <-plus_n_Sm; simpl.
    rewrite nth_add_nth; auto.
    destruct (beq_nat _ _) eqn:Heq.
    + apply Nat.eqb_eq in Heq.
      rewrite <-IHnext; auto.
      destruct n.
      { contradict Heq; intros Hc; apply (Hdisti 0); [omega| rewrite <-!plus_n_O; auto]. }
      remember (S n) eqn:Heq'; rewrite Heq' at 1; simpl; rewrite nth_add_nth; auto.
      rewrite Heq, <-beq_nat_refl; subst.
      rewrite <-nth_dist_ext' with (s := (S s)); [reflexivity|auto..].
      cutrewrite (S s + n = s + S n + 0); [|omega]; apply Hdisti; omega.
      intros j Hj; cutrewrite (S s + n + j = s + n + S j); [|omega]; apply Hdisti; omega.
    + rewrite <-IHnext; auto.
      destruct n; [simpl; reflexivity|].
      remember (S n) eqn:Heq'; rewrite Heq' at 1; simpl; rewrite nth_add_nth; auto; rewrite Heq.
      subst; rewrite <-nth_dist_ext'; [reflexivity|auto..].
      cutrewrite (S s + n = s + S n + 0); [|omega]; apply Hdisti; omega.
      intros j Hj; cutrewrite (S s + n + j = s + n + S j); [|omega]; apply Hdisti; omega.
Qed.

Lemma skip_arr_fold i e f n nt (Hnt0 : nt <> 0) : forall s, 
  i < nt -> 0 < n ->
  forall stc, stc ||=
  nth i (distribute nt e (s * nt + i) f (nt_step nt) 0) emp **
   (e +o Enum' (s * nt + i) -->p (1,  Enum (f (s * nt + i)))) <=>
    nth i (distribute nt e (S s * nt + i) f (nt_step nt) 0) emp.
Proof.
  intros s Hint Hn0 stc.
  assert (Heq : s * nt + i = 0 + (s * nt + i) + 0) by omega.
  rewrite Heq at 2; rewrite Heq at 3.
  rewrite nth_dist_snoc; auto.
  rewrite nth_dist_ext with (next := nt - 1); auto.
  cutrewrite (S (s * nt + i + 0) + (nt - 1) = S s * nt + i); [|simpl; omega]; reflexivity.
  intros j Hj; unfold nt_step.
  - cutrewrite (0 + S (s * nt + i + 0) + j = (S (i + j)) + s * nt); [|omega].
    rewrite Nat.mod_add; auto.
    intros Heqij. pose proof (Nat.div_mod (S (i + j)) nt Hnt0) as H'; rewrite Heqij in H'.
    assert (S j = nt * (S (i + j) / nt)) by omega.
    destruct (S (i + j) / nt); simpl in *; [omega|].
    rewrite mult_comm in H; simpl in *; destruct (n0 * nt); omega.
  - simpl; rewrite <-!plus_n_O; unfold nt_step.
    rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto.
  - inversion 1.
Qed.

Lemma skip_arr_fold' i e f nt (Hnt0 : nt <> 0) : forall s, 
  i < nt -> 
  forall stc, stc ||=
  nth i (distribute nt e (s * nt) f (nt_step nt) 0) emp **
   (e +o Enum' (s * nt + i) -->p (1,  Enum (f (s * nt + i)))) <=>
    nth i (distribute nt e (S s * nt) f (nt_step nt) 0) emp.
Proof.
  intros s Hint stc.
  cutrewrite (s * nt + i = 0 + s * nt + i); [|omega].
  rewrite nth_dist_snoc; try omega; eauto.
  rewrite nth_dist_ext with (next := (nt - S i)); try omega; eauto.
  cutrewrite (S (s * nt + i) + (nt - S i) = S s * nt); [|simpl; omega]; reflexivity.
  intros; simpl; unfold nt_step.
  cutrewrite (S (s * nt + i + j) = (S (i + j) + s * nt));
    [rewrite Nat.mod_add, Nat.mod_small; omega|omega].
  unfold nt_step.
  cutrewrite (0 + s * nt + i = i + s * nt); [rewrite Nat.mod_add, Nat.mod_small; omega|omega].
  intros j Hji; simpl; unfold nt_step; rewrite plus_comm, Nat.mod_add, Nat.mod_small; omega.
Qed.  

Lemma nth_dist_change i e f1 f2 nt (Hnt0 : nt <> 0) dist : forall n s,
  i < nt ->
  (forall i, dist i < nt) ->
  (forall j, j < n -> dist (j + s) = i -> f1 (j + s) = f2 (j + s)) ->
  forall stc, stc ||=
  nth i (distribute nt e n f1 dist s) emp <=> 
  nth i (distribute nt e n f2 dist s) emp.
Proof.
  induction n; intros s Hint Hdist Hf stc; simpl; [reflexivity|].
  rewrite !nth_add_nth; auto.
  destruct (beq_nat i (dist s)) eqn:Heq.
  - apply Nat.eqb_eq in Heq.
    pose (Hf 0) as Hf0; simpl in Hf0; rewrite Hf0; [|omega|auto].
    rewrite IHn; auto; [reflexivity|].
    intros j ?; rewrite <-plus_n_Sm; simpl; apply (Hf (S j)); omega.
  - apply IHn; auto.
    intros j ?; rewrite <-plus_n_Sm; simpl; apply (Hf (S j)); omega.
Qed.

Require Import TLC.LibTactics.
Require Import Psatz.

Lemma skip_arr_nth nt f e i tid :
  forall n st,
  0 < nt -> tid < nt ->
  nt * i + tid < n ->
  forall stc, stc ||=
    nth tid (distribute nt e n f (nt_step nt) (st * nt)) emp <=>
    nth tid (distribute nt e (nt * i) f (nt_step nt) (st * nt)) emp **
    (e +o Enum' ((st + i) * nt + tid) -->p (1, Enum (f ((st + i) * nt + tid)))) **
    nth tid (distribute nt e (n - nt * S i) f (nt_step nt) (nt * S (st + i))) emp.
Proof.
  induction i; intros n st Hnt Htidnt Hlt stc.
  - rewrite mult_0_r; simpl.
    rewrite skip_arr_unfold'; try nia.
    simpl.
    rewrite mult_1_r, <-plus_n_O, mult_succ_r.
    cutrewrite (nt * st + nt = nt + st * nt); [|ring].
    rewrite nth_nseq; destruct leb; split; intros H; sep_normal; sep_normal_in H; repeat sep_cancel.
  - assert (tid < n) by nia.
    rewrite skip_arr_unfold'; try omega.
    assert (tid < nt * S i) by nia.
    rewrite (@skip_arr_unfold' tid e _ (nt * S i)); try omega.
    assert ( nt * i + tid < n - nt) by nia.
    rewrite IHi; try omega.
    cutrewrite (nt * S i - nt = nt * i); [|nia].
    cutrewrite (n - nt * S (S i) = n - nt - nt * S i); [|nia].
    cutrewrite (st + S i = S st + i); [|nia].
    split; intros H'; sep_normal; sep_normal_in H'; sep_cancel.
Qed.

Lemma skip_arr_nth' i nt f e tid :
  forall n,
  0 < nt -> tid < nt ->
  nt * i + tid < n ->
  forall stc, stc ||=
    nth tid (distribute nt e n f (nt_step nt) 0) emp <=>
    nth tid (distribute nt e (nt * i) f (nt_step nt) 0) emp **
    (e +o Enum' (i * nt + tid) -->p (1, Enum (f (i * nt + tid)))) **
    nth tid (distribute nt e (n - nt * S i) f (nt_step nt) (nt * S i)) emp.
Proof.
  intros.
  lets H': (>>skip_arr_nth nt f e i tid n 0).
  simpl in H'; apply H'; try omega.
Qed.

Fixpoint is_array_p e len (f : nat -> Z) s p :=
  match len with
    | O => emp
    | S len' => (e +o Enum (Z.of_nat s) -->p (p, Enum (f s))) ** is_array_p e len' f (S s) p
  end.
