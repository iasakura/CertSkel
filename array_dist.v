Set Implicit Arguments.
Unset Strict Implicit.

Require Import NPeano.
Require Import Arith.
Require Import List.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Require Import Omega.

Lemma seq_add : forall (n1 n2 s : nat), seq s (n1 + n2) = seq s n1 ++ seq (s + n1) n2.
Proof.
  induction n1; intros n2 s; simpl; eauto.
  rewrite <-plus_n_Sm, IHn1; simpl; eauto.
Qed.

Lemma combine_app :
  forall (S T : Type) (s1 s2 : list S) (t1 t2 : list T),
    length s1 = length t1 -> combine (s1 ++ s2) (t1 ++ t2) = combine s1 t1 ++ combine s2 t2.
Proof.
  induction s1; intros s2 t1 t2 Hlen.
  - destruct t1; inversion Hlen; simpl; eauto.
  - destruct t1; inversion Hlen; simpl; rewrite IHs1; eauto.
Qed.

Lemma filter_app : 
  forall (T : Type) (a : T -> bool) (s1 s2 : list T),
    filter a (s1 ++ s2) = filter a s1 ++ filter a s2.
Proof.
  induction s1; simpl; eauto.
  intros s2; rewrite IHs1; destruct (a a0); eauto.
Qed.

Fixpoint mask {T : Type} (m : list bool) (l : list T) :=
  match m with
    | nil => nil
    | b :: m => 
      match l with
        | nil => nil
        | x :: l => if b then x :: mask m l else mask m l
      end
  end.

Lemma filter_mask:
  forall (T : Type) (a : T -> bool) (s : list T),
    filter a s = mask (map a s) s.
Proof.
  induction s; simpl; eauto.
  rewrite IHs; eauto.
Qed.

Fixpoint nseq (T : Type) (n : nat) (d : T) : list T :=
  match n with
    | 0 => nil
    | S n => d :: nseq n d
  end.

Lemma eq_from_nth :
  forall (T : Type) (x : T) (s1 s2 : list T),
    length s1 = length s2 ->
    (forall i : nat, i < length s1 -> nth i s1 x = nth i s2 x) -> s1 = s2.
Proof.
  induction s1; intros [|y s2]; inversion 1; eauto.
  intros Heq; f_equal.
  apply (Heq 0); simpl; omega.
  apply IHs1; eauto.
  intros i H'; pose proof (Heq (S i)); simpl in H0; apply H0; omega.
Qed.

Lemma length_nseq : forall (T : Type) (n : nat) (x : T), length (nseq n x) = n.
Proof.
  intros; induction n; simpl; omega.
Qed.

Lemma nth_map :
  forall (T1 : Type) (x1 : T1) (T2 : Type) (x2 : T2) 
         (f : T1 -> T2) (n : nat) (s : list T1),
    n < length s -> nth n (map f s) x2 = f (nth n s x1).
Proof.
  induction n; intros [|y s]; simpl; eauto; try omega.
  intros. firstorder; omega.
Qed.

Lemma nth_nseq :
  forall (T : Type) (x0 : T) (m : nat) (x : T) (n : nat),
    nth n (nseq m x) x0 = (if leb m n then x0 else x).
Proof.
  induction m; intros; simpl; eauto.
  - destruct n; simpl; eauto.
  - destruct n; eauto.
Qed.

Lemma mask_cat:
  forall (T : Type) (m1 m2 : list bool) (s1 s2 : list T),
    length m1 = length s1 -> mask (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2.
Proof.
  induction m1; intros; destruct s1; simpl in *; try omega; eauto.
  rewrite IHm1; destruct a; simpl; eauto.
Qed.

Lemma mask_false:
  forall (T : Type) (s : list T ) (n : nat), mask (nseq n false) s = nil.
Proof.
  induction s; destruct n; simpl in *; eauto.
Qed.

Lemma skipn_length:
  forall (T : Type) (s : list T) (n0 : nat), length (skipn n0 s) = length s - n0.
Proof.
  induction s; destruct n0; simpl; eauto.
Qed.

Lemma drop_oversize:
  forall (T : Type) (n : nat) (s : list T ), length s <= n -> skipn n s = nil.
Proof.
  induction n; destruct s; simpl; intros; try omega; eauto.
  apply IHn; omega.
Qed.

Lemma nth_skipn:
  forall (n0 : nat) (T : Type) (x0 : T) (s : list T) (i : nat),
    nth i (skipn n0 s) x0 = nth (n0 + i) s x0.
Proof.
  intros.
  rewrite <-(firstn_skipn n0 s) at 2; rewrite app_nth2;
  [|rewrite firstn_length; apply (le_trans _ n0); [apply Min.le_min_l | omega] ].
  rewrite firstn_length.
  assert (n0 <= length s \/ length s < n0) as [H|H] by omega.
  - rewrite Min.min_l; eauto.
    cutrewrite (n0 + i - n0 = i); [|omega]; eauto.
  - rewrite Min.min_r; try omega.
    rewrite drop_oversize; [|omega].
    destruct (n0 + i - length s), i; simpl; eauto.
Qed.

Lemma take_oversize:
  forall (T : Type) (n : nat) (s : list T), length s <= n -> firstn n s = s.
Proof.
  induction n; destruct s; simpl; intros; try omega; eauto.
  rewrite IHn; eauto; omega.
Qed.

Lemma nth_firstn:
  forall (n0 : nat) (T : Type) (x0 : T) (i : nat),
    i < n0 -> forall s : list T, nth i (firstn n0 s) x0 = nth i s x0.
Proof.
  intros; assert (n0 < length s \/ length s <= n0) as [H'|H'] by omega.
  - rewrite <-(firstn_skipn n0 s) at 2; rewrite app_nth1;
    [|rewrite firstn_length, Min.min_l; omega]; eauto.
  - rewrite take_oversize; eauto; omega.
Qed.

Create HintDb len.
Hint Rewrite firstn_length skipn_length seq_length map_length  app_length combine_length length_nseq : len.

Ltac crush_len' crusher :=
  (repeat autorewrite with len in *; simpl in *);
  (repeat match goal with
            | [|- context [min ?X ?Y]] =>
              (rewrite (Min.min_l X Y); [|now crusher]) ||
                                                        (rewrite (Min.min_r X Y); [|now crusher])
          end);
  (repeat match goal with
            | [ H : context [min ?X ?Y] |- _] =>
              (rewrite (Min.min_l X Y) in H; [|now crusher]) ||
                                                             (rewrite (Min.min_r X Y) in H; [|now crusher])
          end).

Ltac crush_len := (repeat crush_len' omega); (first [omega | congruence] || eauto).

Create HintDb nth.
Hint Rewrite nth_firstn nth_skipn seq_nth nth_map combine_nth nth_nseq : nth.
Ltac simpl_nth := repeat (autorewrite with nth in *; simpl in *; crush_len).

Require Import assertion_lemmas.
Require Import assertions.

Definition conj_xs : list assn -> assn := fold_right Astar emp.

Require Import SetoidClass.
Definition equiv_sep (P Q : assn) := (forall s h, P s h <-> Q s h).
Notation "P <=> Q" := (equiv_sep P Q) (at level 87).

Lemma equiv_from_nth :
  forall (x0 : assn) (s1 s2 : list assn),
    length s1 = length s2 ->
    (forall i : nat, i < length s1 -> nth i s1 x0 <=> nth i s2 x0) -> conj_xs s1 <=> conj_xs s2.
Proof.
  intros x0; induction s1; intros s2 Hlen Heq s h; destruct s2; simpl in *; try omega; try tauto.
  assert (a <=> a0) by (apply (Heq 0); omega).
  assert (conj_xs s1 <=> conj_xs s2).
  { apply IHs1; [omega|].
    intros i Hl; apply (Heq (S i)); auto; omega. }
  clear IHs1 Hlen Heq.
  split; apply scRw; intros s' h' H'; specialize (H s' h'); specialize (H0 s' h'); tauto.
Qed.

Require Import SetoidClass.
Instance equiv_sep_equiv : Equivalence equiv_sep.
split; repeat intro; try tauto.
specialize (H s h); tauto.
specialize (H s h); specialize (H0 s h); tauto.
Qed.

Program Instance assn_setoid : Setoid assn :=
  {| equiv := equiv_sep;
     setoid_equiv := equiv_sep_equiv |}.

Instance star_proper : Proper (equiv_sep ==> equiv_sep ==> equiv_sep) Astar.
Proof.
  intros p1 p2 H p3 p4 H' s h.
  split; apply scRw; intros s' h'; firstorder.
Qed.

Lemma sep_assoc (P Q R : assn) : P ** Q ** R <=> (P ** Q) ** R.
Proof.
  split; intros. sep_normal. sep_cancel. sep_normal_in H. sep_cancel.
Qed.  

Lemma conj_xs_app (l1 l2 : list assn) :
  conj_xs (l1 ++ l2) <=> conj_xs l1 ** conj_xs l2.
Proof.
  induction l1; simpl.
  split; intros H; sep_normal; sep_normal_in H; auto.
  rewrite IHl1, sep_assoc; reflexivity.
Qed.

Lemma emp_unit_l (P : assn) : emp ** P <=> P.
Proof.
  split; intros; sep_normal; auto.
  sep_normal_in H; auto.
Qed.

Lemma emp_unit_r (P : assn) : P ** emp <=> P.
Proof.
  split; intros; sep_normal; auto.
  sep_normal_in H; auto.
Qed.

Lemma nseq_emp_emp (n : nat) :
  conj_xs (nseq n emp) <=> emp.
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite emp_unit_l; auto.
Qed.

Lemma map_conj {A : Type} (l : list A) (f g : A -> assn) :
  conj_xs (map (fun x => f x ** g x) l) <=> conj_xs (map f l) ** conj_xs (map g l).
Proof.
  induction l; simpl; auto.
  - rewrite emp_unit_l; reflexivity.
  - rewrite IHl; split; intros H; sep_normal; sep_normal_in H; repeat sep_cancel.
Qed.

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
Fixpoint is_array (e : exp) (n : nat) (f : nat -> Z) (s : nat) :=
  match n with
    | 0 => Aemp
    | S n' => e + Enum (Z.of_nat s) -->p (1%Qc, Enum (f s)) **
                       is_array e n' f (S s)
  end.

Fixpoint distribute (d : nat) (e : exp) (n : nat) (f : nat -> Z) (dist : nat -> nat) (s : nat) :=
  match n with
    | O => nseq d emp
    | S n => add_nth (dist s) (e + Enum (Z.of_nat s) -->p (1%Qc, Enum (f s))) (distribute d e n f dist (S s))
  end.

Open Scope nat_scope.

Lemma conj_xs_add_nth (d : nat) : forall a assns,
                                    (d < length assns) -> conj_xs (add_nth d a assns) <=> a ** conj_xs assns.
Proof.
  induction d; simpl in *; intros a assns Hdas.
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

Lemma distribute_length (d : nat) (e : exp) (n : nat) (f : nat -> Z) (dist : nat -> nat) :
  forall i, length (distribute d e n f dist i) = d.
Proof.
  induction n; simpl; intros.
  - apply length_nseq.
  - rewrite add_nth_length; auto.
Qed.

Notation Enum' n := (Enum (Z.of_nat n)).

Lemma distribute_correct (d : nat) (e : exp) (n : nat) (f : nat -> Z) (dist : nat -> nat) :
  forall s, (forall x, dist x < d) ->
            is_array e n f s <=> conj_xs (distribute d e n f dist s).
Proof.
  induction n; intros s Hdist; simpl.
  - rewrite nseq_emp_emp; reflexivity.
  - rewrite conj_xs_add_nth, IHn; [reflexivity| auto| rewrite distribute_length;auto ].
Qed.

Definition nt_step (nt n : nat) := n mod nt.

Definition nt_dist_nth (i : nat) e n f nt (s : nat) :=
  nth i (distribute nt e n f (nt_step nt)s ) emp.

Definition skip_array_body (e : exp) (nt : nat) (f : nat -> exp) (Hnt0 : nt <> 0) :
  forall x, (forall y, y < x -> nat -> assn) -> nat -> assn.
  refine (fun rest rec x =>
            match ltb 0 (rest - x) as b return ltb 0 (rest - x) = b -> assn with 
              | true => fun Heq => (e + Enum' x -->p (1%Qc, f x)) ** rec (rest - nt) _ (x + nt)
              | false => fun _ => emp
            end eq_refl); abstract (apply ltb_lt in Heq; omega).
Defined.

Definition skip_array nt e f (Hnt0 : nt <> 0) : nat -> nat -> assn :=
  Fix lt_wf (fun _ => nat -> assn) (skip_array_body e f Hnt0).

Lemma three_neq_0 : 3 <> 0. auto. Defined.
Goal skip_array (Enum 0) (fun i => Enum' i) three_neq_0 10 3 = 
((Enum 0 + Enum' 0 -->p (1%Qc, Enum' 0)) **
                                         (Enum 0 + Enum' 2 -->p (1%Qc, Enum' 2))).
Proof.
  unfold skip_array, Fix, skip_array_body. simpl.
Abort.

Hint Unfold nt_step.
Hint Resolve Nat.mod_upper_bound.

Lemma leb_le_false: forall n m : nat, (n <=? m) = false <-> m < n.
Proof.
  split; intros.
  assert (~ n <= m) by (intros Hc; apply leb_le in Hc; congruence); omega.
  assert (~(n <=? m = true)) by (intros Hc; apply leb_le in Hc; omega); destruct (_ <=? _); congruence.
Qed.

Lemma ltb_lt_false: forall n m : nat, (n <? m) = false <-> m <= n.
Proof.
  split; intros.
  assert (~ n < m) by (intros Hc; apply ltb_lt in Hc; congruence); omega.
  assert (~(n <? m = true)) by (intros Hc; apply ltb_lt in Hc; omega); destruct (_ <? _); congruence.
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
  nth i (distribute nt e n f dist s) emp <=> 
    (e + Enum' (s + next) -->p (1%Qc, Enum (f (s + next)))) **
    nth i (distribute nt e (n - S next) f dist (S (s + next))) emp.
Proof.
  induction next; intros s n Hint Hdistnt Hdnx Hnxn Hltnx.
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
  nth i (distribute nt e n f dist s) emp <=> 
  nth i (distribute nt e (n - next) f dist (s + next)) emp.
Proof.
  induction next; intros s n Hint Hdist Hndist.
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
  nth i (distribute nt e n f (nt_step nt) 0) emp <=>
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
  nth i (distribute nt e n f (nt_step nt) (s * nt + i)) emp <=>
   ((e + Enum' (s * nt + i) -->p (1,  Enum (f (s * nt + i)))) **
    nth i (distribute nt e (n - nt) f (nt_step nt) (S s * nt + i)) emp).
Proof.
  intros s Hint Hn0.
  etransitivity.
  { apply nth_dist_next with (next := 0); auto.
    - unfold nt_step.
      rewrite <-plus_n_O, plus_comm, Nat.mod_add; [rewrite Nat.mod_small; auto| auto].
    - intros; omega. }
  rewrite <-plus_n_O.
  match goal with [|- _ ** ?X <=> _ ** ?Y] => assert (H : X <=> Y); [|rewrite H; reflexivity] end.
  etransitivity; [apply nth_dist_nil with (next := nt - 1); auto|].
  { intros j Hjnt; unfold nt_step.
    rewrite plus_Snm_nSm, <-plus_assoc, plus_comm, Nat.mod_add; auto.
    intros Hc.
    pose proof (div_mod (i + S j) nt Hnt0) as Heq; rewrite Hc in Heq.
    assert (S j = nt * ((i + S j) / nt)) by omega.
    destruct ((i + S j ) / nt) as [|n']; rewrite mult_comm in H; simpl in H; try omega.
    destruct (n' * nt) as [|n'']; omega. }
  cutrewrite (n - 1 - (nt - 1) = n - nt); [|omega].
  simpl; generalize (s * nt); intros n0.
  cutrewrite (S (n0 + i + (nt - 1)) = nt + n0 + i); [|omega].
  reflexivity.
Qed.

Lemma distribute_snoc i e f nt (Hnt : nt <> 0) dist : forall n s,
  i < nt ->
  (forall i, dist i < nt) ->
  nth i (distribute nt e (S n) f dist s) emp <=>
  nth i (add_nth (dist (s + n)) (e + Enum' (s + n) -->p (1%Qc, Enum (f (s + n))))
           (distribute nt e n f dist s)) emp.
Proof.
  induction n; intros s Hit Hdist; [simpl|].
  - rewrite !nth_add_nth; [| rewrite length_nseq || rewrite distribute_length..]; auto.
    simpl_nth; destruct (leb _ _); rewrite <-!plus_n_O; destruct (beq_nat _ _); reflexivity.
  - remember (S n) as Sn.
    simpl; rewrite nth_add_nth; [|rewrite distribute_length; auto..].
    destruct (beq_nat i (dist s)) eqn:His.
    + rewrite IHn; auto.
      cutrewrite (S s + n = s + Sn); [|omega]; rewrite !nth_add_nth; [|rewrite distribute_length; auto..].
      destruct (beq_nat i (dist (s + Sn))); rewrite HeqSn; simpl.
      * rewrite nth_add_nth; [|rewrite distribute_length; auto..]; rewrite His.
        split; intros H; repeat sep_cancel.
      * rewrite nth_add_nth; [|rewrite distribute_length; auto..]; rewrite His.
        split; intros H; repeat sep_cancel.
    + rewrite IHn; auto.
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
  nth i (distribute nt e n f dist s) emp ** 
  (e + Enum' (s + n + next) -->p (1%Qc, Enum (f (s + n + next))))
  <=> nth i (distribute nt e (S (n + next)) f dist s) emp.
Proof.
  induction next; intros n s Hint Hdist Hdisti Hj.
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