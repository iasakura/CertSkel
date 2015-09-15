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
Require Import Lang.
Definition equiv_sep (s : stack) (P Q : assn) := (forall h, P s h <-> Q s h).
Notation "s ||= P <=> Q" := (equiv_sep s P Q) (at level 86, next at level 87).

Lemma equiv_from_nth :
  forall (x0 : assn) (s1 s2 : list assn),
    length s1 = length s2 ->
    (forall i : nat, i < length s1 -> forall s, s ||= nth i s1 x0 <=> nth i s2 x0) ->
    forall s, s ||= conj_xs s1 <=> conj_xs s2.
Proof.
  intros x0; induction s1; intros s2 Hlen Heq s h; destruct s2; simpl in *; try omega; try tauto.
  assert (s ||= a <=> a0) by (apply (Heq 0); omega).
  assert (s ||= conj_xs s1 <=> conj_xs s2).
  { apply IHs1; [omega|].
    intros i Hl; apply (Heq (S i)); auto; omega. }
  clear IHs1 Hlen Heq.
  split; apply scRw_stack; intros h' H'; specialize (H h'); specialize (H0 h'); try tauto.
Qed.

Require Import SetoidClass.
Instance equiv_sep_equiv (s : stack) : Equivalence (equiv_sep s).
split; repeat intro; try tauto.
specialize (H h); tauto.
specialize (H h); specialize (H0 h); tauto.
Qed.

Program Instance assn_setoid (s : stack) : Setoid assn :=
  {| equiv := equiv_sep s;
     setoid_equiv := equiv_sep_equiv s |}.

Instance star_proper (s : stack) : Proper (equiv_sep s ==> equiv_sep s ==> equiv_sep s) Astar.
Proof.
  intros p1 p2 H p3 p4 H' h.
  split; apply scRw_stack; intros  h'; firstorder.
Qed.

Lemma sep_assoc (P Q R : assn) : forall s, s ||= P ** Q ** R <=> (P ** Q) ** R.
Proof.
  split; intros. sep_normal. sep_cancel. sep_normal_in H. sep_cancel.
Qed.  

Lemma conj_xs_app (l1 l2 : list assn) :
  forall s, s ||= conj_xs (l1 ++ l2) <=> conj_xs l1 ** conj_xs l2.
Proof.
  induction l1; simpl.
  split; intros H; sep_normal; sep_normal_in H; auto.
  intros; rewrite IHl1, sep_assoc; reflexivity.
Qed.

Lemma emp_unit_l (P : assn) : forall s, s ||= emp ** P <=> P.
Proof.
  split; intros; sep_normal; auto.
  sep_normal_in H; auto.
Qed.

Lemma emp_unit_r (P : assn) : forall s, s ||= P ** emp <=> P.
Proof.
  split; intros; sep_normal; auto.
  sep_normal_in H; auto.
Qed.

Lemma nseq_emp_emp (n : nat) :
  forall s, s ||= conj_xs (nseq n emp) <=> emp.
Proof.
  induction n; simpl.
  - reflexivity.
  - intros; rewrite emp_unit_l; auto.
Qed.

Lemma map_conj {A : Type} (l : list A) (f g : A -> assn) :
  forall s, s ||= conj_xs (map (fun x => f x ** g x) l) <=> conj_xs (map f l) ** conj_xs (map g l).
Proof.
  induction l; simpl; auto; intros.
  - rewrite emp_unit_l; reflexivity.
  - rewrite IHl; split; intros H; sep_normal; sep_normal_in H; repeat sep_cancel.
Qed. 

(*
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
  Fixpoint is_array (e : exp) (n : nat) (f : nat -> exp) (s : nat) :=
    match n with
      | 0 => Aemp
      | S n' => e + Enum (Z.of_nat s) -->p (1%Qc, f s) **
                         is_array e n' f (S s)
    end.

  Fixpoint distribute (d : nat) (e : exp) (n : nat) (f : nat -> exp) (dist : nat -> nat) (s : nat) :=
    match n with
      | O => nseq d emp
      | S n => add_nth (dist s) (e + Enum (Z.of_nat s) -->p (1%Qc, f s)) (distribute d e n f dist (S s))
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

  Lemma distribute_length (d : nat) (e : exp) (n : nat) (f : nat -> exp) (dist : nat -> nat) :
    forall i, length (distribute d e n f dist i) = d.
  Proof.
    induction n; simpl; intros.
    - apply length_nseq.
    - rewrite add_nth_length; auto.
  Qed.

  Notation Enum' n := (Enum (Z.of_nat n)).

  Lemma distribute_correct (d : nat) (e : exp) (n : nat) (f : nat -> exp) (dist : nat -> nat) :
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
    (e + Enum' (s + next) -->p (1%Qc, f (s + next))) **
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
        (e + Enum' (s * nt + i) -->p (1,  f (s * nt + i))) **
        nth i (distribute nt e (n - nt) f (nt_step nt) (S s * nt + i)) emp.
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

  Lemma nth_dist_lt i e f nt (Hnt0 : nt <> 0) n : forall s,
    i < nt -> i < n -> 
    nt_dist_nth i e n f nt (s * nt) <=>
       (e + Enum' ((s * nt) + i) -->p (1%Qc, f ((s * nt) + i))) ** nt_dist_nth i e (n - nt) f nt (S s * nt).
  Proof.
    remember (n / nt) as q eqn:Hq.
    revert Hq; induction q; intros Hq s Hint Hin.
    pose proof (div_mod n nt Hnt0) as Hn.
    rewrite <-Hq, mult_0_r, plus_0_l in Hn.
    assert (n < nt) by (rewrite Hn;apply Nat.mod_upper_bound; auto). 
    - 
  Qed.

  Lemma nth_dist_ge n : forall (i : nat) e f nt (Hnt0 : nt <> 0),
    nt <= n ->
    nt_dist_nth i e n f nt <=> (e + Enum' i -->p (1%Qc, f i)) ** nt_dist_nth i 
  Proof.
    unfold nt_dist_nth; induction n; intros i e f nt Hnt0 Hint Hnnt; simpl.
    - simpl_nth; destruct (leb _ _); reflexivity.
    - rewrite nth_add_nth; [|rewrite distribute_length; unfold nt_step; auto..].
      remember (beq_nat i _) as b0 eqn:Hb0; remember (i <? S n) as b1 eqn:Hb1.
      cutrewrite (nt_step nt n = n) in Hb0; [|unfold nt_step; rewrite Nat.mod_small; omega].
      assert (i < n \/ i = n \/ n < i) as [Hin | [Hin | Hin]] by omega;
        symmetry in Hb0; destruct b0;  first [apply beq_nat_true in Hb0 | apply beq_nat_false in Hb0];
        symmetry in Hb1; destruct b1;  first [apply ltb_lt_false in Hb1 | apply ltb_lt in Hb1]; 
        try omega; [rewrite IHn; auto; [|omega]..].
      rewrite ((proj2 (ltb_lt _ _)) Hin); reflexivity.
      cutrewrite (i <? n = false); [|apply ltb_lt_false; omega]; rewrite emp_unit_r; subst; reflexivity.
      cutrewrite (i <? n = false); [|apply ltb_lt_false; omega]; reflexivity.
  Qed.
  
  Lemma nth_dist_skip (i : nat) e n f nt (Hnt0 : nt <> 0) :
    i < nt ->
    nt_dist_nth i e n f nt <=> skip_array e f Hnt0 n i.
  Proof.
    intros Hint.
    unfold nt_dist_nth, skip_array.
    remember (n / nt) as q eqn:Hq.
    revert Hq; induction q; intros Hq.
    - pose proof (div_mod n nt Hnt0) as Hnnt; rewrite <-Hq, mult_0_r in Hnnt; simpl in Hnnt.
      assert (n < nt) by (rewrite Hnnt; apply Nat.mod_upper_bound; auto).
      rewrite Fix_eq; unfold skip_array_body.
      cutrewrite (0 <? n - x = false); [|destruct (0 <? n - nt) eqn:Ht; auto; apply ltb_lt in Ht; omega].
      induction n; simpl; [simpl_nth; destruct (leb _ _); reflexivity|].
      unfold nt_step.
      
  
\Definition modi_filter {A : Type} (l : list A) s i n :=
  map snd (filter (fun x => beq_nat (fst x mod n) i) (combine (seq s (length l)) l)).



Lemma modi_filter_cons : forall {A : Type} (l : list A) (s i n : nat) (d : A),
                           n <> 0 ->
                           n <= length l -> i < n ->
                           modi_filter l (s * n) i n = nth i l d :: modi_filter (skipn n l) (S s * n) i n.
Proof.
  unfold modi_filter; intros A l s i n d Hn0 Hnl Hin.
  assert (Heq :combine (seq (s * n) (length l)) l =
               combine (seq (s * n) n) (firstn n l) ++
                       combine (seq (S s * n) (length l - n)) (skipn n l)).
  { assert (H' : length l = n + (length l - n)) by omega.
    rewrite H' at 1; rewrite seq_add; rewrite <-(firstn_skipn n l) at 2.
    rewrite combine_app; simpl; crush_len.
    cutrewrite (s * n + n = n + s * n); [|omega]; eauto. }
  rewrite Heq, filter_app, map_app; clear Heq.
  match goal with
    | [|- ?X ++ ?Y = ?Z :: ?W] => assert (Heq : X = Z :: nil /\ Y = W)
  end; [|destruct Heq as [Heq1 Heq2]; rewrite Heq1, Heq2; simpl; eauto].
  split.
  - rewrite filter_mask.
    assert (Heq : map (fun x => beq_nat (fst x mod n) i) (combine (seq (s * n) n) (firstn n l)) =
                  nseq i false ++ (true :: nseq (n - i - 1) false)); [|rewrite Heq; clear Heq].
    { apply (@eq_from_nth _ false); crush_len.
      intros j Hj. rewrite (nth_map (0, d)); simpl_nth.
      rewrite plus_comm, Nat.add_mod, Nat.mod_mul, <-plus_n_O, Nat.mod_mod, Nat.mod_small; auto.
      assert (j < i \/ j = i \/ i < j) as [H | [H | H]] by omega.
      + rewrite app_nth1; crush_len. simpl_nth.
        destruct (leb i j); apply beq_nat_false_iff; omega.
      + rewrite app_nth2; crush_len.
        subst; rewrite minus_diag; simpl.
        apply beq_nat_true_iff; omega.
      + rewrite app_nth2; crush_len.
        case_eq (j - i); intros; try omega; simpl; rewrite nth_nseq.
        destruct (leb (n - i - 1) n0); apply beq_nat_false_iff; omega. }
    rewrite <-(firstn_skipn i (combine _ _)).
    rewrite mask_cat; crush_len.
    case_eq (skipn i (combine (seq (s * n) n) (firstn n l))); [|intros x ss]; intros H.
    apply (f_equal (@length (nat * A))) in H; simpl in H; crush_len.
    simpl; rewrite !mask_false; simpl; f_equal.
    apply (f_equal (fun x => nth 0 x (0, d))) in H; simpl in H.
    rewrite <-H, nth_skipn, combine_nth, nth_firstn; crush_len.
    rewrite <-plus_n_O; auto.
  - crush_len.
Qed.

Lemma map_firstn:
  forall (n0 : nat) (T1 T2 : Type) (f : T1 -> T2) (s : list T1),
    map f (firstn n0 s) = firstn n0 (map f s).
Proof.
  induction n0; intros; destruct s; simpl; eauto.
  rewrite IHn0; eauto.
Qed.

Lemma modi_filter_nil {T : Type} (l : list T) (n : nat) (i : nat) (s : nat) (d : T):
  n <> 0 -> length l <= n -> i < n -> modi_filter l (s * n) i n =
                                      if leb (length l) i then nil else nth i l d :: nil.
Proof.
  unfold modi_filter; intros Hn0 Hln Hin; case_eq (leb (length l) i); intros Hli;
  [apply leb_iff in Hli | apply leb_iff_conv in Hli]; rewrite filter_mask.
  - match goal with
        [|- context [mask ?X _]] =>
        assert (Heq: X = nseq (length l) false);
          [|rewrite Heq; clear Heq; rewrite mask_false; auto]
    end.
    apply (@eq_from_nth _ false); crush_len.
    intros j Hj. rewrite (nth_map (0, d)); crush_len.
    simpl_nth.
    rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; [|omega].
    rewrite leb_correct_conv; auto; apply beq_nat_false_iff; omega.
  - match goal with
        [|- context [mask ?X _]] =>
        assert (Heq: X = nseq i false ++ (true :: nil) ++ nseq (length l - i - 1) false)
    end.
    { rewrite <-(firstn_skipn i (combine (seq (s * n) (Datatypes.length l)) l)).
      rewrite <-(firstn_skipn 1 (skipn i (combine (seq (s * n) (Datatypes.length l)) l))).
      rewrite !map_app.
      assert (map (fun x : nat * T => beq_nat (fst x mod n) i)
                  (firstn 1 (skipn i (combine (seq (s * n) (Datatypes.length l)) l))) = true :: nil).
      { apply (@eq_from_nth _ false); crush_len.
        { case_eq (length l - i); intros; omega. }
        intros j Hj.
        case_eq (length l - i); [|intros nl]; intros H; rewrite H in Hj; try omega.
        assert (j = 0) by omega.
        case_eq (skipn i (combine (seq (s * n) (length l)) l)); [|intros x l']; intros Heq.
        - apply (f_equal (@length (nat * T))) in Heq. crush_len.
        - apply (f_equal (fun x => nth 0 x (0, d))) in Heq; simpl in Heq.
          autorewrite with nth in Heq; crush_len.
          subst; simpl; rewrite <-plus_n_O, plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto.
          rewrite <-beq_nat_refl; auto. }
      rewrite H. f_equal.
      - apply (@eq_from_nth _ false); crush_len.
        intros j Hj; rewrite (nth_map (0, d)); crush_len.
        simpl_nth. rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; try omega.
        destruct (leb i j); apply beq_nat_false_iff; omega.
      - remember 1; simpl; f_equal; subst.
        apply (@eq_from_nth _ false); [crush_len|].
        intros j Hj. autorewrite with len in Hj; rewrite Nat.min_id in Hj.
        rewrite (nth_map (0, d)); [|crush_len].
        simpl_nth.
        rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; try omega.
        destruct (leb _ _); apply beq_nat_false_iff; omega. }
    rewrite <-(firstn_skipn i (combine (seq (s * n) (length l)) l)) at 2.
    rewrite <-(firstn_skipn 1 (skipn i (combine (seq (s * n) (length l)) l))).
    rewrite Heq, !mask_cat; [|crush_len..].
    rewrite !map_app, !mask_false; simpl.
    case_eq (skipn i (combine (seq (s * n) (Datatypes.length l)) l)); [|intros x l']; intros Hxl.
    apply (f_equal (@length (nat * T))) in Hxl; crush_len.
    apply (f_equal (fun x => nth 0 x (0, d))) in Hxl; simpl in Hxl.
    autorewrite with nth in Hxl; crush_len; subst; simpl; rewrite <-plus_n_O; auto.
    case_eq (length l - i); intros; omega.
Qed.

Definition conj_xs : list assn -> assn := fold_right Astar emp.

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

Lemma distribute_correct' : forall (s : nat) (l: list assn) (n : nat),
                              (0 < n) ->
                              conj_xs l <=>  conj_xs (map conj_xs (map (fun i => modi_filter l (s * n) i n) (seq 0 n))).
Proof.
  intros s l n Hn0; assert (Hnn0 : n <> 0) by omega.
  remember (length l / n) as q eqn:Hq.
  revert l s Hq; induction q; intros l s Hq.
  - pose proof (div_mod (length l) n Hnn0) as Hdm.
    rewrite <-Hq, mult_0_r in Hdm; simpl in Hdm.
    assert (length l <= n).
    { rewrite Hdm.
      pose proof (Nat.mod_upper_bound (length l) n Hnn0); omega. }
    rewrite map_map.
    lazymatch goal with [|- _ <=> ?X] =>
    assert (H' : X <=> conj_xs (l ++ nseq (n - length l) emp)); [|rewrite H']
  end.
  { apply (@equiv_from_nth emp); [crush_len|].
    intros i Hi; simpl_nth.
    rewrite (nth_map 0); [|crush_len].
    rewrite (modi_filter_nil _ emp); auto; simpl_nth.
    destruct (leb (length l) i) eqn:Hl; simpl.
    - apply leb_iff in Hl.
      rewrite app_nth2; [|crush_len]; simpl_nth.
      lazymatch goal with [|- context [if ?b then _ else _]] => destruct b end; reflexivity.
    - apply leb_iff_conv in Hl.
      rewrite app_nth1; [|crush_len]; simpl_nth.
      split; [apply sc_emp2'| apply sc_emp2]. }
  rewrite conj_xs_app, nseq_emp_emp, emp_unit_r; reflexivity.
  - assert (n <= length l).
    { pose proof (div_mod (length l) n Hnn0) as Hdm; rewrite <-Hq in Hdm.
      rewrite Hdm, mult_succ_r; generalize (n * q); intros; omega. }
    rewrite map_map.
    assert (H' : conj_xs (map (fun i => conj_xs (modi_filter l (s * n) i n)) (seq 0 n)) <=>
                         conj_xs (map (fun i => nth i l emp ** conj_xs (modi_filter (skipn n l) (S s * n) i n)) (seq 0 n)));
      [|rewrite H'; clear H'].
    { apply (@equiv_from_nth emp); [crush_len|].
      intros j Hj; crush_len.
      repeat (rewrite (nth_map 0); [|crush_len]).
      rewrite (modi_filter_cons _ emp); auto; simpl_nth; reflexivity. }
    rewrite map_conj; rewrite  <-(firstn_skipn n l) at 1.
    rewrite conj_xs_app, (IHq (skipn n l) (S s)).
    + apply star_proper; [apply (@equiv_from_nth emp); [crush_len|]..]; intros i Hj; simpl_nth.
      * rewrite (nth_map 0); [|crush_len].
        rewrite seq_nth; [|crush_len]; reflexivity.
      * rewrite (nth_map []); [|crush_len]; repeat (rewrite (nth_map 0); [|crush_len]).
        reflexivity.
    + crush_len.
      cutrewrite (length l = length l - n + 1 * n) in Hq; [|omega].
      rewrite Nat.div_add in Hq; auto.
      omega.
Qed.
*)