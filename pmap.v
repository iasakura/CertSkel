Set Implicit Arguments.
Unset Strict Implicit.

Require Import Qcanon.
Require Import assertions.
Require Import Lang.
Require Import CSL.
Require Import PHeap.

Local Notation TID := (Var 0).
Local Notation ARR := (Var 1).
Local Notation X := (Var 2).
Local Notation Y := (Var 3).
Open Scope exp_scope.
Open Scope bexp_scope.

Section pmap.
  Definition ele (x y : exp) := (nosimpl (fun s (h : pheap) => edenot x s <= edenot y s)%Z).
  Notation "x '<==' y" := (ele x y) (at level 70, no associativity).
  Definition elt (x y : exp) := (nosimpl (fun s (h : pheap) => edenot x s < edenot y s)%Z).
  Notation "x '<<' y" := (elt x y) (at level 70, no associativity).

  Variable ntrd : nat.
  Variable len : nat.
  
  Local Notation I := (Var 4).

  Definition map :=
    I ::= TID%Z;;
    Cwhile (I < Z.of_nat len) (
      X ::= [ARR + I] ;;
      [ARR + I] ::= X + 1%Z ;;
      I ::= I + Z.of_nat ntrd%Z
    ).
  Require Import NPeano.
  Require Import Arith.
  Require Import List.
  Import ListNotations.
  Local Open Scope list_scope.
  Local Close Scope exp_scope.
  Local Open Scope nat_scope.

  Definition modi_filter {A : Type} (l : list A) s i n :=
    map snd (filter (fun x => beq_nat (fst x mod n) i) (combine (seq s (length l)) l)).

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

Require Import SetoidClass.
Instance equiv_sep_equiv : Equivalence equiv_sep.
  split; repeat intro; try tauto.
  specialize (H s h); tauto.
  specialize (H s h); specialize (H0 s h); tauto.
Qed.

Program Instance assn_setoid : Setoid assn := {|
      equiv := equiv_sep;
      setoid_equiv := equiv_sep_equiv
    |}.

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

Section map.
  Definition ele (x y : exp) := (nosimpl (fun s (h : pheap) => edenot x s <= edenot y s)%Z).
  Notation "x '<==' y" := (ele x y) (at level 70, no associativity).
  Definition elt (x y : exp) := (nosimpl (fun s (h : pheap) => edenot x s < edenot y s)%Z).
  Notation "x '<<' y" := (elt x y) (at level 70, no associativity).
  Local Notation I := (Var 4).
  Variable len : nat.
  Variable ntrd : nat.
  Notation ntrdZ := (Z.of_nat ntrd).
  Variable f : nat -> Z.
  Definition loop_inv : assn :=
    Ex x : nat,
      is_array ARR x (fun i => Z.succ (f i)) **
      is_array (ARR + Z.of_nat x) (len - x) (fun j => f (j + x)) **
      !(I === Z.of_nat x) ** !(pure (x < len))%nat.

  Definition map :=
    I ::= 0%Z;;
    WhileI loop_inv (I < Z.of_nat len) (
      X ::= [ARR + I] ;;
      [ARR + I] ::= X + 1%Z ;;
      I ::= I + 1%Z
    ).

  Lemma is_array_unfold : forall (n : nat) (i : nat) (fi : nat -> Z) (e : exp),
    (i < n)%nat ->
    is_array e n fi |=
      (e + Z.of_nat i) -->p (1, fi i) **
      (is_array e i fi) **
      (is_array (e + Z.succ (Z.of_nat i)) (n - i - 1) (fun j => fi (S (i + j))%nat)).
  Proof.
    induction n; intros; [omega|].
    assert (i < n \/ i = n)%nat as [Hle|] by omega; subst.
    simpl in H0.
    eapply scRw in H0; [|intros ? ? H'; exact H' | intros ? ? H'; apply (IHn i) in H'; [exact H' | auto]].
    do 2 sep_cancel.
    cutrewrite (S n - i - 1 = S (n - i - 1)); [|omega].
    simpl; apply scC; sep_cancel.
    assert (Z.of_nat i + Z.succ (Z.of_nat (n - i - 1)) = Z.of_nat n)%Z.
    (rewrite <-Zplus_succ_r_reverse, <-Znat.Nat2Z.inj_add, <-Znat.Nat2Z.inj_succ; f_equal; omega).
    assert (S (i + (n - i - 1)) = n)%nat by omega.
    sep_cancel.
    simpl in H0.
    sep_cancel.
    cutrewrite (S n - n - 1 = 0); [|omega]; simpl.
    sep_normal; sep_cancel.
  Qed.

  Lemma is_array_S : forall (n : nat) (fi : nat -> Z) (e : exp),
    is_array e (S n) fi |= e -->p (1, fi 0) ** is_array (e + 1%Z) n (fun i => fi (S i)).
  Proof.
    induction n as [|n]; [simpl|]; intros; sep_cancel.
    cutrewrite (is_array e (S (S n)) fi =
                ((e + Z.of_nat (S n)) -->p (1, fi (S n)) ** is_array e (S n) fi)) in H; [|auto].
    cutrewrite (is_array (e + 1%Z) (S n) (fun i : nat => fi (S i)) =
                (e + 1%Z + Z.of_nat n -->p (1, fi (S n)) ** 
                is_array (e + 1%Z) n (fun i : nat => fi (S i)))); [|auto].
    apply scCA. rewrite Znat.Nat2Z.inj_succ in H. sep_cancel.
    apply IHn in H. auto.
  Qed.

  Lemma Ex_intro {T : Type} (P : T -> assn) (x : T) :P x |= (Ex x, P x).
  Proof. intros; exists x; auto. Qed.

  Lemma map_correct (tid : Fin.t ntrd) (bspec : Bdiv.barrier_spec ntrd) :
    CSL bspec tid (is_array ARR len f) map (is_array ARR len (fun i => Z.succ (f i))).
  Proof.
    unfold map.
    eapply rule_seq; [hoare_forward; intros ? ? H; exact H| ].
    hoare_forward.
    eapply Hbackward.
    Focus 2.
    intros ? ? H.
    unfold loop_inv in H; sep_split_in H; destruct H; repeat sep_split_in H.
    cutrewrite (len - x = S (len - x - 1)) in H; [|unfold Apure in HP1; simpl in HP1; omega].
    eapply scRw in H; [idtac | intros ? ? H'; exact H' |
                       intros ? ? H'; apply is_array_S in H'; exact H'].
    sep_lift_in H 1.
    sep_combine_in H.

    
    
 (*Section Hoare_test.
  Variable ntrd : nat.
  Notation ntrdZ := (Z.of_nat ntrd).

  Require Import MyVector.
  Import VectorNotations.

  Definition bpre (tid : Fin.t ntrd) := 
    (ARR + (Z_of_fin tid) -->p (1%Qc, (Z_of_fin tid)))%assn.
  Definition bpost (tid : Fin.t ntrd) := 
    (ARR + ((Z_of_fin tid + 1) mod ntrdZ)%Z) -->p (1%Qc, ((Z_of_fin tid + 1) mod ntrdZ)%Z).
  Notation FalseP := (fun (_ : stack) (h : pheap) => False).
  Definition default : (Vector.t assn ntrd * Vector.t assn ntrd) := 
    (init (fun _ => FalseP), init (fun _ => FalseP)).

  Definition bspec (i : nat) :=
    match i with
      | 0 => (init bpre, init bpost)
      | S _ => default
    end.

  Lemma rotate_l7 (tid : Fin.t ntrd) :
      CSL bspec tid
      (( ARR +  ((Z_of_fin tid + 1) mod ntrdZ))%exp -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ))%Z **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid)))
      (Cif ( TID ==  (ntrdZ - 1)%Z) (
         Y ::=  0%Z
       ) (
         Y ::=  TID +  1%Z
       ))
      ((( ARR +  Y) -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ)%Z) **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid) //\\
         Y ===  ((Z_of_fin tid + 1) mod ntrdZ)%Z))).
    Proof.
      hoare_forward; [hoare_forward | hoare_forward | idtac].
      intros. simpl in H. sep_split_in H. subA_normalize_in H. simpl in H.
      sep_combine_in H. exact H.
      intros. simpl in H. sep_split_in H. subA_normalize_in H. simpl in H. sep_combine_in H. exact H.
      intros ? ? H.
      destruct H.
      sep_split_in H.
    Abort.


  Hint Unfold bspec bpre bpost.
  Hint Rewrite MyVector.init_spec : sep.
  Lemma rotate_l4 (tid : Fin.t ntrd) :
    CSL bspec tid
      (( ARR +  (Z_of_fin tid)) -->p (1%Qc,  (Z_of_fin tid)) **
                                !( TID ===  (Z_of_fin tid)) ** !(X ===  (Z_of_fin tid)))
      (Cbarrier 0)
      (( ARR +  ((Z_of_fin tid + 1) mod ntrdZ)%Z) -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ)%Z) **
      !( TID ===  (Z_of_fin tid)) **  !(X ===  (Z_of_fin tid))).
  Proof.
    hoare_forward.
    intros.
    sep_cancel.
  Qed.

  Lemma rotate_l2 (tid : Fin.t ntrd) (P Q : assn) (E : exp) :
    (inde P (X :: List.nil)) -> (inde Q (X :: List.nil)) -> (indeE E X) ->
    CSL bspec tid 
      (P ** Q ** (E -->p (1%Qc, 3%Z)) ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid)))
      (X ::= [ ARR + TID]) 
      (P ** Q ** (ARR + TID -->p (1%Qc, (Z_of_fin tid))) ** !( TID === (Z_of_fin tid)) ** (E -->p (1%Qc, 3%Z))).
    Proof.
      intros. 
      hoare_forward.
      intros; sep_normal_in H2; sep_split_in H2; sep_normal; sep_split; solve [auto | repeat sep_cancel].
    Qed.

  Lemma rotate_l3 (tid : Fin.t ntrd) (P Q : assn) (E : exp) :
    (inde P (X :: List.nil)) -> (inde Q (X :: List.nil)) -> (indeE E X) ->
    CSL bspec tid 
      (P ** Q ** (E -->p (full_p%Qc, 2%Z)) ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid)))
      ([ ARR + TID] ::= 3%Z) 
      (P ** Q ** (ARR + TID -->p (full_p%Qc, 3%Z)) ** !( TID === (Z_of_fin tid)) ** (E -->p (1%Qc, 2%Z))).
  Proof.
    intros. hoare_forward.
    intros; repeat sep_cancel.
  Qed.

  Lemma test_assign (tid : Fin.t ntrd) (P Q : assn) (E : exp) :
    CSL bspec tid 
        (P ** Q ** (E -->p (full_p%Qc, 2%Z)) ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid)))
        (X ::= 3%Z) 
        (P ** Q ** (ARR + TID -->p (full_p%Qc, 3%Z)) ** !( TID === (Z_of_fin tid)) ** (E -->p (1%Qc, 2%Z))).
  Proof.
    intros. hoare_forward.
    intros s h H.
    sep_split_in H; simpl in *.
    subA_normalize_in H.
  Abort.
End Hoare_test.*)
