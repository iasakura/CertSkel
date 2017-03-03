Require Import Monad.
Require Import MyList.
Require Import List.
Require Import ZArith.
Require Import Psatz.
Require Import LibTactics.

Definition comp := option.
Instance Monad_comp : Monad comp := option_monad.
Definition mapM {A B : Type} (f : A -> comp B) (xs : list A) := sequence (List.map f xs).

Definition lift_op {A : Type} (f : A -> A -> comp A) : comp A -> comp A -> comp A :=
  fun x y => match x, y with
             | Some x, Some y => (f x y)
             | Some x, None | None, Some x => Some x
             | None, None => None
             end.

Definition reduceM {A : Type} (f : A -> A -> comp A) (xs : list A) : comp (list A) :=
  match List.fold_right (lift_op f) None (List.map Some xs) with
  | Some x => ret (x :: nil)
  | None => None
  end.

Definition zip {A B : Type} := @List.combine A B.

Fixpoint nth_error_nat {A : Type} (l:list A) (n:nat) : comp A :=
  match n, l with
  | O, x :: _ => Some x
  | S n, _ :: l => nth_error l n
  | _, _ => None
  end.

Definition Z_to_nat_error (n : Z) : comp nat :=
  if Z_le_dec 0 n then ret (Z.to_nat n)
  else None.

Definition nth_error {A : Type} (l : list A) (n : Z) : comp A :=
  do! n <- Z_to_nat_error n in
  nth_error l n.

Fixpoint seq' s l := 
  match l with
  | O => nil
  | S l => s :: seq' (Z.succ s) l
  end.

Definition seq s l := seq' s (Z.to_nat l).

Definition len {A} (l : list A) := Z.of_nat (length l).

Lemma nth_error_some T (ls : list T) i d :
  i < length ls
  -> List.nth_error ls i = Some (nth i ls d).
Proof.
  revert ls; induction i; simpl; destruct ls; simpl in *; intros; try omega.
  reflexivity.
  intuition.
Qed.

Ltac unfoldM := simpl; unfold Monad.bind_opt.

Lemma nth_error_some' T (ls : list T) (i : Z) d :
  (0 <= i < Z.of_nat (length ls))%Z
  -> nth_error ls i = Some (nth (Z.to_nat i) ls d).
Proof.
  unfold nth_error; simpl; unfoldM.
  intros.
  unfold Z_to_nat_error; destruct Z_le_dec; try lia; simpl.
  apply nth_error_some.
  zify; rewrite Z2Nat.id; lia.
Qed.

Lemma mapM_some A B (xs : list A) (ys : list B) i d1 d2 f :
    mapM f xs = Some ys ->
    Some (nth i ys d2) = if lt_dec i (length xs) then f (nth i xs d1) else Some d2.
Proof.
  unfold mapM; revert i ys; induction xs; simpl; introv Heq;
  destruct i, ys; try inverts Heq; simpl; eauto.
  - unfold Monad.bind_opt in *.
    destruct (f a) eqn:Heq1; inverts H0.
    destruct (sequence _); inverts H1.
  - unfold Monad.bind_opt in *.
    destruct (f a) eqn:Heq1; inverts H0.
    destruct (sequence _) eqn:Heq2; inverts H1; eauto.
  - unfold Monad.bind_opt in *.
    destruct (f a) eqn:Heq1; inverts H0.
    destruct (sequence _) eqn:Heq2; inverts H1; eauto.
  - unfold Monad.bind_opt in *.
    destruct (f a) eqn:Heq1; inverts H0.
    destruct (sequence _) eqn:Heq2; inverts H1; eauto.
    erewrite IHxs; destruct (lt_dec i (length xs)), (lt_dec (S i) (S (length xs))); try lia;
    eauto.
Qed.

    
Lemma mapM_length A B (xs : list A) (ys : list B) f :
  mapM f xs = Some ys -> length ys = length xs.
Proof.
  revert ys; unfold mapM; induction xs; introv.
  - inversion 1; eauto.
  - simpl.
    unfold Monad.bind_opt; destruct (f a), (@sequence _ _ _); simpl;
    destruct ys; inversion 1; substs; simpl; rewrite IHxs; eauto.
Qed.

Lemma seq'_length n m : length (seq' n m) = m.
Proof.
  revert n; induction m; simpl; congruence.
Qed.

Lemma seq'_nth n m i d : nth i (seq' n m) d = if lt_dec i m then (n + Z.of_nat i)%Z else d.
Proof.
  revert n i; induction m; simpl; intros n [|i]; eauto.
  destruct lt_dec; eauto; try lia.
  rewrites IHm.
  repeat destruct lt_dec; try lia.
Qed.

Lemma seq_length n m : length (seq n m) = Z.to_nat m.
Proof.
  unfold seq; rewrite seq'_length; eauto.
Qed.

Lemma seq_nth n m i d : nth i (seq n m) d = if lt_dec i (Z.to_nat m) then (n + Z.of_nat i)%Z else d.
Proof.
  unfold seq; apply seq'_nth.
Qed.