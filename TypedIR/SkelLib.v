Require Import Monad.
Require Import MyList.
Require Import List.
Require Import ZArith.

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
  do! n := Z_to_nat_error n in
  nth_error l n.

Fixpoint seq' s l := 
  match l with
  | O => nil
  | S l => s :: seq' (Z.succ s) l
  end.

Definition seq s l := seq' s (Z.to_nat l).

Definition len {A} (l : list A) := Z.of_nat (length l).
