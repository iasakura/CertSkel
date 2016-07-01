Require Import GPUCSL.
Require Import Monad.
Require Import SimplSkel.
Require Import LibTactics.
Open Scope list_scope.

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

Fixpoint nth_error {A : Type} (l:list A) (n:nat) : comp A :=
  match n, l with
  | O, x :: _ => Some x
  | S n, _ :: l => nth_error l n
  | _, _ => None
  end.

Definition seq s l := map Z.of_nat (seq s l).

Open Scope Z_scope.

Definition max_idx (arr : list Z) : comp (list (Z * Z)) :=
  reduceM (fun x y => if (fst x) <? (fst y) then ret x else ret y) (zip arr (seq 0 (length arr))).

Module Sx := Syntax.
Definition rel (p : Sx.prog) (f : list Z -> comp (list (Z * Z))) : Prop := True.

Definition id_ (A : Type) := A.
Instance id_monad : Monad id := {
  ret A x := id x;
  bind A B x f := f x
}.

Goal {p : Sx.prog | rel p max_idx}.
Proof.
  unfold max_idx.
  
  Lemma ext_fun p f g : (forall x, f x = g x) -> rel p f -> rel p g.
  Proof.
    unfold rel; tauto.
  Qed.
  
  Lemma change_spec {A : Type} (P Q : A -> Prop) : (forall x, P x -> Q x) -> {x : A | P x} -> {x : A | Q x}.
  Proof.
    intros ? [? ?]; eexists; eauto.
  Qed.

  eapply change_spec; intros.
  eapply ext_fun; intros.

  Lemma let_bind {A B : Type} (t : list A) (f : list A -> id B) : (let x := t in f x) = (do! x := t in f x).
  Proof. eauto. Qed.
  
  Lemma let_lift1 {A B : Type} (f : list A -> B) (xs : list A) : f (xs) = do! t := xs in (f t : id B).
  Proof. eauto. Qed.

  rewrite (let_lift1 _ (zip _ _)).
  rewrite (let_lift1 _ (seq _ _)).

  Lemma let_lift2 {A B C : Type} (ae : list A) (f : list A -> B) (g : B -> C) :
    (do! t := do! u := ae in f u : id B in g t) =
    (do! u := ae in do! t := f u : id B in g t).
  Proof. eauto. Qed.

  rewrite (let_lift2 (seq _ _)).
