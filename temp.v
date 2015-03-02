Require Import Vector.
Import VectorNotations.
Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Section Test1.
  Variable P : Prop.
  Variable Q : nat -> Prop.
  Goal (forall n, P /\ Q n) -> P /\ (forall n, Q n).
  Proof.
    intros H.
    split; [apply (H 0) | intros n; apply (H n)].
  Qed.
End Test1.

Section Test2.
  Variable P : nat -> Prop.
  Variable Q : nat -> nat -> Prop.
  
  Goal (forall n, exists m, P m /\ Q m n) -> exists m, P m /\ forall n, Q m n.
  Proof.
    intros H.
    destruct (H 0) as [m [Pm Qmn]].
  Abort.
End Test2.  

Section Test3.
  Variable T U : Type.
  Variable P : T -> Prop.
  Variable Q : U -> Prop.

  Goal (exists x : T, P x) -> (exists y : U, Q y) -> (exists z : (T * U), P (fst z) /\ Q (snd z)).
  Proof.
    intros [x HPx] [y HQy].
    exists (x, y); eauto.
  Qed.
End Test3.

Lemma finvS (n : nat) (i : Fin.t (S n)) : (i = Fin.F1 \/ exists i', i = Fin.FS i').
Proof.
  apply (Fin.caseS (fun n (i : Fin.t (S n)) =>  i = Fin.F1 \/ (exists i' : Fin.t n, i = Fin.FS i'))).
  - intros n0; tauto.
  - intros n0 p; right; eexists; tauto.
Qed.


Section Forall_ex_ex_v.
  Variable T : Type.
  Variable n : nat.
  Hypothesis n_gt_0 : n > 0.
  Variable P : Fin.t n -> T -> Prop.

  Goal (forall i : Fin.t n, exists x : T, P i x) -> 
  (exists v : Vector.t T n, forall i : Fin.t n, P i v[@i]).
  Proof.
    induction n as [|n']; [omega| intros H].
    destruct n' as [|n'']; [destruct (H Fin.F1) as [x Hx]; exists [x] | ].
    - intros i; destruct (finvS i) as [|[i' H']]; [subst; eauto|inversion i'].
    - remember (fun (i : Fin.t (S n'')) x => P (Fin.FS i) x) as P'.
      assert (forall i : Fin.t (S n''), exists x : T, P' i x) as Hex.
      { intros i; subst; apply (H (Fin.FS i)). }
      assert (S n'' > 0) as Hsg by omega.
      destruct (IHn' Hsg P' Hex) as [v IHP'].
      destruct (H Fin.F1) as [x1 H1].
      exists (x1 :: v); intros i; destruct (finvS i) as [|[i' ?]]; subst; eauto.
  Qed.
End Forall_ex_ex_v.