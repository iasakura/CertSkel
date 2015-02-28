Require Import Vector.
Import VectorNotations.
Require Import Omega.
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

Section Test4.
  Variable T : Type.
  Variable n : nat.
  Hypothesis n_gt_0 : n > 0.
  Variable P : Fin.t n -> T -> Prop.
  Goal (forall i : Fin.t n, exists x : T, P i x) -> 
          (exists v : Vector.t T n, forall i : Fin.t n, P i v[@i]).
  Proof.
    induction n; [omega | ].
    intros Hi.
    