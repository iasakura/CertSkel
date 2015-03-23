Require Export Vector.
Require Import Eqdep.
Import VectorNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Section Fin.
  Lemma finvS (n : nat) (i : Fin.t (S n)) : (i = Fin.F1 \/ exists i', i = Fin.FS i').
  Proof.
    pattern n, i; apply (Fin.caseS).
    - intros n0; tauto.
    - intros n0 p; right; eexists; tauto.
  Qed.

Lemma fin_eq_dec : forall (n : nat) (i j : Fin.t n), {i = j} + {i <> j}.
Proof.
  refine (
      fun n =>
        match n with
          | O => fun (i _ : Fin.t 0) => match (Fin.case0 (fun _ => False) i) with end
          | S n => 
            Fin.rect2 (fun n (i : Fin.t n) (j : Fin.t n) => {i = j} + {i <> j})
                      (fun n => left _ _)
                      (fun n f => right _ _)
                      (fun n f =>  right _ _)
                      (fun n f g (b : {f = g} + {f <> g}) => if b then left _ _ else right _ _)
        end); subst; try inversion 1; eauto.
  apply inj_pair2 in H1; congruence.
Qed.
End Fin.

Section Vector.
  Variable T : Type.
  Variable n : nat.

  Lemma vec_exvec (P : Fin.t n -> T -> Prop) : 
    (forall i : Fin.t n, exists x : T, P i x) -> 
    exists v : Vector.t T n, forall i : Fin.t n, P i v[@i].
  Proof.
    induction n as [|n']; [exists []; inversion 0 | intros H].
    destruct n' as [|n'']; [destruct (H Fin.F1) as [x Hx]; exists [x] | ].
    - intros i; destruct (finvS i) as [|[i' H']]; [subst; eauto|inversion i'].
    - set (P' := (fun (i : Fin.t (S n'')) x => P (Fin.FS i) x)).
      assert (forall i : Fin.t (S n''), exists x : T, P' i x) as Hex.
      { intros i; subst; apply (H (Fin.FS i)). }
      destruct (IHn' P' Hex) as [v IHP'].
      destruct (H Fin.F1) as [x1 H1].
      exists (x1 :: v); intros i; destruct (finvS i) as [|[i' ?]]; subst; unfold P' in *; eauto.
  Qed.

  Variable t : T.

  Lemma vec_eq_ex (f : Fin.t n -> T) :
    (forall i j : Fin.t n, f i = f j) -> (exists c, forall i : Fin.t n, f i = c).
  Proof.
    induction n; intros H; [exists t; intros i; inversion i | ].
    exists (f Fin.F1); intros i; destruct (finvS i) as [| [i' ?]]; subst; eauto.
  Qed.

  Fixpoint init (n : nat) : (Fin.t n -> T) -> Vector.t T n :=
    match n with
      | 0 => fun _ => []
      | S n' => fun f => (f Fin.F1) :: init (fun i => f (Fin.FS i)) 
    end%nat.

  Lemma init_spec (m : nat) (f : Fin.t m -> T) : forall i : Fin.t m, (init f)[@i] = f i.
  Proof.
    revert f; induction m; intros f i; [inversion i|].
    destruct (finvS i) as [|[i' ?]]; subst; simpl; [| rewrite IHm]; eauto.
  Qed.

  Lemma vinv0 (v : Vector.t T 0) : v = [].
  Proof.
    pattern v; apply case0; eauto.
  Qed.

  Lemma vinvS (v : Vector.t T (S n)) : exists x y, v = x :: y.
    pattern n, v; apply caseS.
    intros x n1 y; repeat eexists; eauto.
  Qed.
End Vector.
