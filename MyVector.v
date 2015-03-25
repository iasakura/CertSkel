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

Section FusionLemmas.
  Variable T U V W : Type.
  Variable n : nat.

  Lemma map_map (v : Vector.t T n) (f : T -> U) (g : U -> V) :
    (Vector.map g (Vector.map f v)) = Vector.map (fun x => g (f x)) v.
  Proof.
    induction v; simpl; eauto.
    rewrite IHv; eauto.
  Qed.

  Lemma map_map2 (f : T -> U) (g : V -> W -> T) 
        (v2 : Vector.t V n) (v3 : Vector.t W n) :
    Vector.map f (Vector.map2 g v2 v3) = Vector.map2 (fun x y => f (g x y)) v2 v3.
    induction v2.
    - rewrite (vinv0 v3) in *; simpl; eauto.
    - destruct (vinvS v3) as [? [? ?]]; subst; simpl; rewrite IHv2; eauto.
  Qed.
  
  Lemma map2_map (v1 : Vector.t (T * U) n) (v2 : Vector.t V n) (t : T) :
    Vector.map2 (fun x y => (t, snd (fst x, y))) v1 v2 = Vector.map (pair t) v2.
  Proof.
    induction v1.
    - rewrite (vinv0 v2); constructor.
    - destruct (vinvS v2) as [h' [v2' ?]]; subst.
      simpl. rewrite IHv1; eauto.
  Qed.

  Lemma map2_fst (v : Vector.t (T * V) n) (u : Vector.t U n):
    Vector.map2 (fun x y => fst (fst x, y)) v u = Vector.map (fun x => fst x) v.
    induction v; [rewrite (vinv0 u) | destruct (vinvS u) as [? [? ?]]; subst; simpl; rewrite IHv];
    simpl; try congruence. 
  Qed.

  Lemma map2_snd (v : Vector.t (T * V) n) (u : Vector.t U n):
    Vector.map2 (fun x y => snd (fst x, y)) v u = u.
    induction v; [rewrite (vinv0 u) | destruct (vinvS u) as [? [? ?]]; subst; simpl; rewrite IHv];
    simpl; try congruence. 
  Qed.

  Lemma map2_snd' (v : Vector.t T n) (u : Vector.t U n) :
    Vector.map2 (fun x y => snd (x, y)) v u = u.
  Proof.
    induction v.
    - rewrite (vinv0 u); eauto.
    - destruct (vinvS u) as [x [t ?]]; subst; simpl; rewrite IHv; eauto.
  Qed.

  Lemma map2_fst' (v : Vector.t T n) (u : Vector.t U n) :
    Vector.map2 (fun x y => fst (x, y)) v u = v.
  Proof.
    induction v.
    - rewrite (vinv0 u); eauto.
    - destruct (vinvS u) as [x [t ?]]; subst; simpl; rewrite IHv; eauto.
  Qed.
End FusionLemmas.