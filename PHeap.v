Require Import Logic.Eqdep.
Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import String.
Require Import QArith.
Require Import Qcanon.
Require Import Coq.Relations.Relations.

Require ClassicalFacts.
Require Export FunctionalExtensionality.
Require Export ProofIrrelevance.

Require Export Coq.ZArith.BinInt.
Require Export String.

Add LoadPath "../../src/cslsound".

Require Export Vbase Varith Vlistbase Vlist Basic.

Set Implicit Arguments.
Unset Strict Implicit.

Definition pheap' := Z -> option (Qc * Z).

Definition is_pheap (h : pheap') : Prop :=
  forall x, match h x with
    | None => True
    | Some (p, v) => 0 < p /\ p <= 1
  end.
Record pheap := Pheap { this :> pheap'; is_p : is_pheap this }.
Definition pdisj (h1 h2 : pheap') :=
  forall (x : Z), match h1 x, h2 x with
    | None, _ | _, None => True
    | Some (p1, v1), some (p2, v2) =>
      v1 = v2 /\ 0 < p1 + p2 /\ p1 + p2 <= 1
  end.

Definition phplus (h1 h2 : pheap') : pheap' :=
  fun x => match h1 x with
    | None => h2 x
    | Some (p1, v1) => 
      match h2 x with
        | None => h1 x
        | Some (p2, v2) => Some (p1 + p2, v1)
      end
  end.

Definition full_p : Qc := 1.
Definition emp_h : pheap' := fun (n : Z) => None.

Definition fpdom (h : pheap') : Prop :=
  forall (n : Z), match h n with
    | None => True
    | Some (p, v) => (p = full_p)%Qc
  end.

Lemma pdisjC : forall h1 h2, pdisj h1 h2 -> pdisj h2 h1.
Proof. 
  unfold pdisj, pheap'; intros h1 h2 hd x.
  specialize (hd x).
  destruct (h1 x), (h2 x); try tauto.
  destruct p as [? ?], p0 as [? ?].
  assert (q0 + q = q + q0) as heq by ring; rewrite heq.
  destruct hd as [? [? ?]]; repeat split; auto.
Qed.

Lemma pdisj_empty1 : forall (h : pheap), pdisj emp_h h.
  intros h; unfold emp_h, pdisj; simpl; eauto.
Qed.

Lemma pdisj_empty2 : forall (h : pheap), pdisj h emp_h.
  now unfold emp_h, pdisj; intros h x; destruct (this h x) as [[? ?] | ?].
Qed.

Definition ph_upd (h : pheap') (x : Z) (v : Z) : pheap' :=
  fun (x' : Z) => if Z.eq_dec x x' then Some (full_p, v) else h x'.

Lemma ph_upd_ph (h : pheap) (x : Z) (v : Z) : is_pheap (ph_upd h x v).
Proof.
  destruct h as [h ph]; simpl.
  unfold is_pheap, ph_upd; intros y; destruct (Z.eq_dec x y).
  - split; unfold Qclt, Qlt, Qcle, Qle, full_p; simpl; omega.
  - specialize (ph y); eauto.
Qed.

Definition ph_upd2 (h : pheap) (x : Z) (v : Z) : pheap :=
  @Pheap (ph_upd h x v) (ph_upd_ph h x v).

Definition empty_p := 0.

Lemma frac_contra1 : forall p : Qc, (p > empty_p)%Qc -> ~(full_p + p <= full_p)%Qc.
Proof.
  unfold full_p; intros p hp hcontra.
  apply (Qcle_minus_iff (1 + p) 1) in hcontra.
  assert (1 + - (1 + p) = -p) as h by ring; rewrite h in hcontra; clear h.
  apply Qcopp_le_compat in hcontra.
  assert (- -p = p) as h by ring; rewrite h in hcontra; clear h.
  assert (- 0 = 0) as h by ring; rewrite h in hcontra; clear h.
  apply Qclt_not_le in hp; tauto.
Qed.

Lemma frac_contra2 : forall p, p > empty_p -> ~(p + full_p <= 1).
Proof.
  intros ? ?; rewrite Qcplus_comm.
  auto using frac_contra1.
Qed.

Lemma pdisj_upd : forall (h h' : pheap) (x w v : Z), this h x = Some (full_p, w) -> 
  (pdisj (ph_upd h x v) h' <-> pdisj h h').
Proof.
  destruct h as [h iph].
  destruct h' as [h' iph'].
  unfold pdisj, ph_upd; ins.
  split. 
  - intros hp x0; pose proof (hp x0); pose proof (iph x0); pose proof (iph' x0).
    destruct (Z.eq_dec x x0), (h x0) as [[? ?] | ], (h' x0) as [[? ?] | ]; eauto.
    destruct H0 as [? [? ?]],  H2 as [? ?]; exfalso; eapply (@frac_contra1 q0); eauto.
  - intros hp x0; specialize (hp x0); specialize (iph x0); specialize (iph' x0).
    destruct (Z.eq_dec x x0); subst;
    destruct (h x0) as [[? ?] | ], (h' x0) as [[? ?] | ]; simpl; eauto;
    inversion H; subst.
    destruct hp as [? [? ?]], iph' as [? ?]; exfalso; eapply (@frac_contra1 q0); eauto.
Qed.

Lemma phplus_comm (h1 h2 : pheap) : pdisj h1 h2 -> phplus h1 h2 = phplus h2 h1.
Proof.
  destruct h1 as [h1 H1], h2 as [h2 H2]; simpl.
  intros hdisj; unfold is_pheap, pdisj, phplus in *; extensionality x.
  repeat (match goal with [H : forall _ : Z, _ |- _] => specialize (H x) end).
  destruct (h1 x) as [[? ?] | ], (h2 x) as [[? ?] | ]; eauto. 
  destruct hdisj as [? [? ?]].
  assert (q + q0 = q0 + q) by ring; congruence.
Qed.

Lemma plus_gt_0 : forall p1 p2 : Qc, 0 < p1 -> 0 < p2 -> 0 < p1 + p2.
Proof.
  intros p1 p2 h1 h2.
  assert (p2 < p1 + p2).
  { apply Qclt_minus_iff.
    cutrewrite (p1 + p2 + - p2 = p1); [eauto | ring]. }
  apply (Qclt_trans _ p2 _); eauto.
Qed.

Lemma gt_0_plus : forall p p1 : Qc, 0 < p1 -> p < p + p1.
Proof.
  intros p p1 h1.
  apply Qclt_minus_iff.
  cutrewrite (p + p1 + - p = p1); [eauto | ring].
Qed.

Lemma le1_weak : forall p p1 : Qc, 0 < p1 -> p + p1 <= 1 -> p <= 1.
Proof.
  intros p p1 h1 hp.
  apply Qclt_le_weak.
  apply (Qclt_le_trans _ (p + p1) _); [apply gt_0_plus; eauto | eauto].
Qed.

Lemma pdisj_padd (h1 h2 h3 : pheap) :
  pdisj h2 h3 -> pdisj h1 (phplus h2 h3) -> (pdisj h1 h2) /\ (pdisj h1 h3).
Proof.
  destruct h1 as [h1 H1], h2 as [h2 H2], h3 as [h3 H3]; simpl.
  unfold is_pheap, pdisj, phplus in *;
    intros disj23 disj123; split; intros x; 
    repeat (match goal with [H : forall _ : Z, _ |- _] => specialize (H x) end);
    destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |];
    destruct disj23 as [? [? ?]], disj123 as [? [? ?]], H1 as [? ?], H2 as [? ?], H3 as [? ?];
    repeat split; eauto using Qcplus_comm.

  - apply plus_gt_0; eauto.
  - cutrewrite (q + (q0 + q1) = (q + q0) + q1) in H7; [apply (@le1_weak _ q1); eauto | ring ].
  - congruence.
  - apply plus_gt_0; eauto.
  - cutrewrite (q + (q0 + q1) = (q + q1) + q0) in H7; [apply (@le1_weak _ q0); eauto | ring ].
Qed.

Lemma pdisjE1 (h1 h2 h3 : pheap) : pdisj h1 (phplus h2 h3) -> pdisj h2 h3 -> pdisj h1 h2.
Proof.
  destruct h1 as [h1 ph1], h2 as [h2 ph2], h3 as [h3 ph3]; simpl in *.
  unfold is_pheap, pdisj, phplus in *;
    intros h123 h23 x;
    repeat (match goal with [H : forall _ : Z, _ |- _] => specialize (H x) end).
  destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |],
                                                               ph1 as [? ?], ph2 as [? ?], ph3 as [? ?], h123 as [? [? ?]], h23 as [? [? ?]]; eauto.
  repeat split; eauto using plus_gt_0.
  cutrewrite (q + (q0 + q1) = (q + q0) + q1) in H7; [apply (@le1_weak _ q1); eauto | ring ].
Qed.

Lemma pdisjE2 (h1 h2 h3 : pheap) :
  pdisj h1 (phplus h2 h3) -> pdisj h2 h3 -> pdisj h1 h3.
Proof.
  destruct h1 as [h1 ph1], h2 as [h2 ph2], h3 as [h3 ph3]; simpl in *.
  unfold is_pheap, pdisj, phplus in *;
    intros h123 h23 x;
    repeat (match goal with [H : forall _ : Z, _ |- _] => specialize (H x) end).
  destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |],
                                                               ph1 as [? ?], ph2 as [? ?], ph3 as [? ?], h123 as [? [? ?]], h23 as [? [? ?]]; eauto.
  repeat split; eauto using plus_gt_0.
  - congruence.
  - cutrewrite (q + (q0 + q1) = (q + q1) + q0) in H7; [apply (@le1_weak _ q0); eauto | ring ].
Qed.

Lemma pdisj_padd_comm (h1 h2 h3 : pheap) : pdisj h2 (phplus h1 h3) -> pdisj h1 h3 -> 
                                           pdisj h1 (phplus h2 h3).
Proof.
  destruct h1 as [h1 ph1], h2 as [h2 ph2], h3 as [h3 ph3]; simpl in *.
  unfold is_pheap, pdisj, phplus in *;
    intros h123 h23 x;
    repeat (match goal with [H : forall _ : Z, _ |- _] => specialize (H x) end).
  destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |],
    ph1 as [? ?], ph2 as [? ?], ph3 as [? ?], h123 as [? [? ?]], h23 as [? [? ?]]; eauto.
  - cutrewrite (q + (q0 + q1) = q0 + (q + q1)); [ | ring].
    repeat split; eauto.
  - cutrewrite (q + q0 = q0 + q); [ | ring];
    repeat split; eauto.
Qed.

Lemma pdisj_padd_expand (h1 h2 h3 : pheap) : 
  pdisj h1 h2 -> (pdisj (phplus h1 h2) h3 <-> (pdisj h1 (phplus h2 h3) /\ pdisj h2 h3)).
Proof.
  destruct h1 as [h1 ph1], h2 as [h2 ph2], h3 as [h3 ph3]; simpl in *.
  unfold is_pheap, pdisj, phplus in *;
    intros h12; split; [intros H; split; intros x | intros [H1 H2] x];
    repeat (match goal with [H : forall _ : Z, _ |- _] => specialize (H x) end);
    destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |],
                ph1 as [? ?], ph2 as [? ?], ph3 as [? ?], h12 as [? [? ?]];
    des; eauto;
    repeat split; try congruence; eauto; 
    try rewrite (Qcplus_assoc _ _ _); try rewrite (Qcplus_comm _ _); 
    eauto using plus_gt_0.
  - cutrewrite (q1 + (q + q0) = q + q0 + q1); [eauto | ring].
  - cutrewrite (q + q0 + q1 = (q1 + q0) + q) in H10; [apply (@le1_weak _ q); eauto | ring].
  - cutrewrite (q1 + (q + q0) = q + (q0 + q1)); [eauto | ring].
Qed.

Lemma padd_assoc (h1 h2 h3 : pheap) :
  pdisj h1 (phplus h2 h3) -> pdisj h2 h3 -> phplus (phplus h1 h2) h3 = phplus h1 (phplus h2 h3).
Proof.
  destruct h1 as [h1 ph1], h2 as [h2 ph2], h3 as [h3 ph3]; simpl in *.
  unfold is_pheap, pdisj, phplus in *;
    intros h123 h23; extensionality x;
    repeat (match goal with [H : forall _ : Z, _ |- _] => specialize (H x) end);
    destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |];
    des; eauto.
  cutrewrite (q + q0 + q1 = q + (q0 + q1)); [eauto | ring].
Qed.

Lemma padd_left_comm (h1 h2 h3 : pheap) :
  pdisj h1 (phplus h2 h3) -> pdisj h2 h3 -> phplus h1 (phplus h2 h3) = phplus h2 (phplus h1 h3).
Proof.
  destruct h1 as [h1 ph1], h2 as [h2 ph2], h3 as [h3 ph3]; simpl in *.
  unfold is_pheap, pdisj, phplus in *;
    intros h123 h23; extensionality x;
    repeat (match goal with [H : forall _ : Z, _ |- _] => specialize (H x) end);
    destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |];
    des; eauto.
  - cutrewrite (q + (q0 + q1) = q0 + (q + q1)); [congruence | ring].
  - cutrewrite (q + q0 = q0 + q); [congruence | ring].
Qed.

Lemma padd_cancel (h1 h2 h3 : pheap) :
  phplus h1 h2 = phplus h1 h3 -> pdisj h1 h2 -> pdisj h1 h3 -> h2 = h3.
Proof.
  destruct h1 as [h1 ph1], h2 as [h2 ph2], h3 as [h3 ph3]; simpl in *.
  intros heq h12 h13.
  assert (h2 = h3).
  unfold is_pheap, pdisj, phplus in *;
    extensionality x; pose proof  (equal_f heq x) as heq'; simpl in *; clear heq;
    repeat (match goal with [H : forall _ : Z, _ |- _] => specialize (H x) end);
    destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |];
    des; eauto; try congruence.
  - remember (q + q0) as q0'; remember (q + q1) as q1'.
    inversion heq'. subst.
    assert (q + q0 - q = q + q1 - q) by (rewrite H0; eauto).
    cutrewrite (q + q0 - q = q0) in H; [| ring].
    cutrewrite (q + q1 - q = q1) in H; [| ring].
    congruence.
  - remember (q + q0) as q'.
    inversion heq'; subst.
    assert (q + q0 - q = q - q) by (rewrite H0; eauto).
    cutrewrite (q + q0 - q = q0) in H; [| ring].
    cutrewrite (q - q = 0) in H; [| ring].
    rewrite H in ph2.
    inversion ph2.
  - inversion heq'.
    assert (q - q = (q + q0) - q) by (rewrite H0 at 1; eauto).
    cutrewrite (q - q = 0) in H; [| ring].
    cutrewrite (q + q0 - q = q0) in H; [| ring].
    rewrite <- H in ph3; inversion ph3.
  - subst; cutrewrite (ph2 = ph3); [eauto | apply proof_irrelevance ].
Qed.

Corollary padd_cancel2 (h1 h2 h3 : pheap) :
  phplus h2 h1 = phplus h3 h1 -> pdisj h2 h1 -> pdisj h3 h1 -> h2 = h3.
Proof.
  Hint Resolve pdisjC.
  intros.
  rewrite (@phplus_comm h2 h1), (@phplus_comm h3 h1) in H; eauto.
  eapply padd_cancel; eauto.
Qed.

Definition ptoheap (ph : pheap') (h : heap) : Prop :=
  forall (x : Z), match ph x with
                    | None => h x = None
                    | Some (p, v) => p = full_p /\ h x = Some v
                  end.

Lemma ptoD (ph1 ph2 : pheap') (h : heap):
  ptoheap ph1 h -> ptoheap ph2 h -> ph1 = ph2.
Proof.
  (*    destruct ph1 as [h1 ph1], ph2 as [h2 ph2]; simpl in *.*)
  intros pto1 pto2.
  unfold is_pheap, pdisj, phplus, ptoheap in *; extensionality x; simpl in *;
  repeat (match goal with [H : forall _ : Z, _ |- _] => specialize (H x) end);
  destruct (ph1 x) as [[? ?] |], (ph2 x) as [[? ?] |];
  des; eauto; try congruence.
Qed.

Lemma pdisj_is_pheap (h1 h2 : pheap) :
  pdisj h1 h2 -> is_pheap (phplus h1 h2).
Proof.
  intros dis12 x; specialize (dis12 x); specialize (is_p h1 x); specialize (is_p h2 x).
  unfold phplus; destruct (this h1 x) as [[q1 v1] | ], (this h2 x) as [[q2 v2] | ]; des; eauto.
Qed.

Definition phplus_pheap (h1 h2 : pheap) (H : pdisj h1 h2) : pheap := Pheap (pdisj_is_pheap H).