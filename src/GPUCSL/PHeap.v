Require Import Logic.Eqdep.
Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import String.
Require Import QArith.
Require Import Qcanon.
Require Import Coq.Relations.Relations.
Require Import MyVector.

Require ClassicalFacts.
Require Export FunctionalExtensionality.
Require Export ProofIrrelevance.

Require Export Coq.ZArith.BinInt.

(* Require Export Vbase Varith Vlistbase Vlist Basic.*)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Classes.EquivDec.

Inductive PL := Shared | Global.

Inductive loc := Loc (pl : PL) (l : Z).

Inductive val :=
| VZ (n : Z)
| VPtr (l : loc).

Class eq_type A :=
  { eq_dec : forall x y : A, {x = y} + {x <> y}}.

Section Loc.
Variable (loc : Type).
Context {loc_eq_dec : eq_type loc}.

Definition gen_pheap' := loc -> option (Qc * val).

Definition is_pheap (h : gen_pheap') : Prop :=
  forall x, match h x with
    | None => True
    | Some (p, v) => 0 < p /\ p <= 1
  end.
Record gen_pheap := Pheap { this :> gen_pheap'; is_p : is_pheap this }.
Definition pdisj (h1 h2 : gen_pheap') :=
  forall (x : loc), match h1 x, h2 x with
    | None, _ | _, None => True
    | Some (p1, v1), Some (p2, v2) =>
      v1 = v2 /\ 0 < p1 + p2 /\ p1 + p2 <= 1
  end.

Definition phplus (h1 h2 : gen_pheap') : gen_pheap' :=
  fun x => match h1 x with
    | None => h2 x
    | Some (p1, v1) => 
      match h2 x with
        | None => h1 x
        | Some (p2, v2) => Some (p1 + p2, v1)
      end
  end.

Definition full_p : Qc := 1.
Definition emp_h : gen_pheap' := fun (n : loc) => None.

Definition fpdom (h : gen_pheap') : Prop :=
  forall (n : loc), match h n with
    | None => True
    | Some (p, v) => (p = full_p)%Qc
  end.

Lemma pdisjC : forall h1 h2, pdisj h1 h2 -> pdisj h2 h1.
Proof. 
  unfold pdisj, gen_pheap'; intros h1 h2 hd x.
  specialize (hd x).
  destruct (h1 x), (h2 x); try tauto.
  destruct p as [? ?], p0 as [? ?].
  assert (q0 + q = q + q0) as heq by ring; rewrite heq.
  destruct hd as [? [? ?]]; repeat split; auto.
Qed.

Lemma pdisj_empty1 : forall (h : gen_pheap), pdisj emp_h h.
  intros h; unfold emp_h, pdisj; simpl; eauto.
Qed.

Lemma pdisj_empty2 : forall (h : gen_pheap), pdisj h emp_h.
  now unfold emp_h, pdisj; intros h x; destruct (this h x) as [[? ?] | ?].
Qed.

(* Definition loc_eq_dec (l1 l2 : loc) : {l1 = l2} + {l1 <> l2}. *)
(*   repeat decide equality. *)
(* Qed. *)

Definition ph_upd (h : gen_pheap') (x : loc) (v : val) : gen_pheap' :=
  fun (x' : loc) => if eq_dec x x' then Some (full_p, v) else h x'.

Lemma ph_upd_ph (h : gen_pheap) (x : loc) (v : val) : is_pheap (ph_upd h x v).
Proof.
  destruct h as [h ph]; simpl.
  unfold is_pheap, ph_upd; intros y; destruct (eq_dec x y).
  - split; unfold Qclt, Qlt, Qcle, Qle, full_p; simpl; omega.
  - specialize (ph y); eauto.
Qed.

Definition ph_upd2 (h : gen_pheap) (x : loc) (v : val) : gen_pheap :=
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

Lemma pdisj_upd : forall (h h' : gen_pheap) (x : loc) (v w : val), this h x = Some (full_p, w) -> 
  (pdisj (ph_upd h x v) h' <-> pdisj h h').
Proof.
  destruct h as [h iph].
  destruct h' as [h' iph'].
  unfold pdisj, ph_upd; intros; simpl in *.
  split. 
  - intros hp x0; pose proof (hp x0); pose proof (iph x0); pose proof (iph' x0).
    destruct (eq_dec x x0), (h x0) as [[? ?] | ], (h' x0) as [[? ?] | ]; eauto.
    destruct H0 as [? [? ?]],  H2 as [? ?]; exfalso; eapply (@frac_contra1 q0); eauto.
  - intros hp x0; specialize (hp x0); specialize (iph x0); specialize (iph' x0).
    destruct (eq_dec x x0); unfold "===" in *; subst;
    destruct (h x0) as [[? ?] | ], (h' x0) as [[? ?] | ]; simpl; eauto;
    inversion H; subst.
    destruct hp as [? [? ?]], iph' as [? ?]; exfalso; eapply (@frac_contra1 q0); eauto.
Qed.

Lemma phplus_comm (h1 h2 : gen_pheap') : pdisj h1 h2 ->phplus h1 h2 = phplus h2 h1.
Proof.
  (* destruct h1 as [h1 H1], h2 as [h2 H2]; simpl. *)
  intros hdisj;unfold is_pheap, pdisj, phplus in *; extensionality x.
  repeat (match goal with [H : forall _: loc, _ |- _] => specialize (H x) end).
  destruct (h1 x) as [[? ?] | ], (h2 x) as [[? ?] | ]; eauto. 
  (* destruct hdisj as [? [? ?]]. *)
  assert (q + q0 = q0 + q) by ring; destruct hdisj; congruence.
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

Lemma pdisj_padd (h1 h2 h3 : gen_pheap) :
  pdisj h2 h3 -> pdisj h1 (phplus h2 h3) -> (pdisj h1 h2) /\ (pdisj h1 h3).
Proof.
  destruct h1 as [h1 H1], h2 as [h2 H2], h3 as [h3 H3]; simpl.
  unfold is_pheap, pdisj, phplus in *; intros disj23 disj123; split; intros x;
  repeat (match goal with [H : forall _ : loc, _ |- _] => specialize (H x) end);
    destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |];
    destruct disj23 as [? [? ?]], disj123 as [? [? ?]], H1 as [? ?], H2 as [? ?], H3 as [? ?];
    repeat split; eauto using Qcplus_comm.
  - apply plus_gt_0; eauto.
  - cutrewrite (q + (q0 + q1) = (q + q0) + q1) in H7; [apply (@le1_weak _ q1); eauto | ring ].
  - congruence.
  - apply plus_gt_0; eauto.
  - cutrewrite (q + (q0 + q1) = (q + q1) + q0) in H7; [apply (@le1_weak _ q0); eauto | ring ].
Qed.

Lemma pdisjE1 (h1 h2 h3 : gen_pheap) : pdisj h1 (phplus h2 h3) -> pdisj h2 h3 -> pdisj h1 h2.
Proof.
  destruct h1 as [h1 ph1], h2 as [h2 ph2], h3 as [h3 ph3]; simpl in *.
  unfold is_pheap, pdisj, phplus in *;
    intros h123 h23 x;
    repeat (match goal with [H : forall _ : loc, _ |- _] => specialize (H x) end).
  destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |],
           ph1 as [? ?], ph2 as [? ?], ph3 as [? ?], h123 as [? [? ?]], h23 as [? [? ?]]; eauto.
  repeat split; eauto using plus_gt_0.
  cutrewrite (q + (q0 + q1) = (q + q0) + q1) in H7; [apply (@le1_weak _ q1); eauto | ring ].
Qed.

Lemma pdisjE2 (h1 h2 h3 : gen_pheap) :
  pdisj h1 (phplus h2 h3) -> pdisj h2 h3 -> pdisj h1 h3.
Proof.
  destruct h1 as [h1 ph1], h2 as [h2 ph2], h3 as [h3 ph3]; simpl in *.
  unfold is_pheap, pdisj, phplus in *;
    intros h123 h23 x;
    repeat (match goal with [H : forall _ : loc, _ |- _] => specialize (H x) end).
  destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |],
              ph1 as [? ?], ph2 as [? ?], ph3 as [? ?], h123 as [? [? ?]], h23 as [? [? ?]]; eauto.
  repeat split; eauto using plus_gt_0.
  - congruence.
  - cutrewrite (q + (q0 + q1) = (q + q1) + q0) in H7; [apply (@le1_weak _ q0); eauto | ring ].
Qed.

Ltac des_conj := 
  repeat (match goal with [H : _ /\ _ |- _] => destruct H end).

Lemma pdisj_padd_comm (h1 h2 h3 : gen_pheap) : pdisj h2 (phplus h1 h3) -> pdisj h1 h3 -> 
                                           pdisj h1 (phplus h2 h3).
Proof.
  destruct h1 as [h1 ph1], h2 as [h2 ph2], h3 as [h3 ph3]; simpl in *.
  unfold is_pheap, pdisj, phplus in *;
    intros h123 h23 x;
    repeat (match goal with [H : forall _ : loc, _ |- _] => specialize (H x) end).
  destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |],
    ph1 as [? ?], ph2 as [? ?], ph3 as [? ?], h123 as [? [? ?]], h23 as [? [? ?]]; eauto.
  - cutrewrite (q + (q0 + q1) = q0 + (q + q1)); [ | ring].
    repeat split; eauto.
  - cutrewrite (q + q0 = q0 + q); [ | ring];
    repeat split; eauto.
Qed.

Lemma pdisj_padd_expand (h1 h2 h3 : gen_pheap) : 
  pdisj h1 h2 -> (pdisj (phplus h1 h2) h3 <-> (pdisj h1 (phplus h2 h3) /\ pdisj h2 h3)).
Proof.
  destruct h1 as [h1 ph1], h2 as [h2 ph2], h3 as [h3 ph3]; simpl in *.
  unfold is_pheap, pdisj, phplus in *;
    intros h12; split; [intros H; split; intros x | intros [H1 H2] x];
    repeat (match goal with [H : forall _ : loc, _ |- _] => specialize (H x) end);
    destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |],
                ph1 as [? ?], ph2 as [? ?], ph3 as [? ?], h12 as [? [? ?]];
    des_conj; eauto;
    repeat split; try congruence; eauto; 
    try rewrite (Qcplus_assoc _ _ _); try rewrite (Qcplus_comm _ _); 
    eauto using plus_gt_0.
  - cutrewrite (q1 + (q + q0) = q + q0 + q1); [eauto | ring].
  - cutrewrite (q + q0 + q1 = (q1 + q0) + q) in H10; [apply (@le1_weak _ q); eauto | ring].
  - cutrewrite (q1 + (q + q0) = q + (q0 + q1)); [eauto | ring].
Qed.

Lemma padd_assoc (h1 h2 h3 : gen_pheap') :
  (* pdisj h1 (phplus h2 h3) -> pdisj h2 h3 ->  *)phplus (phplus h1 h2) h3 = phplus h1 (phplus h2 h3).
Proof.
  (* destruct h1 as [h1 ph1], h2 as [h2 ph2], h3 as [h3 ph3]; simpl in *. *)
  (* unfold is_pheap, pdisj, phplus in *; *)
  (*   intros h123 h23; extensionality x; *)
  (*   repeat (match goal with [H : forall _ : Z, _ |- _] => specialize (H x) end); *)
  (*   destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |]; *)
  (*   des_conj; eauto. *)
  (* cutrewrite (q + q0 + q1 = q + (q0 + q1)); [eauto | ring]. *)
  extensionality l; unfold phplus; simpl.
  destruct (h1 l) as [[? ?] |], (h2 l) as [[? ?] |], (h3 l) as [[? ?] |]; eauto.
  cutrewrite (q + q0 + q1 = q + (q0 + q1)); [eauto | ring].
Qed.

Lemma padd_left_comm (h1 h2 h3 : gen_pheap) :
  pdisj h1 (phplus h2 h3) -> pdisj h2 h3 -> phplus h1 (phplus h2 h3) = phplus h2 (phplus h1 h3).
Proof.
  destruct h1 as [h1 ph1], h2 as [h2 ph2], h3 as [h3 ph3]; simpl in *.
  unfold is_pheap, pdisj, phplus in *;
    intros h123 h23; extensionality x;
    repeat (match goal with [H : forall _ : loc, _ |- _] => specialize (H x) end);
    destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |];
    des_conj; eauto.
  - cutrewrite (q + (q0 + q1) = q0 + (q + q1)); [congruence | ring].
  - cutrewrite (q + q0 = q0 + q); [congruence | ring].
Qed.

Lemma padd_cancel (h1 h2 h3 : gen_pheap) :
  phplus h1 h2 = phplus h1 h3 -> pdisj h1 h2 -> pdisj h1 h3 -> h2 = h3.
Proof.
  destruct h1 as [h1 ph1], h2 as [h2 ph2], h3 as [h3 ph3]; simpl in *.
  intros heq h12 h13.
  assert (h2 = h3).
  unfold is_pheap, pdisj, phplus in *;
    extensionality x; pose proof  (equal_f heq x) as heq'; simpl in *; clear heq;
    repeat (match goal with [H : forall _ : loc, _ |- _] => specialize (H x) end);
    destruct (h1 x) as [[? ?] |], (h2 x) as [[? ?] |], (h3 x) as [[? ?] |];
    des_conj; eauto; try congruence.
  - remember (q + q0) as q0'; remember (q + q1) as q1'.
    inversion heq'. subst.
    assert (q + q0 - q = q + q1 - q) by (rewrite H12; eauto).
    cutrewrite (q + q0 - q = q0) in H2; [| ring].
    cutrewrite (q + q1 - q = q1) in H2; [| ring].
    congruence.
  - remember (q + q0) as q'.
    inversion heq'; subst.
    assert (q + q0 - q = q - q) by (rewrite H7; eauto).
    cutrewrite (q + q0 - q = q0) in H; [| ring].
    cutrewrite (q - q = 0) in H; [| ring].
    rewrite H in H2. 
    inversion H2.
  - inversion heq'.
    assert (q - q = (q + q0) - q) by (rewrite H7 at 1; eauto).
    cutrewrite (q - q = 0) in H6; [| ring].
    cutrewrite (q + q0 - q = q0) in H6; [| ring].
    rewrite <- H6 in H2. inversion H2.
  - subst; cutrewrite (ph2 = ph3); [eauto | apply proof_irrelevance ].
Qed.

Hint Resolve pdisjC.

Corollary padd_cancel2 (h1 h2 h3 : gen_pheap) :
  phplus h2 h1 = phplus h3 h1 -> pdisj h2 h1 -> pdisj h3 h1 -> h2 = h3.
Proof.
  intros.
  rewrite (@phplus_comm h2 h1), (@phplus_comm h3 h1) in H; eauto.
  eapply padd_cancel; eauto.
Qed.

Definition heap := loc -> option val.

Definition ptoheap (ph : gen_pheap') (h : heap) : Prop :=
  forall (x : loc), match ph x with
                    | None => h x = None
                    | Some (p, v) => p = full_p /\ h x = Some v
                  end.

Lemma ptoD (ph1 ph2 : gen_pheap') (h : heap):
  ptoheap ph1 h -> ptoheap ph2 h -> ph1 = ph2.
Proof.
  (*    destruct ph1 as [h1 ph1], ph2 as [h2 ph2]; simpl in *.*)
  intros pto1 pto2.
  unfold is_pheap, pdisj, phplus, ptoheap in *; extensionality x; simpl in *;
  repeat (match goal with [H : forall _ : loc, _ |- _] => specialize (H x) end);
  destruct (ph1 x) as [[? ?] |], (ph2 x) as [[? ?] |];
  intuition; eauto; try congruence.
Qed.

Lemma pdisj_is_pheap (h1 h2 : gen_pheap) :
  pdisj h1 h2 -> is_pheap (phplus h1 h2).
Proof.
  intros dis12 x; specialize (dis12 x); specialize (is_p h1 x); specialize (is_p h2 x).
  unfold phplus; destruct (this h1 x) as [[q1 v1] | ], (this h2 x) as [[q2 v2] | ]; intuition; eauto.
Qed.

Definition phplus_pheap (h1 h2 : gen_pheap) (H : pdisj h1 h2) : gen_pheap := Pheap (pdisj_is_pheap H).

Definition htop' (h : heap) : gen_pheap' :=
  fun (x : loc) => 
    match h x with
      | None => None
      | Some v => Some (full_p, v)
    end.

Lemma htop_is_pheap (h : heap) : is_pheap (htop' h).
Proof.
  intros x; unfold is_pheap, htop', full_p; destruct (h x); repeat split; eauto.
  unfold Qcle; unfold Qle; simpl; omega.
Qed.

Definition htop (h : heap) : gen_pheap :=
  Pheap (htop_is_pheap h).

Lemma ptoheap_htop (h : heap) : ptoheap (htop h) h.
Proof.
  intros x; unfold htop,htop'; simpl; destruct (h x); eauto.
Qed.

Lemma pheap_eq (ph1 ph2 : gen_pheap') (is_p1 : is_pheap ph1) (is_p2 : is_pheap ph2) :
  ph1 = ph2 -> Pheap is_p1 = Pheap is_p2.
Proof.
  destruct 1.
  cutrewrite (is_p1 = is_p2); [eauto | apply proof_irrelevance ].
Qed.

Lemma ptoheap_eq (ph : gen_pheap') (h : heap) : ptoheap ph h -> ph = htop h.
Proof.
  intros ptoheap.
  unfold htop, htop' in *; (*destruct ph as [ph iph]; apply pheap_eq;*) extensionality x.
  specialize (ptoheap x); simpl in *(* ; specialize (iph x) *).
  simpl in *; destruct (ph x) as [[? ?]|], (h x) as [? |];
  repeat match goal with [H : _ /\ _ |- _ ] => destruct H end;
  try tauto; try congruence.
Qed.

Lemma pheap_disj_eq (h1 h2 : gen_pheap) (v : loc) (v1 v2 : val) (q1 q2 : Qc) :
  pdisj h1 h2 -> this h1 v = Some (q1, v1) -> this h2 v = Some (q2, v2) -> v1 = v2.
Proof.
  intros hdis h1v h2v.
  specialize (hdis v); rewrite h1v, h2v in hdis; intuition; eauto.
Qed.

Lemma pheap_disj_disj (h1 h2 : gen_pheap) (v1 v2 : loc) (v1' v2' v1'' v2'' : val) :
  pdisj h1 h2 -> this h1 v1 = Some (full_p, v1') -> this h2 v2 = Some (full_p, v2') ->
  pdisj (ph_upd2 h1 v1 v1'') (ph_upd2 h2 v2 v2'').
Proof.
  intros hdis h1v h2v.
  apply (pdisj_upd (ph_upd2 h2 v2 v2'') v1'' h1v).
  apply pdisjC.
  unfold ph_upd2; simpl.
  apply (pdisj_upd h1 v2'' h2v); eauto.
Qed.

Import VectorNotations.

Lemma emp_is_heap : is_pheap emp_h. unfold is_pheap, emp_h; eauto. Qed.
Definition emp_ph : gen_pheap := Pheap emp_is_heap.

Lemma emp_is_emp (h : gen_pheap) :
  (forall v : loc, this h v = None) -> h = emp_ph.
Proof.
  destruct h as [h ?]; unfold emp_ph; intros hsat.
  assert (h = emp_h) by (extensionality x; specialize (hsat x); simpl in *; eauto).
  pose proof (emp_is_heap).
  cutrewrite (emp_is_heap = H0); [ | apply proof_irrelevance].
  destruct H.
  cutrewrite (is_p0 = H0); [ | apply proof_irrelevance].
  eauto.
Qed.


Inductive disj_eq : forall (n : nat), Vector.t gen_pheap n -> gen_pheap -> Prop :=
| eq_nil  : disj_eq [] emp_ph
| eq_cons : forall (n : nat) (hs : Vector.t gen_pheap n) (ph h : gen_pheap) (hdis : pdisj h ph),
              disj_eq hs ph -> disj_eq (h :: hs) (Pheap (pdisj_is_pheap hdis)).

Lemma disjeq_disj1 (n : nat) (h h' : gen_pheap) (hs : Vector.t gen_pheap n)
      (diseq : disj_eq hs h) (i : Fin.t n) :
  pdisj h' h -> pdisj h' hs[@i].
Proof.
  intros hdisj; induction diseq; [inversion i|].
  assert (pdisj h' h /\ pdisj h' ph) by (apply pdisj_padd; eauto).
  destruct (finvS i) as [? | [i' ?]]; subst; simpl in *; try tauto.
  apply IHdiseq; tauto.
Qed.

Lemma disjeq_disj (n : nat) (h : gen_pheap) (hs : Vector.t gen_pheap n) (diseq : disj_eq hs h) 
      (i j : Fin.t n) :
  i <> j -> pdisj (Vector.nth hs i) (Vector.nth hs j).
Proof.
  induction diseq; [inversion i |].
  intros hneq; destruct (finvS i) as [? | [i' ?]], (finvS j) as [? | [j' ?]]; subst; 
  try congruence; simpl.
  - eapply disjeq_disj1; eauto.
  - apply pdisjC; eapply disjeq_disj1; eauto.
  - apply IHdiseq. intros Hcontra; subst; tauto. 
Qed.

Lemma disj_eq_fun (n : nat) (hs : Vector.t gen_pheap n) (h h' : gen_pheap) :
  disj_eq hs h -> disj_eq hs h' -> h = h'.
Proof.
  revert n h h' hs; induction n; intros h h' hs hdis hdis'.
  - rewrite (vinv0 hs) in *; inversion hdis; inversion hdis'; subst; eauto.
  - destruct (vinvS hs) as [h0 [hs' ?]]; subst; inversion hdis; inversion hdis'; 
    clear hdis hdis'; subst.
    repeat (match goal with [ H : existT _ _ _ = existT _ _ _ |- _] => 
                            apply inj_pair2 in H; subst end).
    apply pheap_eq; rewrite (IHn ph0 ph hs' H8 H3); eauto.
Qed.

Lemma disj_exclude (n : nat) (hs : Vector.t gen_pheap n) (h h' : gen_pheap) (i : Fin.t n) :
  disj_eq hs h -> disj_eq (replace hs i emp_ph) h' -> pdisj hs[@i] h' /\ this h = phplus hs[@i] h'.
Proof.
  revert hs h h' i; induction n; 
  intros hs h h' i heq heq'; [inversion i|].
  destruct (vinvS hs) as [h0 [hs0 ?]]; subst.
  inversion heq; inversion heq';  
  repeat (match goal with [ H : existT _ _ _ = existT _ _ _ |- _] => 
                          apply inj_pair2 in H; subst end); subst; simpl in *; subst.
  destruct (finvS i) as [? | [i' ?]]; subst; simpl in *;
  inversion H5; clear H5; subst; apply inj_pair2 in H1; subst.
  - cutrewrite (phplus emp_ph ph0 = ph0); [ | extensionality x; unfold phplus; simpl; eauto].
    rewrite (disj_eq_fun H6 H3); eauto.
  - pose proof (IHn _ _ _ _ H3 H6) as IH.
    rewrite phplus_comm; eauto; split; destruct IH; subst.
    + apply pdisj_padd_expand; eauto.
      rewrite <-H0; eauto.
    + rewrite (phplus_comm (pdisjC hdis0)); rewrite padd_left_comm; eauto.
      rewrite <-H0; eauto.
      rewrite (phplus_comm hdis0); apply pdisj_padd_expand; eauto.
      rewrite <-H0; eauto.
Qed.

Lemma disj_weak (n : nat) (hs : Vector.t gen_pheap n) (h h' h'': gen_pheap) (i : Fin.t n) :
  disj_eq hs h -> pdisj h'' h -> disj_eq (replace hs i emp_ph) h' -> pdisj h'' h'.
  revert h h' h''; generalize dependent n.
  induction n; intros hs i h h' h'' heq hdis heq'; [inversion i |].
  destruct (vinvS hs) as [h0 [hs0 ?]]; subst.
  destruct (finvS i) as [? | [i' ?]]; subst; simpl in *.
  - inversion heq; clear heq; subst. apply inj_pair2 in H2; subst; simpl in *.
    apply pdisj_padd in hdis; eauto.
    inversion heq'; clear heq'; subst. apply inj_pair2 in H2; subst; simpl in *.
    cutrewrite ((phplus emp_h ph0) = ph); [tauto | ].
    extensionality x; unfold phplus; simpl; rewrite (disj_eq_fun H4 H3); eauto.
  - inversion heq; inversion heq'; clear heq heq';
    repeat (match goal with [ H : existT _ _ _ = existT _ _ _ |- _] => 
                            apply inj_pair2 in H; subst end); subst; simpl in *.
    pose proof (disj_exclude H3 H8) as [hdall heq]; rewrite heq in *.
    rewrite padd_left_comm in hdis; eauto.
    cutrewrite (phplus h0 ph0 = this (Pheap (pdisj_is_pheap hdis1))) in hdis; [ | simpl; eauto].
    apply pdisj_padd in hdis; simpl in *; try tauto.
    apply pdisjC, pdisj_padd_expand; eauto; split; eauto.
    rewrite phplus_comm; eauto.
Qed.

Lemma disj_exclude_exists (n : nat) (hs : Vector.t gen_pheap n) (h : gen_pheap) (i : Fin.t n) :
  disj_eq hs h -> exists h', disj_eq (Vector.replace hs i emp_ph) h'.
Proof.
  revert hs h i; induction n; 
  intros hs h i heq; [inversion i|].
  destruct (vinvS hs) as [h0 [hs0 ?]]; subst.
  inversion heq; 
    repeat (match goal with [ H : existT _ _ _ = existT _ _ _ |- _] => 
                            apply inj_pair2 in H; subst end); subst; simpl in *; subst.
  destruct (finvS i) as [? | [i' ?]]; subst; simpl in *.
  - assert (pdisj emp_ph ph) as hph by (unfold pdisj, emp_ph; intros x; simpl; eauto).
    exists (Pheap (pdisj_is_pheap hph)).
    apply (eq_cons hph H3).
  - destruct (IHn _ _ i' H3) as [ph' H].
    destruct (disj_exclude H3 H).
    assert (pdisj h0 ph') by apply (disj_weak H3 hdis H ).
    exists (Pheap (pdisj_is_pheap H2)).
    apply (eq_cons H2 H).
Qed.

Lemma disj_tid (n : nat) (hs : Vector.t gen_pheap n) (h : gen_pheap) (i : Fin.t n):
  disj_eq hs h -> exists h', disj_eq (Vector.replace hs i emp_ph) h' /\ 
                             pdisj hs[@i] h' /\ phplus hs[@i] h' = h.
Proof.
  intros hdeq.
  destruct (disj_exclude_exists i hdeq) as [h' ?].
  exists h'; split; eauto.
  split; destruct (disj_exclude hdeq H); eauto; try congruence.
Qed.

Lemma disj_upd (n : nat) (hs : Vector.t gen_pheap n) (i : Fin.t n) (h hq : gen_pheap):
  disj_eq (replace hs i emp_ph) h -> 
  pdisj hq h ->
  exists h', 
    disj_eq (replace hs i hq) h' /\ phplus hq h = h'.
Proof.
  revert hs h i hq; induction n; 
  intros hs h i hq heq hdis; [inversion i|].
  destruct (vinvS hs) as [h0 [hs0 ?]]; subst.
  inversion heq; subst. apply inj_pair2 in H0; subst.
  destruct (finvS i) as [? | [i' ?]]; simpl in *; subst; inversion H0; subst; simpl in *.
  - cutrewrite (phplus emp_h ph = ph) in hdis; [ | unfold phplus, emp_h; extensionality x; eauto].
    exists (Pheap (pdisj_is_pheap hdis)); simpl.
    split; [constructor; eauto | ].
    cutrewrite (phplus emp_h ph = ph); [eauto | unfold phplus, emp_h; extensionality x; eauto].
  - apply inj_pair2 in H3; subst.
    apply pdisjC in hdis; eapply pdisj_padd_expand in hdis; eauto.
    destruct hdis as [hdis hd].
    assert (pdisj h0 (Pheap (pdisj_is_pheap hd))) as dis' by (simpl; eauto).
    exists (Pheap (pdisj_is_pheap dis')); split; eauto.
    + econstructor.
      destruct (IHn _ _ _ _ H1 (pdisjC hd)) as [h' [hdeq pheq]].
      rewrite phplus_comm in pheq; eauto.
      cutrewrite ( Pheap (pdisj_is_pheap hd) = h'); 
        [eauto | destruct h'; apply pheap_eq; simpl in *; eauto].
    + simpl. rewrite padd_left_comm, (@phplus_comm ph hq); eauto.
      apply pdisjC, pdisj_padd_expand; eauto.
Qed.

Lemma disj_eq_each_disj (n : nat) (hs1 hs2 : Vector.t gen_pheap n) (h1 h2 : gen_pheap) :
  disj_eq hs1 h1 -> disj_eq hs2 h2 -> pdisj h1 h2 -> 
  (forall i : Fin.t n, pdisj hs1[@i] hs2[@i]).
  revert h1 h2; generalize dependent n; induction n as [|n]; 
  intros hs1 hs2 h1 h2 hdeq1 hdeq2 hdis i; [inversion i|].
  destruct (vinvS hs1) as [hh1 [hs1' ?]], (vinvS hs2) as [hh2 [hs2' ?]]; subst.
  inversion hdeq1; clear hdeq1; apply inj_pair2 in H2; subst; rename H3 into heq1.
  inversion hdeq2; clear hdeq2; apply inj_pair2 in H2; subst; rename H3 into heq2.
  destruct (finvS i) as [| [i' ?]]; subst.
  - cutrewrite (this {|this := phplus hh2 ph0; is_p := pdisj_is_pheap (h1:=hh2) (h2:=ph0) hdis1 |} =
                phplus hh2 ph0) in hdis; [|eauto].
    apply pdisjE1, pdisjC in hdis; simpl in hdis; eauto; apply pdisjE1 in hdis; eauto.
  - eapply IHn; eauto.
    cutrewrite (this {|this := phplus hh2 ph0; is_p := pdisj_is_pheap (h1:=hh2) (h2:=ph0) hdis1 |} =
                phplus hh2 ph0) in hdis; [|eauto].      
    apply pdisjE2, pdisjC in hdis; simpl in hdis; eauto; apply pdisjE2 in hdis; eauto.
Qed.

Lemma pp_pdisj1 (h1 h2 h3 h4 : gen_pheap) (dis12 : pdisj h1 h2) (dis34 : pdisj h3 h4) :
  pdisj (phplus_pheap dis12) (phplus_pheap dis34) ->
  pdisj h1 h3.
Proof.
  unfold phplus_pheap.
  cutrewrite (this {| this := phplus h3 h4;
                      is_p := pdisj_is_pheap (h1:=h3) (h2:=h4) dis34 |} =
              phplus h3 h4); [|simpl; eauto]; intros H.
  apply pdisjE1, pdisjC in H; simpl in H; eauto; apply pdisjE1 in H; eauto.
Qed.

Lemma pp_pdisj2 (h1 h2 h3 h4 : gen_pheap) (dis12 : pdisj h1 h2) (dis34 : pdisj h3 h4) :
  pdisj (phplus_pheap dis12) (phplus_pheap dis34) ->
  pdisj h2 h4.
Proof.
  unfold phplus_pheap.
  cutrewrite (this {| this := phplus h3 h4;
                      is_p := pdisj_is_pheap (h1:=h3) (h2:=h4) dis34 |} =
              phplus h3 h4); [|simpl; eauto]; intros H.
  apply pdisjE2, pdisjC in H; simpl in H; eauto; apply pdisjE2 in H; eauto.
Qed.

Lemma disj_eq_sum (n : nat) (hs1 hs2 hs' : Vector.t gen_pheap n) (h1 h2 : gen_pheap) (hdis : pdisj h1 h2):
  disj_eq hs1 h1 -> disj_eq hs2 h2 -> 
  (forall i, this hs'[@i] = phplus hs1[@i] hs2[@i]) ->
  disj_eq hs' (phplus_pheap hdis).
Proof.
  revert hs1 hs2 hs' h1 h2 hdis ; induction n;
  intros hs1 hs2 hs' h1 h2 hdis hdeq1 hdeq2 heqs.
  - rewrite (vinv0 hs1), (vinv0 hs2), (vinv0 hs') in *.
    inversion hdeq1; inversion hdeq2; subst.
    cutrewrite (phplus_pheap hdis = emp_ph); [constructor| apply pheap_eq; extensionality x; eauto].
  - destruct (vinvS hs1) as [ht1 [hs1' ?]], (vinvS hs2) as [ht2 [hs2' ?]], (vinvS hs') as [ht' [hs'' ?]] in *; subst.
    inversion hdeq1; clear hdeq1; apply inj_pair2 in H2; subst; rename H3 into hdeq1.
    inversion hdeq2; clear hdeq2; apply inj_pair2 in H2; subst; rename H3 into hdeq2.
    (*      inversion hdeq'; clear hdeq'; apply inj_pair2 in H2; subst; rename H3 into hdeq'.*)
    pose proof (pp_pdisj1 hdis) as dh12; pose proof (pp_pdisj2 hdis) as dph12.
    assert (forall i : Fin.t n, this hs''[@i] = phplus hs1'[@i] hs2'[@i]) by
        (intros i; specialize (heqs (Fin.FS i)); eauto).
    pose proof (IHn _ _ _ _ _ dph12 hdeq1 hdeq2 H).
    pose proof (heqs Fin.F1).
    set (h1 := phplus_pheap dph12).
    set (h2 := phplus_pheap dh12). 
    assert (pdisj h2 h1).
    { apply pdisjC.
      assert (pdisj ph0 (phplus ht1 ht2)).
      { apply pdisj_padd_comm, pdisjC; eauto.
        cutrewrite (this {|this := phplus ht1 ph; is_p := pdisj_is_pheap hdis0|} = phplus ht1 ph) in
            hdis; [|simpl; eauto]; apply pdisjC in hdis.
        eapply pdisjE1, pdisjC in hdis; eauto; simpl; rewrite phplus_comm; eauto. }
      unfold h1, h2.
      cutrewrite (this (phplus_pheap dph12) = phplus ph ph0); [|eauto].
      apply pdisj_padd_expand; eauto; split; [|simpl; eauto].
      simpl; rewrite padd_left_comm; eauto.
      cutrewrite (phplus ph0 ht2 = phplus_pheap hdis1); [|rewrite phplus_comm; eauto].
      apply pdisj_padd_expand; eauto; simpl in hdis; rewrite phplus_comm; eauto. }
    cutrewrite (phplus_pheap hdis = phplus_pheap H2).
    + cutrewrite (ht' = h2); [| now (unfold h1; destruct ht'; apply pheap_eq; apply H1)].
      constructor; eauto.
    + apply pheap_eq;
      cutrewrite (this {| this := phplus ht1 ph;
                          is_p := pdisj_is_pheap hdis0 |} = phplus ht1 ph); 
      [|simpl; eauto].
      Hint Resolve pdisjC pdisj_padd_comm.
      pose proof (pp_pdisj1 hdis).
      pose proof (pp_pdisj2 hdis). 
      pose proof (pdisjE1 hdis hdis1).
      pose proof (pdisjE2 hdis hdis1).
      pose proof (pdisjE1 (pdisjC hdis) hdis0).
      pose proof (pdisjE2 (pdisjC hdis) hdis0).
      assert (pdisj ht1 (phplus ph (phplus ht2 ph0))).
      { cutrewrite (phplus ht2 ph0 = this {| this := phplus ht2 ph0;
                                             is_p := pdisj_is_pheap hdis1 |}); [|simpl; eauto].
        apply pdisj_padd_expand; eauto. }
      rewrite padd_assoc; eauto.
      simpl. rewrite padd_left_comm; eauto.
      cutrewrite (phplus ph ph0 = this {| this := phplus ph ph0;
                                          is_p := pdisj_is_pheap dph12 |}); [|simpl; eauto].
      rewrite <-padd_assoc; simpl; f_equal; eauto.
      (* rewrite <-padd_left_comm; eauto. *)
Qed.

Lemma disj_eq_sub (n : nat) (hs hs1 hs2 : Vector.t gen_pheap n) (h : gen_pheap): 
  disj_eq hs h -> (forall i : Fin.t n, pdisj hs1[@i] hs2[@i] /\ phplus hs1[@i] hs2[@i] = hs[@i]) ->
  exists (h1 h2 : gen_pheap), 
    disj_eq hs1 h1 /\ disj_eq hs2 h2 /\ pdisj h1 h2 /\ phplus h1 h2 = h.
Proof.
  revert h; induction n; intros h hdis heq.
  - generalize (vinv0 hs), (vinv0 hs1), (vinv0 hs2); intros; subst; repeat eexists; 
    (repeat split); try constructor.
    inversion hdis; subst; unfold emp_ph; simpl; extensionality x; eauto.
  - destruct (vinvS hs) as [ph [hs' ?]], (vinvS hs1) as [ph1 [hs1' ?]], 
             (vinvS hs2) as [ph2 [hs2' ?]]; subst. inversion hdis; apply inj_pair2 in H2; subst.
    clear hdis.
    assert (forall i : Fin.t n, pdisj hs1'[@i] hs2'[@i] /\ phplus hs1'[@i] hs2'[@i] = hs'[@i]) 
      as H by (intros i; pose proof (heq (Fin.FS i)) as H; simpl in H; tauto).
    destruct (IHn _ _ _ _ H3 H) as [h1 [h2 IH]].
    assert (pdisj h1 ph1 /\ pdisj h2 ph2) as [dis1 dis2].
    { destruct IH as [? [? [H1 H2]]]; rewrite <-H2 in hdis0.
      destruct (heq Fin.F1) as [dis12 pp12]; simpl in *.
      assert (phplus_pheap dis12 = ph) by (destruct ph; apply pheap_eq; simpl in *; eauto).
      rewrite <-H5 in hdis0.
      apply pdisj_padd in hdis0; eauto.
      destruct hdis0 as [dis1 dis2]; apply pdisjC in dis1; apply pdisjC in dis2.
      simpl in *; apply pdisj_padd in dis1; apply pdisj_padd in dis2; tauto. }
    assert (pdisj h1 (phplus_pheap (pdisjC dis2))). 
    { simpl. rewrite (phplus_comm (pdisjC dis2)); apply pdisj_padd_expand; try tauto.
      destruct (heq Fin.F1) as [dis12 pp12]; simpl in dis12, pp12.
      destruct IH as [_ [_ [? ?]]].
      cutrewrite (ph0 = phplus_pheap H0) in hdis0;[|destruct ph0; eauto; apply pheap_eq; eauto].
      rewrite <-pp12 in hdis0.
      apply pdisjC in hdis0; apply pdisjE2 in hdis0; tauto. }
    assert (pdisj (phplus_pheap (h1:=ph1) (h2:=h1) (pdisjC (h1:=h1) (h2:=ph1) dis1))
                  (phplus_pheap (h1:=ph2) (h2:=h2) (pdisjC (h1:=h2) (h2:=ph2) dis2))).
    { apply (pdisj_padd_expand _ (pdisjC dis1)); split; auto.
      simpl; rewrite (padd_left_comm H0 (pdisjC dis2)).
      destruct IH as [? [? [hdis12 hpp12]]].
      cutrewrite (phplus h1 h2 = phplus_pheap hdis12); [| simpl; eauto].
      assert (pdisj ph1 (phplus ph2 (phplus_pheap (h1:=h1) (h2:=h2) hdis12)) /\
              pdisj ph2 (phplus_pheap (h1:=h1) (h2:=h2) hdis12)); [ | tauto].
      apply pdisj_padd_expand; [generalize (heq (Fin.F1)); tauto |].
      simpl; rewrite hpp12. 
      destruct (heq (Fin.F1)) as [? Heq]; simpl in *; rewrite Heq; eauto using pdisjC. }
    exists (phplus_pheap (pdisjC dis1)), (phplus_pheap (pdisjC dis2)); 
      repeat split; try econstructor; try tauto.
    + cutrewrite (this (phplus_pheap (h1:=ph1) (h2:=h1) (pdisjC (h1:=h1) (h2:=ph1) dis1)) =
                  phplus ph1 h1); [|eauto].
      rewrite padd_assoc. (* ;  [simpl| apply (pdisj_padd_expand _ (pdisjC dis1))| ];try tauto. *)
      destruct IH as [? [? [dis12 pp12]]]. simpl.
      rewrite (phplus_comm (pdisjC dis2)). 
      (* rewrite<-padd_assoc; [| rewrite (@phplus_comm h2 ph2); try tauto| apply ( dis2)]. *)
      rewrite <-(padd_assoc h1).
      (* cutrewrite (phplus h1 h2 = phplus_pheap dis12); [|eauto].  *)
      assert (pdisj ph2 (phplus_pheap (h1:=h1) (h2:=h2) dis12)).
      { destruct (heq (Fin.F1)) as [? ?]; simpl in *; rewrite <-H6 in hdis0.
        apply pdisjC,pdisjE2,pdisjC in hdis0; try eauto; rewrite pp12; eauto. }
      rewrite (@phplus_comm _ ph2), <-padd_assoc; eauto.
      simpl; rewrite pp12; destruct (heq (Fin.F1)) as [? ?]; simpl in *; congruence.
      (* * apply pdisj_padd_expand; destruct (heq Fin.F1); simpl in *; try tauto. *)
      (*   rewrite H7, pp12; tauto. *)
Qed.    

Lemma phplus_eq (h1 h2 : gen_pheap) (disj : pdisj h1 h2) :
  this (phplus_pheap disj) = phplus h1 h2. 
  simpl; eauto.
Qed.

Lemma disjeq_phplus (n : nat) (hs : Vector.t gen_pheap n) (h h' : gen_pheap) (i : Fin.t n) :
  disj_eq hs h -> pdisj h h' ->
  exists h'' : gen_pheap, pdisj hs[@i] h'' /\ pdisj h'' h' /\ 
              phplus hs[@i] h'' = h /\ pdisj hs[@i] (phplus h'' h').
Proof.
  intros hdeq hdis.
  destruct (disj_tid i hdeq) as [h'' [H [hdis' hplus]]].
  exists h''; repeat split; eauto.
  - rewrite <-hplus in hdis; apply pdisjC, pdisjE2, pdisjC in hdis; eauto.
  - apply pdisj_padd_expand; eauto.
    rewrite hplus; eauto.
Qed.

Lemma ptoheap_phplus (ph : gen_pheap) (h h' : heap) :
  pdisj ph (htop h) -> ptoheap (phplus ph (htop h)) h' -> 
  exists h'' : heap, ptoheap ph h''.
Proof.
  intros hdis heq.
  set (h'' := fun x : loc => match this ph x with
                             | Some (_, x) => Some x
                             | None => None
                           end).
  exists h''; intros x; specialize (hdis x); specialize (heq x); 
  unfold h'', phplus, htop, htop' in *; simpl in *; clear h''.
  destruct ph as [ph isph]; simpl in *; specialize (isph x);
    destruct (ph x) as [[? ?] | ], (h x); destruct heq, hdis as [? [? ?]], isph; try congruence.
  - cut False; [try tauto | eapply (@frac_contra2 q); eauto ].
  - split; congruence.
Qed.

Definition hdisj (h1 h2 : heap) := forall x, h1 x = None \/ h2 x = None.

(* h1 + h2 *)
Definition hplus (h1 h2 : heap) : heap := 
  (fun x => match h1 x with None => h2 x | Some y => Some y end).

Lemma ptoheap_plus (ph : gen_pheap) (h : heap) (hF : heap) :
  ptoheap ph h -> hdisj h hF -> ptoheap (phplus ph (htop hF)) (hplus h hF).
Proof.
  intros heq hdis x.
  specialize (heq x); specialize (hdis x).
  unfold phplus, htop, htop', hplus; simpl in *.
  destruct ph as [ph isp]; simpl in *; specialize (isp x);
  destruct (ph x) as [[? ?]|], (h x), (hF x); try congruence; destruct hdis, heq; 
  split; try congruence.
Qed.

Lemma hdisj_pdisj (h1 h2 : heap) : hdisj h1 h2 <-> pdisj (htop h1) (htop h2).
Proof.
  unfold hdisj, pdisj, htop, htop'; simpl; 
  split; intros H x; specialize (H x); destruct (h1 x), (h2 x); destruct H; try congruence; eauto.
  destruct H0; unfold full_p in *.
  unfold Qcle, Qle in H1; simpl in H1; omega.
Qed.

Lemma hplus_phplus (h1 h2 : heap) : hdisj h1 h2 -> htop' (hplus h1 h2) = phplus (htop h1) (htop h2).
Proof.
  intros hdis; extensionality x; specialize (hdis x); 
  unfold htop', hplus, phplus, htop, htop'; simpl.
  destruct (h1 x), (h2 x), hdis; congruence.
Qed.

Lemma heap_pheap_eq (h1 h2 : heap) : h1 = h2 <-> htop' h1 = htop' h2.
Proof.
  unfold htop; split; intros H; [|]; extensionality x.
  - subst; eauto.
  - inversion H; subst.
    assert (htop' h1 x = htop' h2 x) as Heq by (rewrite H1; eauto).
    unfold htop' in *; destruct (h1 x), (h2 x); congruence.
Qed.

Lemma htop'_eq (h1 h2 : heap) : htop' h1 = htop' h2 -> htop h1 = htop h2.
Proof.
  intros H; unfold htop.
  apply heap_pheap_eq in H; destruct H; eauto.
Qed.

Lemma hplus_cancel_l (h1 h2 hF h : heap) :
  hdisj h1 hF -> hdisj h2 hF -> h = hplus h1 hF -> h = hplus h2 hF -> h1 = h2.
Proof.
  intros Hdis1 Hdis2 Heq1 Heq2; extensionality x.
  assert (hplus h1 hF x = hplus h2 hF x) by congruence.
  unfold hplus in *; specialize (Hdis1 x); specialize (Hdis2 x);
  destruct (h1 x), (h2 x), (hF x); destruct Hdis1, Hdis2; try congruence.
Qed.

Lemma hplus_map (h1 h2 : heap) (x : loc) (v : val) :
  hdisj h1 h2 -> hplus h1 h2 x = Some v -> 
  (h1 x = Some v /\ h2 x = None) \/ (h1 x = None /\ h2 x = Some v).
Proof.
  intros Hdis heq; specialize (Hdis x); unfold hplus in *; destruct (h1 x), (h2 x), Hdis;
  try tauto; congruence.
Qed.

Definition upd A (f: loc -> A) x y a := if eq_dec a x then y else f a.

Lemma hplus_upd (h1 h2 hF : heap) (x : loc) (v : val) :
  hdisj h1 hF -> hdisj h2 hF -> upd (hplus h1 hF) x (Some v) = hplus h2 hF ->
  upd h1 x (Some v) = h2 \/ (exists v', hF x = Some v').
Proof.
  intros Hdis1 Hdis2 Heq.
  remember (hF x) as hFx; destruct hFx; [right; eexists; eauto|].
  left; extensionality x'; specialize (Hdis1 x'); specialize (Hdis2 x');
  assert (upd (hplus h1 hF) x (Some v) x' = hplus h2 hF x') by (rewrite Heq; eauto); clear Heq;
  unfold upd, hplus in *; destruct Hdis1, Hdis2, (eq_dec x' x), (h1 x'), (h2 x'); 
  try congruence.
Qed.

Lemma disj_emp1 (h : gen_pheap) : pdisj h emp_ph.
Proof.
  intros x; destruct (this h x) as [[? ?]|]; simpl; eauto.
Qed.

Lemma disj_emp2 (h : gen_pheap) : pdisj emp_ph h.
Proof.
  intros x; destruct (this h x) as [[? ?]|]; simpl; eauto.
Qed.

Lemma phplus_emp1 (h : gen_pheap) : phplus emp_ph h = h.
Proof.
  unfold phplus; simpl; extensionality x; auto.
Qed.

Lemma phplus_emp2 (h : gen_pheap) : phplus h emp_ph = h.
Proof.
  unfold phplus; simpl; extensionality x; destruct (this h x) as [[? ? ]|]; auto.
Qed.

End Loc.

Hint Resolve pdisjC pdisj_padd_comm.