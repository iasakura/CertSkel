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

Module PHeap.
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

  Lemma pdisj_padd_expand 
        (h1 h2 h3 : pheap) : pdisj h1 h2 -> 
                             (pdisj (phplus h1 h2) h3 <-> (pdisj h1 (phplus h2 h3) /\ pdisj h2 h3)).
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

  Lemma padd_assoc
        (h1 h2 h3 : pheap)  :
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

  Lemma padd_left_comm 
        (h1 h2 h3 : pheap) :
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
  
  Lemma padd_cancel
        (h1 h2 h3 : pheap) :
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
End PHeap.

Module Language.
  Import PHeap.
  
  Definition var := Z.
  Definition stack := var -> Z.
  Definition state := (stack * heap)%type.

  Inductive exp := 
  | Evar (x : var)
  | Enum (n : Z)
  | Eplus (e1: exp) (e2: exp).

  Inductive bexp :=
  | Beq (e1: exp) (e2: exp)
  | Band (b1: bexp) (b2: bexp)
  | Bnot (b: bexp).

  Inductive cmd : Set :=
  | Cskip
  | Cassign (x: var) (e: exp)
  | Cread (x: var) (e: exp)
  | Cwrite (e1: exp) (e2: exp)
  | Cseq (c1: cmd) (c2: cmd)
  | Cif (b: bexp) (c1: cmd) (c2: cmd)
  | Cwhile (b: bexp) (c: cmd)
  | Cbarrier (j : nat).

  Notation "'SKIP'" := Cskip.
  Notation "x '::=' a" := (Cassign x a) (at level 60).
  Notation "x '::=' '[' a ']'" := (Cread x a) (at level 60).
  Notation "'[' a ']' '::=' e" := (Cwrite a e) (at level 60).
  Notation "c1 ;; c2" := (Cseq c1 c2) (at level 80, right associativity).
  Notation "'BARRIER' ( j )" := (Cbarrier j).

  Fixpoint wait (c : cmd) : option (nat * cmd) :=
    match c with
      | SKIP | _ ::= _ | _ ::= [_] | [_] ::= _ | Cif _ _ _ | Cwhile _ _ => None
      | BARRIER (j) => Some (j, Cskip)
      | c1 ;; c2 =>
        match wait c1 with
          | Some (j, c1') => Some (j, c1' ;; c2)
          | None => None
        end
    end.

  Fixpoint edenot e s :=
    match e with
      | Evar v => s v
      | Enum n => n
      | Eplus e1 e2 => (edenot e1 s + edenot e2 s)%Z
    end.
  
  Fixpoint bdenot b s : bool := 
    match b with
      | Beq e1 e2 => if Z.eq_dec (edenot e1 s) (edenot e2 s) then true else false
      | Band b1 b2 => bdenot b1 s && bdenot b2 s
      | Bnot b => negb (bdenot b s)
    end.
  
  Reserved Notation "c '/' st  '==>s'  c' '/' st' " (at level 40, st at level 39, c' at level 39).
  Inductive red: cmd -> state -> cmd  -> state -> Prop := 
  | red_Seq1: forall (c : cmd) (ss : state), (SKIP ;; c) / ss ==>s c / ss
  | red_Seq2: forall (c1 : cmd) (ss : state) (c1' : cmd) (ss' : state) (c2 : cmd)
                     (R: c1 / ss ==>s c1' / ss'), 
                   (c1 ;; c2) / ss ==>s (c1' ;; c2) / ss'
  | red_If1: forall (b : bexp) (c1 c2 : cmd) (ss : state) 
                    (B: bdenot b (fst ss) = true), 
                    (Cif b c1 c2) / ss ==>s c1 / ss
  | red_If2: forall (b : bexp) (c1 c2 : cmd) (ss : state)
                    (B: bdenot b (fst ss) = false),
                    (Cif b c1 c2) / ss ==>s c2 / ss
  | red_Loop: forall (b : bexp) (c : cmd) (ss : state), 
                    (Cwhile b c) / ss ==>s (Cif b (Cseq c (Cwhile b c)) Cskip) / ss
  | red_Assign: forall (x : var) (e : exp) ss ss' s h
                       (EQ1: ss = (s, h))
                       (EQ2: ss' = (upd s x (edenot e s), h)),
                       (x ::= e) / ss ==>s Cskip / ss'
  | red_Read: forall x e ss ss' s h v
                     (EQ1: ss = (s, h))
                     (RD: h (edenot e s) = Some v)
                     (EQ2: ss' = (upd s x v, h)),
                     (x ::= [e]) / ss ==>s Cskip / ss'
  | red_Write: forall e1 e2 ss ss' s h
                      (EQ1: ss = (s, h))
                      (EQ2: ss' = (s, upd h (edenot e1 s) (Some (edenot e2 s)))),
                      (Cwrite e1 e2) / ss ==>s Cskip / ss'
   where  "c '/' st  '==>s'  c' '/' st' " := (red c st c' st').

  Definition red_tup (st1 st2 : (cmd * state)) : Prop := red (fst st1) (snd st1) (fst st2) (snd st2).
  Definition multi_red_tup : (cmd * state) -> (cmd * state) -> Prop := clos_refl_trans_1n _ red_tup.
  Definition multi_red (c1 : cmd) (st1 : state) (c2 : cmd) (st2 : state) := 
    multi_red_tup (c1, st1) (c2, st2).
  
  Notation "c '/' st  '==>s*'  c' '/' st' " := (multi_red c st c' st') (at level 40, st at level 39, c' at level 39).

  Lemma red_det (c c1 c2 : cmd) (st st1 st2 : state) :
    c / st ==>s c1 / st1 ->
    c / st ==>s c2 / st2 ->
    c1 = c2 /\ st1 = st2.
  Proof.
    intros red1 red2.
    induction [c2 st2 red2]red1; intros c2' st2 red2; try (inversion red2; subst; split; congruence).
    - inversion red2; subst; eauto.
      inversion R.
    - inversion red2; subst.
      + inversion red1.
      + apply IHred1 in R; destruct R; subst; split; congruence.
  Qed.

  Fixpoint accesses (c : cmd) (s : stack) := 
    match c with
      | Cskip => None
      | x ::= e => None
      | x ::= [e] => Some (edenot e s)
      | [e] ::= e' => Some (edenot e s)
      | c1 ;; c2 => accesses c1 s
      | (Cif b c1 c2) => None
      | (Cwhile b c) => None
      | (Cbarrier _) => None
    end.

  Fixpoint writes (c : cmd) (s : stack) :=
    match c with
      | Cskip => None
      | (x ::= e) => None
      | (x ::= [e]) => None
      | ([e] ::= e') => Some (edenot e s)
      | (c1 ;; c2) => writes c1 s
      | (Cif b c1 c2) => None
      | (Cwhile b c) => None
      | Cbarrier j => None
    end.
  
  Inductive aborts : cmd -> state -> Prop := 
  | aborts_Seq : forall (c1 c2 : cmd) (ss : state) (A: aborts c1 ss), aborts (Cseq c1 c2) ss
  | aborts_Read: forall x e ss
                        (NIN: snd ss (edenot e (fst ss)) = None),
                   aborts (Cread x e) ss
  | aborts_Write: forall e1 e2 ss
                         (NIN: snd ss (edenot e1 (fst ss)) = None),
                    aborts (Cwrite e1 e2) ss.

  Fixpoint barriers c :=
    match c with
      | Cskip => nil
      | (Cassign x e) => nil
      | (Cread x e) => nil
      | (Cwrite e e') => nil
      | (Cseq c1 c2) => barriers c1 ++ barriers c2
      | (Cif b c1 c2) => barriers c1 ++ barriers c2
      | (Cwhile b c) => barriers c
      | Cbarrier j => j :: nil
    end.

  Definition wf_cmd c := disjoint_list (barriers c).

  Module BigStep.
    Reserved Notation " c '/' s '||' c' '/' s'" (at level 40, s at level 39, c' at level 39).
    Inductive eval : cmd -> state -> option (nat * cmd) -> state -> Prop :=
    | eval_Skip : forall (st : state), SKIP / st || None / st
    | eval_Seq1 : forall (c1 c2 c1': cmd) (st st' : state) (j : nat),
                    c1 / st || (Some (j, c1')) / st' ->
                    (c1 ;; c2) / st || Some (j, c1' ;; c2) / st'
    | eval_Seq2 : forall (c1 c2 : cmd) (c2' : option (nat * cmd)) (st st' st'' : state), 
                    c1 / st || None / st' -> c2 / st' || c2' / st'' -> (c1 ;; c2) / st || c2' / st''
    | eval_If1 : forall (b : bexp) (c1 c2 : cmd) (c1' : option (nat * cmd)) (st st' : state),
                  bdenot b (fst st) = true -> c1 / st || c1' / st' ->
                  (Cif b c1 c2) / st || c1' / st'
    | eval_If2 : forall (b : bexp) (c1 c2 : cmd) (c2' : option (nat * cmd)) (st st' : state),
                   bdenot b (fst st) = false -> c2 / st || c2' / st' ->
                   (Cif b c1 c2) / st || c2' / st'
    | eval_Loop : forall (b : bexp) (c : cmd) (c' : option (nat * cmd)) (st st' : state),
                     (Cif b (c ;; (Cwhile b c)) Cskip) / st || c'/ st' ->
                     (Cwhile b c) / st || c' / st'
    | eval_Assign : forall (x : var) (e : exp) (st st' : state) s h,
                      (st = (s, h)) -> (st' = (upd s x (edenot e s), h)) ->
                      (x ::= e) / st || None / st'
    | eval_Read : forall (x : var) (e : exp) (v : Z) (st st' : state) (s : stack) (h : heap),
                    (st = (s, h)) -> (h (edenot e s) = Some v) ->
                    (st' = (upd s x v, h)) ->
                    (x ::= [e]) / st || None / st'
    | eval_Write : forall e1 e2 ss ss' s h,
                     (ss = (s, h)) ->
                     (ss' = (s, upd h (edenot e1 s) (Some (edenot e2 s)))) ->
                     (Cwrite e1 e2) / ss || None / ss'
    | eval_Barrier : forall ss j,
                       (Cbarrier j) / ss || Some (j, Cskip) / ss
      where " c '/' s '||' c' '/' s'" := (eval c s c' s').
    
    Lemma red1_eval (c1 c2 : cmd) (st1 st2 : state) (st : state) : 
      c1 / st1 ==>s c2 / st2 -> c2 / st2 || None / st -> c1 / st1 || None / st.
    Proof.
      move=> H IH.
      induction [st IH]H; ins; try do 10 (econstructor; eauto).
      - inversion IH; subst.
        econstructor; eauto.
      - apply eval_If2; eauto.
      - eapply eval_Assign; eauto.
        inversion IH; subst; eauto.
      - eapply eval_Read; eauto.
        inversion IH; subst; eauto.
      - eapply eval_Write; eauto.
        inversion IH; subst; eauto.
    Qed.

    Corollary red1_eval' (c1 c2 : cmd) (st1 st2 st3 : state) : 
      c1 / st1 ==>s c2 / st2 -> c2 / st2 || None / st3 -> c1 / st1 || None / st3.
    Proof.
      move=> H H'.
      remember (c1, st1) as s1.
      assert (c1 = fst s1) as h by (rewrite Heqs1; tauto); rewrite h in *; clear h.
      assert (st1 = snd s1) as h by (rewrite Heqs1; tauto); rewrite h in *; clear h.
      remember (c2, st2) as s2.
      assert (c2 = fst s2) as h by (rewrite Heqs2; tauto); rewrite h in *; clear h.
      assert (st2 = snd s2) as h by (rewrite Heqs2; tauto); rewrite h in *; clear h.
      eapply red1_eval; eauto.
    Qed.

    Lemma eval__mred1 (c : cmd) (st st' : state) : 
      c / st ==>s* Cskip / st' -> c / st || None / st'.
      intros H. unfold multi_red in H.
      remember (c, st) as s.
      remember (SKIP, st') as s'.
      assert (c = fst s) as h by (rewrite Heqs; tauto); rewrite h; clear h.
      assert (st = snd s) as h by (rewrite Heqs; tauto); rewrite h; clear h.
      assert (st' = snd s') as h by (rewrite Heqs'; tauto); rewrite h; clear h.
      clear Heqs.
       induction [Heqs'] H.
      - move=>->; simpl; apply eval_Skip.
      - move/IHclos_refl_trans_1n=>IH; clear IHclos_refl_trans_1n.
        clear H0.
        eapply red1_eval; eauto.
    Qed.

    Lemma eval_mred2 (c c' c'': cmd) (st st' : state) (j : nat) : 
      c / st ==>s* c' / st' -> wait c' = Some (j, c'') ->
      c / st || Some (j, c'') / st'.
    Proof.
      intros hs hwait.
      unfold multi_red in hs.
      remember (c, st) as s.
      remember (c', st') as s'.
      assert (c = fst s) as h by (rewrite Heqs; tauto); rewrite h; clear h.
      assert (st = snd s) as h by (rewrite Heqs; tauto); rewrite h; clear h.
      assert (st' = snd s') as h by (rewrite Heqs'; tauto); rewrite h; clear h.
      clear Heqs.
      induction [Heqs'] hs.
      - intros ->.
        induction [c'' j hwait]c'; move=> c'' j' hwait; inversion hwait.
        + destruct (wait c'1); eauto.
          * destruct p as (j'', c'); simpl in *.
            apply eval_Seq1.
            now apply IHc'1.
          * inversion H0.
        + apply eval_Barrier.
      - move=>->; simpl in *.
        assert ((c', st') = (c', st')) as IH by eauto; apply IHhs in IH; clear IHhs; simpl in *.
        clear hs hwait c' c st.
        unfold red_tup in H;
        induction [c'' IH]H; ins; try do 5 (econstructor; eauto).
        + inversion IH; subst.
          * apply eval_Seq1. 
            apply IHred; eauto.
          * eapply eval_Seq2; eauto.
            eapply red1_eval'; eauto.
        + apply eval_If2; eauto.
        + inversion IH.
        + inversion IH.
        + inversion IH.
    Qed.
  End BigStep.

  Definition kstate := (list (cmd * stack) * heap)%type.

  Module PLang.
    Definition pstate := (stack * pheap)%type.
  
    Definition access_ok (c : cmd) (s : stack) (h : pheap) :=
      match accesses c s with
        | None => True
        | Some v => exists x, this h v = Some x
      end.

    Definition write_ok (c : cmd) (s : stack) (h : pheap) :=
      match writes c s with
        | None => True
        | Some v => exists x, this h v = Some (full_p, x)
      end.

    Inductive red_p: cmd -> pstate -> cmd -> pstate -> Prop :=
      redp_ster : forall (c1 c2 : cmd) (st1 st2 : state) (pst1 pst2 : pstate) (s1 s2 : stack)
                         (ph1 ph2 phF : pheap) (h1 h2 : heap),
        st1 = (s1, h1) -> st2 = (s2, h2) ->
        pst1 = (s1, ph1) -> pst2 = (s2, ph2) ->
        access_ok c1 s1 ph1 ->
        write_ok c1 s1 ph1 ->
        pdisj ph1 phF -> ptoheap (phplus ph1 phF) h1 ->
        c1 / st1 ==>s c2 / st2 ->
        pdisj ph2 phF -> ptoheap (phplus ph2 phF) h2 ->
        red_p c1 pst1 c2 pst2.
    Notation "c '/' st  '==>p'  c' '/' st' " := 
      (red_p c st c' st') (at level 40, st at level 39, c' at level 39).

    Hint Resolve pdisjC.
    Lemma Q1 (q1 q2 q : Qc) : q1 + q2 = q -> q1 = q - q2.
    Proof. intros H; rewrite <-H; ring. Qed.
    Hint Rewrite Q1.

    Lemma Q2 (q1 q2 q : Qc) : q1 + q2 = q -> q2 = q - q1.
    Proof. intros H; rewrite <-H; ring. Qed.
    Hint Rewrite Q2.

    Lemma phplus_cancel_toheap (ph1 ph2 phF : pheap) (h : heap):
      pdisj ph1 phF -> pdisj ph2 phF ->
      ptoheap (phplus ph1 phF) h -> ptoheap (phplus ph2 phF) h -> ph1 = ph2.
    Proof.
      intros dis1 id2 to1 to2.
      pose proof (ptoD to1 to2).
      eapply padd_cancel2; eauto.
    Qed.

    Lemma padd_upd_cancel (ph1 ph2 phF : pheap) (h : heap) (x v v': Z) :
      pdisj ph1 phF -> pdisj ph2 phF -> ptoheap (phplus ph1 phF) h ->
      this ph1 x = Some (full_p, v') -> ptoheap (phplus ph2 phF) (upd h x (Some v)) -> 
      this ph2 = ph_upd ph1 x v.
    Proof.
      intros pd1 pd2 toh1 have1 toh2; extensionality y; unfold ph_upd.
      destruct ph1 as [ph1 h1], ph2 as [ph2 h2], phF as [phF hF]; simpl in *.
      destruct (Z.eq_dec x y).
      - rewrite <-e; clear e y.
        unfold is_pheap, pdisj, ptoheap, upd, phplus in *;
          repeat (match goal with [H : forall _ : Z, _ |- _] => specialize (H x) end).
        destruct (Z.eq_dec x x); try tauto.
        rewrite have1 in *.
        destruct (phF x) as [[pF vF]|]; des.
        + apply Qcle_minus_iff in pd3.
          cutrewrite (1 + -(full_p + pF) = -pF) in pd3; [|unfold full_p; field].
          apply Qcopp_le_compat in pd3; ring_simplify in pd3.
          apply Qcle_not_lt in pd3; tauto.
        + destruct (ph2 x) as [[p2 v2]|]; try congruence.
          des; congruence.
      - unfold is_pheap, pdisj, ptoheap, upd, phplus in *;
        repeat (match goal with [H : forall _ : Z, _ |- _] => specialize (H y) end).
        destruct (Z.eq_dec y x); [symmetry in e; tauto |].
        destruct (ph1 y) as [[? ?]|], (phF y) as [[? ?]|], (ph2 y) as [[? ?]|]; des; 
        try congruence.
        apply Q1 in toh1; apply Q1 in toh2.
        destruct (h y) as [? | ]; inversion toh0; inversion toh3; congruence.
        rewrite toh2 in toh1.
        assert (q + full_p - full_p = full_p - full_p) by (rewrite toh1; ring).
        ring_simplify in H; rewrite H in h1; inversion h1.
        rewrite toh1 in toh2.
        assert (q0 + full_p - full_p = full_p - full_p) by (rewrite toh2; ring).
        ring_simplify in H; rewrite H in h2; inversion h2.
    Qed.

    Lemma red_p_det (c c1 c2 : cmd) (st st1 st2 : pstate) :
      c / st ==>p c1 / st1 ->
      c / st ==>p c2 / st2 ->
      c1 = c2 /\ st1 = st2.
    Proof.
      intros red1 red2.
      destruct red1 as
          [c1 c1' st1 st1' pst1 pst1' s1 s1' ph1 ph1' phF1 h1 h1' eq1 eq1' 
              peq1 peq1' aok1 wok1 dis1 to1 red1 dis1' to1'].
      destruct red2 as
          [c2 c2' st2 st2' pst2 pst2' s2 s2' ph2 ph2' phF2 h2 h2' eq2 eq2' 
              peq2 peq2' aok2 wok2 dis2 to2 red2 dis2' to2'].
      induction [c2' red2]red1; intros c2' red2; 
      try (inversion red2; subst; 
           repeat (match goal with [H : (_, _) = (_, _) |- _ ] => inversion H; subst; clear H end);
           simpl in *; try congruence;
           assert (ph1' = ph2) by (eapply phplus_cancel_toheap; eauto);
           assert (ph2' = ph2) by (eapply phplus_cancel_toheap; eauto);
           split; congruence).
      - inversion red2; subst.
        + repeat (match goal with [H : (_, _) = (_, _) |- _ ] => inversion H; subst; clear H end).
          assert (ph1' = ph2) by (eapply phplus_cancel_toheap; eauto).
          assert (ph2' = ph2) by (eapply phplus_cancel_toheap; eauto).
          split; congruence.
        + inversion R.
      - inversion red2; subst. 
        + inversion red1.
        + unfold access_ok, write_ok in *; simpl in *. 
          pose proof (IHred1 eq_refl eq_refl aok1 wok1 aok2 wok2 c1'0 R) as H; 
            destruct H as [He1 He2].
          split; [subst; eauto | eauto].
      - inversion red2; subst;
        repeat (match goal with [H : (_, _) = (_, _) |- _ ] => inversion H; subst; clear H end).
        unfold access_ok in *; simpl in *.
        remember (edenot e s0) as vad.
        assert (ph1' = ph2) by (eapply phplus_cancel_toheap; eauto).
        assert (ph2' = ph2) by (eapply phplus_cancel_toheap; eauto).
        cutrewrite (v = v0); [split; congruence |].
        assert (Some v0 = Some v) as Heq; [ rewrite <- RD0, <-RD | 
                                            rewrite <-RD0, <-RD in Heq; congruence].
        clear Heqvad; subst.
        destruct aok1 as [[q va] Hv].
        unfold pdisj, ptoheap in *.
        repeat (match goal with [H : forall _ : Z, _ |- _] => specialize (H vad) end).
        unfold phplus in *.
        rewrite Hv in *.
        destruct (this phF1 vad) as [[? ?] | ], (this phF2 vad) as [[? ?] | ]; des; try congruence.
      - inversion red2; subst.
        split; eauto.
        assert (s1' = s2') by congruence; subst.
        assert (ph1' = ph2'); [| subst; eauto].
        inversion EQ3; inversion EQ0; inversion peq2; inversion EQ2; inversion EQ1. 
        subst. rewrite H8 in *.
        unfold write_ok in *; simpl in *.
        destruct wok1 as [v1' H1], wok2 as [v2' H2].
        remember (edenot e1 s) as addr. clear Heqaddr.
        remember (edenot e2 s) as v. clear Heqv.
        assert (this ph1' = ph_upd ph2 addr v) by eapply (padd_upd_cancel dis1 dis1' to1 H1 to1').
        assert (this ph2' = ph_upd ph2 addr v) by eapply (padd_upd_cancel dis2 dis2' to2 H2 to2').
        destruct ph1' as [ph1' h1], ph2' as [ph2' h2]; simpl in *; subst.
        assert (h1 = h2) by apply proof_irrelevance; congruence.
    Qed.

    Section Typing.
      Inductive type := Hi | Lo.
      Definition join (t1 t2 : type) :=
        match (t1, t2) with
          | (Hi, _) | (_, Hi) => Hi
          | (Lo, Lo) => Lo
        end.
      
      Definition le_type (t1 t2 : type) : bool :=
        match (t1, t2) with
          | (Lo, _) | (_, Hi) => true
          | (Hi, Lo) => false
        end.

      Definition env := var -> type.
      Inductive typing_exp : env -> exp -> type -> Prop := 
      | ty_var : forall (g : env) (v : var) (ty : type), g v = ty -> typing_exp g (Evar v) ty
      | ty_num : forall (g : env) (n : Z) (ty : type), typing_exp g (Enum n) ty
      | ty_plus : forall (g : env) (e1 e2 : exp) (ty1 ty2 : type), 
                    typing_exp g e1 ty1 -> typing_exp g e2 ty2 ->
                    typing_exp g (Eplus e1 e2) (join ty1 ty2).

      Inductive typing_bexp : env -> bexp -> type -> Prop := 
      | ty_eq : forall (g : env) (e1 e2 : exp) (ty1 ty2 : type), 
                  typing_exp g e1 ty1 -> typing_exp g e2 ty2 ->
                  typing_bexp g (Beq e1 e2) (join ty1 ty2)
      | ty_and : forall (g : env) (b1 b2 : bexp) (ty1 ty2 : type), 
                  typing_bexp g b1 ty1 -> typing_bexp g b2 ty2 ->
                  typing_bexp g (Band b1 b2) (join ty1 ty2)
      | ty_not : forall (g : env) (b : bexp) (ty : type), 
                   typing_bexp g b ty -> typing_bexp g (Bnot b) ty.

      Inductive typing_cmd : env -> cmd -> type -> Prop :=
      | ty_skip : forall (g : env) (pc : type), typing_cmd g Cskip pc
      | ty_assign : forall (g : env) (v : var) (e : exp) (pc ty : type),
                      typing_exp g e ty -> le_type (join ty pc) (g v) = true ->
                      typing_cmd g (v ::= e) pc
      | ty_read : forall (g : env) (v : var) (e : exp) (pc ty : type),
                    typing_exp g e ty -> le_type (join ty pc) (g v) = true ->
                    typing_cmd g (v ::= [e]) pc
      | ty_write : forall (g : env) (e1 e2 : exp) (pc : type),
                     typing_cmd g ([e1] ::= e2) pc
      | ty_seq : forall (g : env) (c1 c2 : cmd) (pc : type),
                   typing_cmd g c1 pc -> typing_cmd g c2 pc ->
                   typing_cmd g (c1 ;; c2) pc
      | ty_if : forall (g : env) (b : bexp) (c1 c2 : cmd) (pc ty : type),
                  typing_bexp g b ty ->
                  typing_cmd g c1 (join pc ty) -> typing_cmd g c2 (join pc ty) ->
                  typing_cmd g (Cif b c1 c2) pc
      | ty_while : forall (g : env) (b : bexp) (c : cmd) (pc ty : type),
                     typing_bexp g b ty ->
                     typing_cmd g c (join pc ty) -> typing_cmd g (Cwhile b c) pc
      | ty_barrier : forall (g : env) (j : nat), typing_cmd g (Cbarrier j) Lo.

      

End Language.