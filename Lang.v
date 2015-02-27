Require Import Logic.Eqdep.
Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import QArith.
Require Import Qcanon.
Require Import Coq.Relations.Relations.
Require Import Vector.
Require Import List.
Require ClassicalFacts.
Require Export FunctionalExtensionality.
Require Export ProofIrrelevance.

Require Export Coq.ZArith.BinInt.

Add LoadPath "../../src/cslsound".

Require Import Vbase Varith Vlistbase Vlist Basic.

Set Implicit Arguments.
Unset Strict Implicit.

Require Import PHeap.

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

  Definition red_p_tup (st1 st2 : (cmd * pstate)) : Prop := 
    red_p (fst st1) (snd st1) (fst st2) (snd st2).
  Definition multi_red_p_tup : (cmd * pstate) -> (cmd * pstate) -> Prop := 
    clos_refl_trans_1n _ red_p_tup.
  Definition multi_red_p (c1 : cmd) (st1 : pstate) (c2 : cmd) (st2 : pstate) := 
    multi_red_p_tup (c1, st1) (c2, st2).
  
  Notation "c '/' st  '==>p*'  c' '/' st' " := (multi_red_p c st c' st') 
    (at level 40, st at level 39, c' at level 39).

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

  Lemma red_p_frame (c1 c2 : cmd) (pst1 pst2 : pstate) (hF : pheap) :
    c1 / pst1 ==>p c2 / pst2 ->
    pdisj hF (snd pst1) -> pdisj hF (snd pst2).
  Proof.
    intros hred; move: hF; case hred.
    clear c1 c2 pst1 pst2 hred; 
    intros c1 c2 st1 st2 pst1 pst2 s1 s2 ph1 ph2 phF h1 h2 hst1 hst2 hpst1 hpst2 haok hwok 
           hdis1 htoh1 hred_s hdis2 htoh2 hF hdisF.
    induction hred_s; subst;
    try (inversion hst2; subst; rewrite<- (phplus_cancel_toheap hdis1 hdis2 htoh1 htoh2); tauto);
    unfold access_ok, write_ok in *; simpl in *.
    - apply IHhred_s; eauto.
    - inversion EQ1; inversion EQ2; subst;
      rewrite<- (phplus_cancel_toheap hdis1 hdis2 htoh1 htoh2); tauto.
    - inversion EQ1; inversion EQ2; subst;
      rewrite<- (phplus_cancel_toheap hdis1 hdis2 htoh1 htoh2); tauto.
    - inversion EQ1; inversion EQ2; clear EQ1 EQ2; subst.
      destruct hwok as [v' H].
      rewrite (padd_upd_cancel hdis1 hdis2 htoh1 H htoh2).
      apply pdisjC; apply <-pdisj_upd; eauto.
  Qed.

  Lemma red_s_safe' (c1 c2 : cmd) (st1 st2 : state) (pst1 : pstate) (hF : pheap) :
    c1 / st1 ==>s c2 / st2 -> 
    (fst pst1 = fst st1) ->
    pdisj (snd pst1) hF -> ptoheap (phplus (snd pst1) hF) (snd st1) ->
    access_ok c1 (fst pst1) (snd pst1) ->
    write_ok c1 (fst pst1) (snd pst1) ->
    exists (ph2 : pheap),
      pdisj ph2 hF /\ ptoheap (phplus ph2 hF) (snd st2).
  Proof.
    intros red1; move: pst1 hF; induction red1; intros pst1 hF hst hdis1 hto1 haok hwok;
    try (exists (snd pst1); subst; simpl; try destruct ss; split; tauto).
    - eapply IHred1; eauto.
    - subst; rewrite hst in *; unfold access_ok, write_ok in *; simpl in *.
      destruct hwok as [v' Hv'].
      exists (Pheap (ph_upd_ph (snd pst1) (edenot e1 s) (edenot e2 s))); simpl; split.
      + apply<- pdisj_upd; eauto.
      + assert (this hF (edenot e1 s) = None).
        { destruct hF as [hF isphF]; 
          pose proof (hdis1 (edenot e1 s)); pose proof (isphF (edenot e1 s)); simpl in *.
          rewrite Hv' in H. destruct (hF (edenot e1 s)); eauto.
          destruct p. destruct H0 as [H1 _], H as [_ [_ H2]].
          apply frac_contra1 in H2; eauto; tauto. } 
        intros x; unfold phplus, ph_upd, upd. 
        specialize (hto1 x); destruct (Z.eq_dec (edenot e1 s) x).
        * rewrite e, H in *; repeat split; unfold upd; destruct (Z.eq_dec x x); tauto.
        * unfold phplus,upd in *; destruct (this (snd pst1) x) as [[? ?]|], (this hF x) as [[? ?]|];
          destruct (Z.eq_dec x (edenot e1 s)); 
          repeat split; try tauto; try congruence.
  Qed.

  Lemma red_s_safe (c1 c2 : cmd) (st1 st2 : state) (pst1 : pstate) (hF : pheap) :
    c1 / st1 ==>s c2 / st2 -> 
    (fst pst1 = fst st1) ->
    pdisj (snd pst1) hF -> ptoheap (phplus (snd pst1) hF) (snd st1) ->
    access_ok c1 (fst pst1) (snd pst1) ->
    write_ok c1 (fst pst1) (snd pst1) ->
    exists (pst2 : pstate),
      c1 / pst1 ==>p c2 / pst2 /\ 
      fst pst2 = fst st2 /\
      pdisj (snd pst2) hF /\ 
      ptoheap (phplus (snd pst2) hF) (snd st2).
  Proof.
    intros red1 heq1 hdis1 hto1 aok wok. 
    destruct (red_s_safe' red1 heq1 hdis1 hto1 aok wok) as [ph2 [H1 H2]].
    exists (fst st2, ph2); split; eauto.
    apply (@redp_ster c1 c2 st1 st2 pst1 (fst st2, ph2) (fst st1) (fst st2) (snd pst1) ph2 hF 
                      (snd st1) (snd st2));
      try (destruct st1, st2, pst1; simpl in *; eauto; congruence).
  Qed.
End PLang.

Export PLang.

Module BigStep.
  Reserved Notation " c '/' s '||' c' '/' s'" (at level 40, s at level 39, c' at level 39).
  Inductive eval : cmd -> pstate -> option (nat * cmd) -> pstate -> Prop :=
  | eval_Skip : forall (st : pstate), SKIP / st || None / st
  | eval_Seq1 : forall (c1 c2 c1': cmd) (st st' : pstate) (j : nat),
                  c1 / st || (Some (j, c1')) / st' ->
                  (c1 ;; c2) / st || Some (j, c1' ;; c2) / st'
  | eval_Seq2 : forall (c1 c2 : cmd) (c2' : option (nat * cmd)) (st st' st'' : pstate), 
                  c1 / st || None / st' -> c2 / st' || c2' / st'' -> (c1 ;; c2) / st || c2' / st''
  | eval_If1 : forall (b : bexp) (c1 c2 : cmd) (c1' : option (nat * cmd)) (st st' : pstate),
                 bdenot b (fst st) = true -> c1 / st || c1' / st' ->
                 (Cif b c1 c2) / st || c1' / st'
  | eval_If2 : forall (b : bexp) (c1 c2 : cmd) (c2' : option (nat * cmd)) (st st' : pstate),
                 bdenot b (fst st) = false -> c2 / st || c2' / st' ->
                 (Cif b c1 c2) / st || c2' / st'
  | eval_Loop : forall (b : bexp) (c : cmd) (c' : option (nat * cmd)) (st st' : pstate),
                  (Cif b (c ;; (Cwhile b c)) Cskip) / st || c'/ st' ->
                  (Cwhile b c) / st || c' / st'
  | eval_Assign : forall (x : var) (e : exp) (st st' : pstate) s h,
                    (st = (s, h)) -> (st' = (upd s x (edenot e s), h)) ->
                    (x ::= e) / st || None / st'
  | eval_Read : forall (x : var) (e : exp) (v : Z) (st st' : pstate) (s : stack) (h : pheap) (q : Qc),
                  (st = (s, h)) -> (this h (edenot e s) = Some (q, v)) ->
                  (st' = (upd s x v, h)) ->
                  (x ::= [e]) / st || None / st'
  | eval_Write : forall (e1 e2 : exp) (ss ss' : pstate) (s : stack) (h : pheap) (v : Z),
                   (ss = (s, h)) ->
                   this h (edenot e1 s) = Some (1, v) ->
                   (ss' = (s, ph_upd2 h (edenot e1 s) (edenot e2 s))) ->
                   (Cwrite e1 e2) / ss || None / ss'
  | eval_Barrier : forall ss j,
                     (Cbarrier j) / ss || Some (j, Cskip) / ss
                                  where " c '/' s '||' c' '/' s'" := (eval c s c' s').
  
  Lemma red1_eval (c1 c2 : cmd) (st1 st2 : pstate) (st : pstate) : 
    c1 / st1 ==>p c2 / st2 -> c2 / st2 || None / st -> c1 / st1 || None / st.
  Proof.
    move=> H IH.
    destruct H as
        [c c' st' st'' pst pst' s s' ph ph' phF h h' eq eq' 
            peq peq' aok wok dis to red dis' to'].
    induction [st IH]red; ins; subst; 
    repeat (match goal with [H : (_, _) = (_, _) |- _ ] => inversion H; subst; clear H end); 
    try assert (ph = ph') by (eapply phplus_cancel_toheap; eauto); subst;
    try (constructor; tauto).
    - econstructor; [econstructor | eauto].
    - inversion IH; subst; unfold access_ok, write_ok in *; simpl in *. 
      pose proof (IHred eq_refl eq_refl aok wok _ H1).
      econstructor; eauto.
    - apply eval_If2; eauto.
    - eapply eval_Assign; eauto.
      inversion IH; subst; eauto.
    - unfold access_ok in *; simpl in *; destruct aok as [[q v'] h].
      eapply eval_Read; eauto.
      inversion IH; subst.
      unfold ptoheap, phplus in to; specialize (to (edenot e s0)); rewrite h in to;
      destruct (this phF (edenot e s0)) as [[? ?] |]; destruct to as [? H'];
      rewrite H' in *; inversion RD; eauto.
    - unfold write_ok in *; simpl in *; destruct wok as [v' h];
      eapply eval_Write; eauto.
      inversion IH; subst; eauto.
      cutrewrite (ph' = ph_upd2 ph (edenot e1 s0) (edenot e2 s0)); eauto.
      assert (this ph' = this (ph_upd2 ph (edenot e1 s0) (edenot e2 s0))) by 
          (eapply padd_upd_cancel; eauto).
      destruct ph'; simpl in H.
      unfold ph_upd2.
      symmetry in H; destruct H.
      cutrewrite (is_p = ph_upd_ph ph (edenot e1 s0) (edenot e2 s0)); 
        [ eauto | apply proof_irrelevance ].
  Qed.

  Lemma eval__mred1 (c : cmd) (st st' : pstate) : 
    c / st ==>p* Cskip / st' -> c / st || None / st'.
    intros H; unfold multi_red_p in H.
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

  Lemma eval_mred2 (c c' c'': cmd) (st st' : pstate) (j : nat) : 
    c / st ==>p* c' / st' -> wait c' = Some (j, c'') ->
    c / st || Some (j, c'') / st'.
  Proof.
    intros hs hwait.
    unfold multi_red_p in hs.
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
      unfold red_p_tup in H.
      destruct H as [c c' stp' stp'' pst pst' s s' ph ph' phF h h' eq eq' 
                     peq peq' aok wok dis to red dis' to'].
      induction [c'' IH]red; ins; subst; try inversion eq'; subst;
      try assert (ph = ph') by (eapply phplus_cancel_toheap; eauto); subst;
      try (econstructor; tauto).
      + eapply eval_Seq2; [apply eval_Skip | eauto ].
      + inversion IH; subst;
        unfold access_ok, write_ok in *; simpl in *.
        * apply eval_Seq1; eauto.
        * eapply eval_Seq2; eauto.
          eapply red1_eval; eauto.
          apply (@redp_ster _ _ (s, h) (s', h') (s, ph) (s', ph') s s' ph ph' phF h h'); eauto.
      + apply eval_If2; eauto.
      + inversion IH.
      + inversion IH.
      + inversion IH.
  Qed.
End BigStep.

Export BigStep.

Section ParSem.
  Variable ngroup : nat.
  Definition klist := Vector.t (cmd * stack) ngroup.
  Definition kstate := (klist * heap)%type.
  Definition kidx := Fin.t ngroup.

  Inductive red_k : kstate -> kstate -> Prop :=
  | redk_Seq : 
      forall (ks : kstate) (ss : klist) (c c' : cmd) (st st' : state) 
             (s s' : stack) (h h' : heap) (i : kidx),
        ks = (ss, h) -> Vector.nth ss i = (c, s) ->
        c / st ==>s c' / st' ->
        st = (s, h) -> st' = (s', h') ->
        red_k ks (Vector.replace ss i (c', s'), h')
  | redk_Barrier :
      forall (ks ks' : kstate) (ss ss' : klist) (h : heap) (j : nat),
        ks = (ss, h) -> ks' = (ss', h) ->
        (forall (i : kidx),
         exists c s c', Vector.nth ss  i = (c, s) /\ wait c = Some (j, c') /\
                        Vector.nth ss' i = (c', s)) ->
        red_k ks ks'.
End ParSem.
Notation "ks '==>k' ks'" := (red_k ks ks') (at level 40).
Definition multi_red_k (ngroup : nat) (k1 k2 : kstate ngroup) := clos_refl_trans_1n _ (@red_k ngroup) k1 k2.
Notation "ks '==>k*' ks'" := (multi_red_k ks ks') (at level 40).
  
Section NonInter.
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
  Variable g : env.
  
  Inductive typing_exp : exp -> type -> Prop := 
  | ty_var : forall (v : var) (ty : type), g v = ty -> typing_exp (Evar v) ty
  | ty_num : forall (n : Z) (ty : type), typing_exp (Enum n) ty
  | ty_plus : forall (e1 e2 : exp) (ty1 ty2 : type), 
                typing_exp e1 ty1 -> typing_exp e2 ty2 ->
                typing_exp (Eplus e1 e2) (join ty1 ty2).

  Inductive typing_bexp : bexp -> type -> Prop := 
  | ty_eq : forall (e1 e2 : exp) (ty1 ty2 : type), 
              typing_exp e1 ty1 -> typing_exp e2 ty2 ->
              typing_bexp (Beq e1 e2) (join ty1 ty2)
  | ty_and : forall (b1 b2 : bexp) (ty1 ty2 : type), 
               typing_bexp b1 ty1 -> typing_bexp b2 ty2 ->
               typing_bexp (Band b1 b2) (join ty1 ty2)
  | ty_not : forall (b : bexp) (ty : type), 
               typing_bexp b ty -> typing_bexp (Bnot b) ty.

  Inductive typing_cmd : cmd -> type -> Prop :=
  | ty_skip : forall (pc : type), typing_cmd Cskip pc
  | ty_assign : forall (v : var) (e : exp) (pc ty : type),
                  typing_exp e ty -> le_type (join ty pc) (g v) = true ->
                  typing_cmd (v ::= e) pc
  | ty_read : forall (v : var) (e : exp) (pc ty : type),
                typing_exp e ty -> le_type (join ty pc) (g v) = true ->
                typing_cmd (v ::= [e]) pc
  | ty_write : forall (e1 e2 : exp) (pc : type),
                 typing_cmd ([e1] ::= e2) pc
  | ty_seq : forall (c1 c2 : cmd) (pc : type),
               typing_cmd c1 pc -> typing_cmd c2 pc ->
               typing_cmd (c1 ;; c2) pc
  | ty_if : forall (b : bexp) (c1 c2 : cmd) (pc ty : type),
              typing_bexp b ty ->
              typing_cmd c1 (join pc ty) -> typing_cmd c2 (join pc ty) ->
              typing_cmd (Cif b c1 c2) pc
  | ty_while : forall (b : bexp) (c : cmd) (pc ty : type),
                 typing_bexp b ty ->
                 typing_cmd c (join pc ty) -> typing_cmd (Cwhile b c) pc
  | ty_barrier : forall (j : nat), typing_cmd (Cbarrier j) Lo.

  Definition low_eq (s1 s2 : stack) := forall x, g x = Lo -> s1 x = s2 x.
  
  Lemma hi_low_eq (x : var) (v1 v2 : Z) (s1 s2 : stack):
    low_eq s1 s2 -> g x = Hi -> low_eq (upd s1 x v1) (upd s2 x v2).
  Proof.
    unfold upd; intros heq hhi y; destruct (Z.eq_dec y x); subst.
    - intros h; rewrite hhi in h; inversion h.
    - intros h; apply heq in h; eauto.
  Qed.

  Lemma low_eq_eq_exp (e : exp) (s1 s2 : stack) :
    low_eq s1 s2 -> typing_exp e Lo -> edenot e s1 = edenot e s2.
  Proof.
    intros heq hty; induction e; simpl; eauto.
    - inversion hty; specialize (heq x); eauto.
    - inversion hty.
      destruct ty1, ty2; unfold join in H1; simpl in H1; inversion H1.
      apply IHe1 in H2; apply IHe2 in H3; rewrite H2, H3; eauto.
  Qed.

  Lemma low_eq_eq_bexp (be : bexp) (s1 s2 : stack) :
    low_eq s1 s2 -> typing_bexp be Lo -> bdenot be s1 = bdenot be s2.
  Proof.
    intros heq hty; induction be; simpl; eauto.
    - inversion hty.
      destruct ty1, ty2; inversion H1.
      cutrewrite (edenot e1 s1 = edenot e1 s2); [ | eapply low_eq_eq_exp; eauto].
      cutrewrite (edenot e2 s1 = edenot e2 s2); [ | eapply low_eq_eq_exp; eauto].
      eauto.
    - inversion hty.
      destruct ty1, ty2; inversion H1.
      apply IHbe1 in H2; apply IHbe2 in H3; rewrite H2, H3; eauto.
    - inversion hty.
      rewrite (IHbe H0); eauto.
  Qed.

  Lemma pheap_disj_eq (h1 h2 : pheap) (v v1 v2 : Z) (q1 q2 : Qc) :
    pdisj h1 h2 -> this h1 v = Some (q1, v1) -> this h2 v = Some (q2, v2) -> v1 = v2.
  Proof.
    intros hdis h1v h2v.
    specialize (hdis v); rewrite h1v, h2v in hdis; des; eauto.
  Qed.

  Lemma pheap_disj_disj (h1 h2 : pheap) (v1 v2 v1' v2' v1'' v2'' : Z) :
    pdisj h1 h2 -> this h1 v1 = Some (full_p, v1') -> this h2 v2 = Some (full_p, v2') ->
    pdisj (ph_upd2 h1 v1 v1'') (ph_upd2 h2 v2 v2'').
  Proof.
    intros hdis h1v h2v.
    apply (pdisj_upd (ph_upd2 h2 v2 v2'') v1'' h1v).
    apply pdisjC.
    unfold ph_upd2; simpl.
    apply (pdisj_upd h1 v2'' h2v); eauto.
  Qed.

  Definition st_compat (st1 st2 : pstate) :=
    low_eq (fst st1) (fst st2) /\ pdisj (snd st1) (snd st2).

  Definition terminal := option (nat * cmd).

  Lemma non_interference_hi (c : cmd) (st1 st2 st2' : pstate) (t : terminal) :
    typing_cmd c Hi -> st_compat st1 st2 ->
    c / st2 || t / st2' -> t = None /\ st_compat st1 st2'.
  Proof.
    intros htng1 hcomp ev.
    induction ev.
    - split; eauto. 
    - inversion htng1; subst.
      pose proof (IHev H1 hcomp) as [H ?]; inversion H.
    - inversion htng1; subst.
      pose proof (IHev1 H1 hcomp) as [_ hcomp'].
      apply (IHev2 H3 hcomp').
    - inversion htng1; subst.
      assert (join Hi ty = Hi) by (destruct ty; simpl; eauto); subst; eauto.
    - inversion htng1; subst.
      assert (join Hi ty = Hi) by (destruct ty; simpl; eauto); subst; eauto.
    - assert (typing_cmd (Cif b (c ;; Cwhile b c) SKIP) Hi).
      inversion htng1; subst.
      apply (ty_if H1); econstructor; eauto.
      eauto.
    - inversion htng1; subst.
      cutrewrite (join ty Hi = Hi) in H5; [ | destruct ty; eauto].
      assert (g x = Hi) by (destruct (g x); inversion H5; eauto).
      destruct hcomp as [heq ?];
        repeat split; destruct st1 as [s1 h1]; simpl; eauto.
      intros y; unfold upd; destruct (Z.eq_dec y x); subst.
      + intros H'; congruence.
      + specialize (heq y); eauto.
    - inversion htng1; subst.
      cutrewrite (join ty Hi = Hi) in H6; [ | destruct ty; eauto].
      assert (g x = Hi) by (destruct (g x); inversion H6; eauto).
      destruct st1 as [s' h'], hcomp as [heq hdisj]; simpl in *.
      repeat split; eauto; simpl.
      intros y; unfold upd; destruct (Z.eq_dec y x); subst.
      + intros H'; congruence.
      + specialize (heq y); simpl; eauto.
    - subst; destruct st1, hcomp; unfold st_compat in *; simpl in *; repeat split; eauto.
      apply pdisjC. apply (pdisj_upd _ _ H0); apply pdisjC; eauto.
    - inversion htng1.
  Qed.

  Lemma st_compat_refl (st1 st2 : pstate) : st_compat st1 st2 -> st_compat st2 st1.
  Proof.
    unfold st_compat; intros [h1 h2]; split.
    - intros x; specialize (h1 x); intros; symmetry; eauto. 
    - apply pdisjC; eauto.
  Qed.

  Lemma non_interference_hi2 (c1 c2 : cmd) (st1 st2 st1' st2' : pstate) (t1 t2 : terminal) :
    typing_cmd c1 Hi -> typing_cmd c2 Hi -> st_compat st1 st2 ->
    c1 / st1 || t1 / st1' -> c2 / st2 || t2 / st2' -> t1 = t2 /\ st_compat st1' st2'.
  Proof.
    intros htng1 htng2 hcomp ev1 ev2.
    pose proof (non_interference_hi htng2 hcomp ev2) as [hc1 hc2].      
    pose proof (non_interference_hi htng1 (st_compat_refl hc2) ev1) as [hc3 hc4].
    subst; split; eauto.
    apply st_compat_refl; eauto.
  Qed.

  Lemma non_interference_big (ty : type) (c : cmd) (st1 st2 st1' st2' : pstate) (t1 t2 : terminal) :
    typing_cmd c ty -> st_compat st1 st2 ->
    c / st1 || t1 / st1' -> c / st2 || t2 / st2' -> t1 = t2 /\ st_compat st1' st2'.
  Proof.
    intros htng hcomp ev1 ev2.
    revert hcomp ev2; generalize st2 st2' t2; clear st2 st2' t2; induction ev1;
    intros st2 st2' t2 hcomp ev2; unfold st_compat in *; des.
    - inversion ev2; split; [eauto | split; subst; eauto].
    - inversion htng; subst.
      inversion ev2; subst.
      + pose proof (IHev1 H1 _ _ _ (conj hcomp hcomp0) H6) as H; clear IHev1; rename H into IHev1.
        destruct IHev1 as [hteq ?]; split; eauto.
        inversion hteq; subst; eauto.
      + pose proof (IHev1 H1 _ _ _ (conj hcomp hcomp0) H2) as H; clear IHev1; rename H into IHev1.
        destruct IHev1 as [H ?]; inversion H.
    - inversion htng; subst.
      inversion ev2; subst.
      + pose proof (IHev1_1 H1 _ _ _ (conj hcomp hcomp0) H6) as [H ?]; inversion H.
      + pose proof (IHev1_1 H1 _ _ _ (conj hcomp hcomp0) H2) as [_ hcomp'].
        apply (IHev1_2 H3 _ _ _ hcomp' H7).
    - inversion htng; subst.
      rename H3 into htngb, H5 into htng1, H6 into htng2.
      inversion ev2; subst.
      + destruct ty0.
        * assert (join ty Hi = Hi) as Hr by (destruct ty; eauto); rewrite Hr in *; clear Hr.
          eapply (non_interference_hi2 htng1 htng1 (conj hcomp hcomp0) ev1 H7).
        * destruct ty; [eapply (non_interference_hi2 htng1 htng1 (conj hcomp hcomp0) ev1 H7)|].
          apply (IHev1 htng1 _ _ _ (conj hcomp hcomp0)); eauto.
      + destruct ty0.
        * assert (join ty Hi = Hi) as Hr by (destruct ty; eauto); rewrite Hr in *; clear Hr.
          eapply (non_interference_hi2 htng1 htng2 (conj hcomp hcomp0) ev1 H7).
        * destruct ty; [eapply (non_interference_hi2 htng1 htng2 (conj hcomp hcomp0) ev1 H7)|].
          pose proof (low_eq_eq_bexp hcomp htngb); congruence.
    - inversion htng; subst.
      rename H3 into htngb, H5 into htng1, H6 into htng2.
      inversion ev2; subst.
      + destruct ty0.
        * assert (join ty Hi = Hi) as Hr by (destruct ty; eauto); rewrite Hr in *; clear Hr.
          eapply (non_interference_hi2 htng2 htng1 (conj hcomp hcomp0) ev1 H7).
        * destruct ty; [eapply (non_interference_hi2 htng2 htng1 (conj hcomp hcomp0) ev1 H7)|].
          pose proof (low_eq_eq_bexp hcomp htngb); congruence.
      + destruct ty0.
        * assert (join ty Hi = Hi) as Hr by (destruct ty; eauto); rewrite Hr in *; clear Hr.
          eapply (non_interference_hi2 htng2 htng2 (conj hcomp hcomp0) ev1 H7).
        * destruct ty; [eapply (non_interference_hi2 htng2 htng2 (conj hcomp hcomp0) ev1 H7)|].
          apply (IHev1 htng2 _ _ _ (conj hcomp hcomp0)); eauto.
    - inversion ev2; subst.
      inversion H4; subst.
      + assert (typing_cmd (Cif b (c;; Cwhile b c) SKIP) ty).
        { inversion htng; subst; repeat (econstructor; eauto).
          destruct ty, ty0; eauto. }
        apply (IHev1 H _ _ _ (conj hcomp hcomp0) H4).
      + inversion H7; subst.
        inversion ev1; subst; try (inversion H9; subst; tauto).
        destruct ty; inversion htng; subst.
        * cutrewrite (join Hi ty = Hi) in H3; [|eauto].
          pose proof (st_compat_refl (conj hcomp hcomp0)).
          assert (typing_cmd (c ;; Cwhile b c) Hi) by (econstructor; eauto).
          pose proof (non_interference_hi H0 H H9).
          destruct H2 as [? H']; split; [eauto | apply (st_compat_refl H')].
        * destruct ty.
          { assert (typing_cmd (Cwhile b c) Hi) by (econstructor; eauto).
            assert (typing_cmd (c;; Cwhile b c) Hi) by (econstructor; eauto).
            pose proof (non_interference_hi H0 (st_compat_refl (conj hcomp hcomp0)) H9).
            destruct H2 as [? H']; split; [eauto | apply (st_compat_refl H')]. }
          pose proof (low_eq_eq_bexp hcomp H1); congruence.
    - inversion ev2; subst; simpl in *; repeat split; eauto.
      destruct ty; inversion htng; subst.
      + inversion H3; apply hi_low_eq; eauto.
        destruct ty, (g x); unfold le_type in *; simpl in *; inversion H3; eauto.
      + intros y hlo; pose proof (hcomp y hlo); unfold upd; destruct (Z.eq_dec y x); eauto; subst.
        eapply low_eq_eq_exp; eauto.
        destruct ty, (g x); simpl in H3; inversion H3; inversion hlo; eauto.
    - inversion ev2; subst; simpl in *; repeat split; eauto.
      destruct ty; inversion htng; subst.
      + apply hi_low_eq; eauto.
        destruct ty, (g x); unfold le_type in *; simpl in *; inversion H4; eauto.
      + intros y hlo; pose proof (hcomp y hlo); unfold upd; destruct (Z.eq_dec y x); eauto; subst.
        destruct ty, (g x); simpl in H4; inversion H4; inversion hlo; eauto.
        assert (edenot e s = edenot e s0) by (apply low_eq_eq_exp; eauto).
        rewrite H1 in *.
        eapply pheap_disj_eq; eauto.
    - inversion ev2; subst; simpl in *; repeat split; eauto.
      apply (pheap_disj_disj _ _ hcomp0 H0 H5).
    - inversion ev2; subst; repeat split; eauto.
  Qed.

  Theorem non_interference_p1 (ty : type) (c : cmd) (st1 st2 st1' st2' : pstate) 
          (t1 t2 : terminal) :
    typing_cmd c ty -> st_compat st1 st2 ->
    c / st1 ==>p* Cskip / st1' -> c / st2 ==>p* Cskip / st2' -> st_compat st1' st2'.
  Proof.
    intros htyp hcomp hred1 hred2.
    apply eval__mred1 in hred1.
    apply eval__mred1 in hred2.
    assert ((None : terminal)  = None /\ st_compat st1' st2').
    eapply non_interference_big; eauto.
    tauto.
  Qed.

  Theorem non_interference_p2 (ty : type) (c c1 c2 c1' c2' : cmd) (st1 st2 st1' st2' : pstate) 
          (j1 j2 : nat) :
    typing_cmd c ty -> st_compat st1 st2 ->
    c / st1 ==>p* c1 / st1' -> c / st2 ==>p* c2 / st2' -> 
    wait c1 = Some (j1, c1') -> wait c2 = Some (j2, c2') ->
    j1 = j2 /\ c1' = c2' /\ st_compat st1' st2'.
  Proof.
    intros htyp hcomp hred1 hred2 hwait1 hwait2.
    apply (eval_mred2 hred1) in hwait1.
    apply (eval_mred2 hred2) in hwait2.
    assert (Some (j1, c1') = Some (j2, c2') /\ st_compat st1' st2').
    eapply non_interference_big; eauto.
    destruct H as [H' ?]; inversion H'; subst; tauto.
  Qed. 

  Theorem non_interference_p3 (ty : type) (c c1 c1' : cmd) (st1 st2 st1' st2' : pstate) 
          (j1 j2 : nat) :
    typing_cmd c ty -> st_compat st1 st2 ->
    c / st1 ==>p* c1 / st1' -> c / st2 ==>p* Cskip / st2' -> 
    ~ wait c1 = Some (j1, c1').
  Proof.
    intros htyp hcomp hred1 hred2 hwait.
    apply (eval_mred2 hred1) in hwait.
    apply eval__mred1 in hred2.
    assert (Some (j1, c1') = None /\ st_compat st1' st2').
    eapply non_interference_big; eauto.
    destruct H as [H' ?]; inversion H'.
  Qed. 
End NonInter.
