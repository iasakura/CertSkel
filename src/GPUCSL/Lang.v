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
Require Import String.
Require Import LibTactics.

Require Export Coq.ZArith.BinInt.

Set Implicit Arguments.
Unset Strict Implicit.

Require Import PHeap.
(* Definition of Language *)

Inductive PL := Shared | Global.

Inductive loc := Loc (pl : PL) (l : Z).
Notation SLoc := (Loc Shared).
Notation GLoc := (Loc Global).
Inductive var := Var : string -> var.
Definition stack := var -> Z.
Require Import Classes.EquivDec.
Global Program Instance loc_eq_dec : eq_type loc.
Next Obligation.
  repeat decide equality.
Defined.
Global Program Instance Z_eq_dec : eq_type Z.
Next Obligation.
  apply Z_eq_dec.
Defined.

Notation heap := (heap loc).
Notation pheap' := (gen_pheap' loc).
Notation pheap := (gen_pheap loc).
Definition state := (stack * heap)%type.
Arguments eq_dec _ _ _ _ : simpl never.

Inductive binop_exp :=
| OP_plus | OP_min | OP_lt | OP_eq | OP_mult | OP_sub | OP_div | OP_mod.

Inductive exp := 
| Evar (x : var)
| Enum (n : Z)
| Ebinop (op : binop_exp) (e1 e2 : exp).

Inductive binop_comp :=
| OP_beq | OP_blt.

Inductive binop_bool :=
| OP_and | OP_or.

Inductive unop_bool :=
| OP_not.

Inductive bexp :=
| Bcomp (op : binop_comp) (e1 e2 : exp)
| Bbool (op : binop_bool) (b1 b2 : bexp)
| Bunary (op : unop_bool) (b : bexp).

Inductive loc_exp :=
| Addr : PL -> exp -> loc_exp
| loc_offset : loc_exp -> exp -> loc_exp.
Notation Sh := (Addr Shared).
Notation Gl := (Addr Global).

Inductive CTyp := Int | Bool | Ptr (cty : CTyp).

Inductive cmd : Set :=
| Cskip
| Cassign (typ : option CTyp) (x: var) (e: exp)
| Cread (typ : option CTyp) (x: var) (e: loc_exp)
| Cwrite (e1: loc_exp) (e2: exp)
| Cseq (c1: cmd) (c2: cmd)
| Cif (b: bexp) (c1: cmd) (c2: cmd)
| Cwhile (b: bexp) (c: cmd)
| Cbarrier (j : nat).

Notation "'SKIP'" := Cskip.
Notation "x '::=' a" := (Cassign None x a) (at level 60).
Notation "x '::=' '[' a ']'" := (Cread None x a) (at level 60).
Notation "x ':T' ty '::=' a" := (Cassign (Some ty) x a) (at level 60, ty at next level).
Notation "x ':T' ty '::=' '[' a ']'" := (Cread (Some ty) x a) (at level 60, ty at next level).
Notation "x '::T' ty '::=' a" := (Cassign ty x a) (at level 60, ty at next level).
Notation "x '::T' ty '::=' '[' a ']'" := (Cread ty x a) (at level 60, ty at next level).
Notation "'[' a ']' '::=' e" := (Cwrite a e) (at level 60).
Notation "c1 ;; c2" := (Cseq c1 c2) (at level 80, right associativity).
Notation "'BARRIER' ( j )" := (Cbarrier j).

(* wait c = Some (j, c') <-> c is wait barrier at j and continuation after barrier is c' *)
Fixpoint wait (c : cmd) : option (nat * cmd) :=
  match c with
    | SKIP | _ ::T _ ::= _ | _ ::T _ ::= [_] | [_] ::= _ | Cif _ _ _ | Cwhile _ _ => None
    | BARRIER (j) => Some (j, Cskip)
    | c1 ;; c2 =>
      match wait c1 with
        | Some (j, c1') => Some (j, c1' ;; c2)
        | None => None
      end
  end.

Fixpoint binop_exp_denot op :=
  match op with
  | OP_plus => Z.add
  | OP_min => Z.min
  | OP_lt => fun x y => if Z_lt_dec x y then 1 else 0
  | OP_eq => fun x y => if eq_dec x y then 1 else 0
  | OP_mult => Z.mul
  | OP_sub => Z.sub
  | OP_div => Z.div
  | OP_mod => Z.modulo
  end%Z.

Fixpoint edenot e s :=
  match e with
    | Evar v => s v
    | Enum n => n
    | Ebinop op e1 e2 => binop_exp_denot op (edenot e1 s) (edenot e2 s)
  end%Z.

Fixpoint ledenot e s :=
  match e with
    | Addr p e => Loc p (edenot e s)
    | loc_offset e e' =>
      match ledenot e s with
      | Loc p lv => Loc p (lv + edenot e' s)
      end
  end%Z.

Fixpoint binop_comp_denot op :=
  match op with 
  | OP_beq => fun x y => if eq_dec x y then true else false
  | OP_blt => fun x y => if Z_lt_dec x y then true else false
  end.

Fixpoint binop_bool_denot op :=
  match op with
  | OP_and => andb
  | OP_or => orb
  end.

Fixpoint unop_bool_denot op :=
  match op with
  | OP_not => negb
  end.

Fixpoint bdenot b s : bool := 
  match b with
  | Bcomp op e1 e2 => binop_comp_denot op (edenot e1 s) (edenot e2 s)
  | Bbool op b1 b2 => binop_bool_denot op (bdenot b1 s) (bdenot b2 s)
  | Bunary op b => unop_bool_denot op (bdenot b s)
  end.

Lemma var_eq_dec (x y : var) : {x = y} + {x <> y}.
Proof.
  repeat decide equality. 
Defined.

Definition var_upd A (f: var -> A) x y a := if var_eq_dec a x then y else f a.

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
| red_Assign: forall (x : var) (e : exp) (cty : option CTyp) ss ss' s h
                     (EQ1: ss = (s, h))
                     (EQ2: ss' = (var_upd s x (edenot e s), h)),
                (x ::T cty ::= e) / ss ==>s Cskip / ss'
| red_Read: forall x e ss ss' (cty : option CTyp) s h v
                   (EQ1: ss = (s, h))
                   (RD: h (ledenot e s) = Some v)
                   (EQ2: ss' = (var_upd s x v, h)),
              (x ::T cty ::= [e]) / ss ==>s Cskip / ss'
| red_Write: forall e1 e2 ss ss' s h
                    (EQ1: ss = (s, h))
                    (EQ2: ss' = (s, upd h (ledenot e1 s) (Some (edenot e2 s)))),
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
  revert c2 st2 red2; induction red1; intros c2' st2 red2; try (inversion red2; subst; split; congruence).
  - inversion red2; subst; eauto.
    inversion R.
  - inversion red2; subst.
    + inversion red1.
    + apply IHred1 in R; destruct R; subst; split; congruence.
Qed.

Fixpoint accesses (c : cmd) (s : stack) := 
  match c with
    | Cskip => None
    | x ::T _ ::= e => None
    | x ::T _ ::= [e] => Some (ledenot e s)
    | [e] ::= e' => Some (ledenot e s)
    | c1 ;; c2 => accesses c1 s
    | (Cif b c1 c2) => None
    | (Cwhile b c) => None
    | (Cbarrier _) => None
  end.

Fixpoint writes (c : cmd) (s : stack) :=
  match c with
    | Cskip => None
    | (x ::T _ ::= e) => None
    | (x ::T _ ::= [e]) => None
    | ([e] ::= e') => Some (ledenot e s)
    | (c1 ;; c2) => writes c1 s
    | (Cif b c1 c2) => None
    | (Cwhile b c) => None
    | Cbarrier j => None
  end.

Inductive aborts : cmd -> state -> Prop := 
| aborts_Seq : forall (c1 c2 : cmd) (ss : state) (A: aborts c1 ss), aborts (Cseq c1 c2) ss
| aborts_Read: forall x e ty ss
                      (NIN: snd ss (ledenot e (fst ss)) = None),
                 aborts (Cread x ty e) ss
| aborts_Write: forall e1 e2 ss
                       (NIN: snd ss (ledenot e1 (fst ss)) = None),
                  aborts (Cwrite e1 e2) ss.

Fixpoint barriers c :=
  match c with
    | Cskip => nil
    | (x ::T _ ::= e) => nil
    | (x ::T _ ::= [e]) => nil
    | (Cwrite e e') => nil
    | (Cseq c1 c2) => barriers c1 ++ barriers c2
    | (Cif b c1 c2) => barriers c1 ++ barriers c2
    | (Cwhile b c) => barriers c
    | Cbarrier j => j :: nil
  end.

Lemma naborts_red_s (c1 c2 : cmd) (s1 s2 : stack) (h1 h2 hF : heap) :
  hdisj h1 hF -> hdisj h2 hF ->
  ~aborts c1 (s1, h1) ->
  c1 / (s1, hplus h1 hF) ==>s c2 / (s2, hplus h2 hF) ->
  c1 / (s1, h1) ==>s c2 / (s2, h2).
Proof.
  intros hdis1 hdis2 naborts hred.
  remember (s1, hplus h1 hF) as st1.
  remember (s2, hplus h2 hF) as st2.
  induction hred; try constructor; eauto;
  try (destruct ss as [s h]; inversion Heqst1; inversion Heqst2;
       assert (h1 = h2) by (apply (hplus_cancel_l hdis1 hdis2 H1); eauto);
       repeat subst; constructor; eauto).
  - apply IHhred; eauto.
    intros H; apply naborts; constructor; eauto.
  - econstructor; eauto.
    destruct ss, ss'. 
    repeat match goal with | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H end; subst.
    rewrites* (>>hplus_cancel_l H7).
  - apply (@red_Read _ _ _ _ _ s1 h1 v); eauto;
    destruct ss as [s1' h1F], ss' as [s2' h2F];
    repeat match goal with  | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H end; subst.
    + rewrite H7 in RD.
      destruct (hplus_map hdis1 RD) as [[? ?]| [? ?]]; [congruence|].
      contradict naborts; constructor; subst; eauto.
    + rewrites* (>>hplus_cancel_l H7).
  - apply (@red_Write _ _ _ _ s1 h1); eauto.
    destruct ss as [sx hx], ss' as [sx' hx'].
    repeat match goal with | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H end; subst.
    cut (h2 = upd h1 (ledenot e1 s1) (Some (edenot e2 s1))); [intros; subst; eauto|].
    destruct (hplus_upd hdis1 hdis2 H5) as [? | [hFx ?]]; eauto.
    contradict naborts; constructor; simpl; destruct (hdis1 (ledenot e1 s1)); congruence.
Qed.

Fixpoint disjoint_list A (l : list A) :=
  match l with
    | nil => True
    | x :: l => ~ In x l /\ disjoint_list l
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
  Lemma Q1 (q1 q2 q : Qc) : (q1 + q2 = q -> q1 = q - q2)%Qc.
  Proof. intros H; rewrite <-H; ring. Qed.
  Hint Rewrite Q1.

  Lemma Q2 (q1 q2 q : Qc) : (q1 + q2 = q -> q2 = q - q1)%Qc.
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

  Lemma padd_upd_cancel (ph1 ph2 phF : pheap) (h : heap) (x : loc) (v v' : Z) :
    pdisj ph1 phF -> pdisj ph2 phF -> ptoheap (phplus ph1 phF) h ->
    this ph1 x = Some (full_p, v') -> ptoheap (phplus ph2 phF) (upd h x (Some v)) -> 
    this ph2 = ph_upd ph1 x v.
  Proof.
    intros pd1 pd2 toh1 have1 toh2; extensionality y; unfold ph_upd.
    destruct ph1 as [ph1 h1], ph2 as [ph2 h2], phF as [phF hF].
    destruct (eq_dec x y); simpl in *.
    - rewrite <-e; clear e y.
      unfold is_pheap, pdisj, ptoheap, upd, phplus in *;
        repeat (match goal with [H : forall _ : loc, _ |- _] => specialize (H x) end).
      destruct (eq_dec x x); try congruence.
      rewrite have1 in *.
      destruct (phF x) as [[pF vF]|]; intuition.
      + apply (Qcle_minus_iff (full_p + pF) 1) in H8.
        cutrewrite (1 + -(full_p + pF) = -pF)%Qc in H8; [|unfold full_p; field].
        apply Qcopp_le_compat in H8; ring_simplify in H8.
        apply Qcle_not_lt in H8; tauto.
      + destruct (ph2 x) as [[p2 v2]|]; try congruence.
        intuition; congruence.
    - unfold is_pheap, pdisj, ptoheap, upd, phplus in *;
      repeat (match goal with [H : forall _ : loc, _ |- _] => specialize (H y) end).
      destruct (eq_dec y x); autounfold in *; [symmetry in e; congruence |].
      destruct (ph1 y) as [[? ?]|], (phF y) as [[? ?]|], (ph2 y) as [[? ?]|]; intuition; 
      try congruence.
      apply Q1 in H9; apply Q1 in H11.
      destruct (h y) as [? | ]; inversion H12; inversion H10; congruence.
      rewrite H7 in H5.
      assert (q + full_p - full_p = full_p - full_p)%Qc by (rewrite H5; ring).
      ring_simplify in H4; rewrite H4 in H; inversion H.
      rewrite H5 in H7.
      assert (q0 + full_p - full_p = full_p - full_p)%Qc by (rewrite H7; ring).
      ring_simplify in H4; rewrite H4 in H; inversion H.
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
    revert c2' red2; induction red1; intros c2' red2; 
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
      remember (ledenot e s) as vad.
      assert (ph1' = ph2) by (eapply phplus_cancel_toheap; eauto).
      assert (ph2' = ph2) by (eapply phplus_cancel_toheap; eauto).
      cutrewrite (v = v0); [split; congruence |].
      assert (Some v0 = Some v) as Heq; [ rewrite <- RD0, <-RD | 
                                          rewrite <-RD0, <-RD in Heq; congruence].
      clear Heqvad; subst.
      destruct aok1 as [[q va] Hv].
      unfold pdisj, ptoheap in *.
      repeat (match goal with [H : forall _ : loc, _ |- _] => specialize (H vad) end).
      unfold phplus in *.
      rewrite Hv in *.
      destruct (this phF1 vad) as [[? ?] | ], (this phF2 vad) as [[? ?] | ]; intuition; try congruence.
    - inversion red2; subst.
      split; eauto.
      assert (s1' = s2') by congruence; subst.
      assert (ph1' = ph2'); [| subst; eauto].
      inversion EQ3; inversion EQ0; inversion peq2; inversion EQ2; inversion EQ1. 
      subst. 
      unfold write_ok in *; simpl in *.
      destruct wok1 as [v1' H1], wok2 as [v2' H2].
      remember (ledenot e1 s) as addr. clear Heqaddr.
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
    intros hred; revert hF; case hred.
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
      apply pdisjC. rewrite pdisj_upd; eauto.
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
    intros red1; revert pst1 hF; induction red1; intros pst1 hF hst hdis1 hto1 haok hwok;
    try (exists (snd pst1); subst; simpl; try destruct ss; split; tauto).
    - eapply IHred1; eauto.
    - subst; rewrite hst in *; unfold access_ok, write_ok in *; simpl in *.
      destruct hwok as [v' Hv'].
      exists (Pheap (ph_upd_ph (snd pst1) (ledenot e1 s) (edenot e2 s))); simpl; split.
      + rewrite pdisj_upd; eauto.
      + assert (this hF (ledenot e1 s) = None).
        { destruct hF as [hF isphF]; 
          pose proof (hdis1 (ledenot e1 s)); pose proof (isphF (ledenot e1 s)); simpl in *.
          rewrite Hv' in H. destruct (hF (ledenot e1 s)); eauto.
          destruct p. destruct H0 as [H1 _], H as [_ [_ H2]].
          apply frac_contra1 in H2; eauto; tauto. } 
        intros x; unfold phplus, ph_upd, upd. 
        specialize (hto1 x); destruct (eq_dec (ledenot e1 s) x).
        * rewrite e, H in *; repeat split; unfold upd; destruct (eq_dec x x); try tauto.
        * unfold phplus,upd in *; destruct (this (snd pst1) x) as [[? ?]|], (this hF x) as [[? ?]|];
          destruct (eq_dec x (ledenot e1 s)); 
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
  | eval_Assign : forall (x : var) (e : exp) (cty : option CTyp) (st st' : pstate) s h,
                    (st = (s, h)) -> (st' = (var_upd s x (edenot e s), h)) ->
                    (x ::T cty ::= e) / st || None / st'
  | eval_Read : forall (x : var) (e : loc_exp) (cty : option CTyp) (v : Z) (st st' : pstate) (s : stack) (h : pheap) (q : Qc),
                  (st = (s, h)) -> (this h (ledenot e s) = Some (q, v)) ->
                  (st' = (var_upd s x v, h)) ->
                  (x ::T cty ::= [e]) / st || None / st'
  | eval_Write : forall (e1 : loc_exp) (e2 : exp) (ss ss' : pstate) (s : stack) (h : pheap) (v : Z),
                   (ss = (s, h)) ->
                   this h (ledenot e1 s) = Some (1%Qc, v) ->
                   (ss' = (s, ph_upd2 h (ledenot e1 s) (edenot e2 s))) ->
                   (Cwrite e1 e2) / ss || None / ss'
  | eval_Barrier : forall ss j,
                     (Cbarrier j) / ss || Some (j, Cskip) / ss
                                  where " c '/' s '||' c' '/' s'" := (eval c s c' s').
  
  Lemma red1_eval (c1 c2 : cmd) (st1 st2 : pstate) (st : pstate) : 
    c1 / st1 ==>p c2 / st2 -> c2 / st2 || None / st -> c1 / st1 || None / st.
  Proof.
    intros H IH.
    destruct H as
        [c c' st' st'' pst pst' s s' ph ph' phF h h' eq eq' 
            peq peq' aok wok dis to red dis' to'].
    revert st IH; induction red; intros; simpl in *; eauto; intros; subst; 
    repeat (match goal with [H : (_, _) = (_, _) |- _ ] => inversion H; subst; clear H end); 
    try assert (ph = ph') by (eapply phplus_cancel_toheap; eauto); subst;
    try (constructor; tauto).
    - econstructor; [econstructor | eauto].
    - inversion IH; subst; unfold access_ok, write_ok in *; simpl in *. 
      pose proof (IHred eq_refl eq_refl aok wok _ H1).
      econstructor; eauto.
    (* - apply eval_If2; eauto. *)
    - eapply eval_Assign; eauto.
      inversion IH; subst; eauto.
    - unfold access_ok in *; simpl in *; destruct aok as [[q v'] h].
      eapply eval_Read; eauto.
      inversion IH; subst.
      unfold ptoheap, phplus in to; specialize (to (ledenot e s0)); rewrite h in to;
      destruct (this phF (ledenot e s0)) as [[? ?] |]; destruct to as [? H'];
      rewrite H' in *; inversion RD; eauto.
    - unfold write_ok in *; simpl in *; destruct wok as [v' h];
      eapply eval_Write; eauto.
      inversion IH; subst; eauto.
      cutrewrite (ph' = ph_upd2 ph (ledenot e1 s0) (edenot e2 s0)); eauto.
      assert (this ph' = this (ph_upd2 ph (ledenot e1 s0) (edenot e2 s0))) by 
          (eapply padd_upd_cancel; eauto).
      destruct ph'; simpl in H.
      unfold ph_upd2.
      symmetry in H; destruct H.
      cutrewrite (is_p = ph_upd_ph ph (ledenot e1 s0) (edenot e2 s0)); 
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
    revert Heqs'; induction H.
    - intros H; rewrite H; clear H; simpl; apply eval_Skip.
    - intros Hz; apply IHclos_refl_trans_1n in Hz.
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
    revert Heqs'; induction hs.
    - intros ->.
      revert c'' j hwait; induction c'; intros c'' j' hwait; inversion hwait.
      + destruct (wait c'1); eauto.
        * destruct p as (j'', c'); simpl in *.
          apply eval_Seq1.
          now apply IHc'1.
        * inversion H0.
      + apply eval_Barrier.
    - intros ->; simpl in *.
      assert ((c', st') = (c', st')) as IH by eauto; apply IHhs in IH; clear IHhs; simpl in *.
      clear hs hwait c' c st.
      unfold red_p_tup in H.
      destruct H as [c c' stp' stp'' pst pst' s s' ph ph' phF h h' eq eq' 
                     peq peq' aok wok dis to red dis' to'].
      revert c'' IH; induction red; simpl in *; eauto; intros; subst; try inversion eq'; subst;
      try assert (ph = ph') by (eapply phplus_cancel_toheap; eauto); subst;
      try (econstructor; tauto).
      + eapply eval_Seq2; [apply eval_Skip | eauto ].
      + inversion IH; subst;
        unfold access_ok, write_ok in *; simpl in *.
        * apply eval_Seq1; eauto.
        * eapply eval_Seq2; eauto.
          eapply red1_eval; eauto.
          apply (@redp_ster _ _ (s, h) (s', h') (s, ph) (s', ph') s s' ph ph' phF h h'); eauto.
      (* + apply eval_If2; eauto. *)
      + inversion IH.
      + inversion IH.
      + inversion IH.
  Qed.
End BigStep.

Export BigStep.

Section ParSem.
  Variable ntrd : nat.
  Definition klist := Vector.t (cmd * stack) ntrd.
  Definition kstate := (klist * heap)%type.
  Definition kidx := Fin.t ntrd.

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
  Import VectorNotations.
  Definition abort_k (ks : kstate) :=
    exists (tid : Fin.t ntrd), 
      let (c, s) := (fst ks)[@tid] in aborts c (s, snd ks).
End ParSem.

Notation "ks '==>k' ks'" := (red_k ks ks') (at level 40).
Definition multi_red_k (ntrd : nat) (k1 k2 : kstate ntrd) := clos_refl_trans_1n _ (@red_k ntrd) k1 k2.
Notation "ks '==>k*' ks'" := (multi_red_k ks ks') (at level 40).

Section ParNAborts.
  Variable ntrd : nat.
  Import VectorNotations.
  Lemma naborts_red_k (ks1 ks2 : klist ntrd) (h1 h2 hF : heap) :
    hdisj h1 hF -> hdisj h2 hF ->
    ~abort_k (ks1, h1) ->
    (ks1, hplus h1 hF) ==>k (ks2, hplus h2 hF) ->
    (ks1, h1) ==>k (ks2, h2).
  Proof.
    intros Hdis1 Hdis2 Hnaborts Hred.
    remember (ks1, hplus h1 hF) as kss1; remember (ks2, hplus h2 hF) as kss2; 
    destruct Hred.
    - assert (~aborts c (s, h1)) as Hnab.
      { intros Hc; contradict Hnaborts; exists i; simpl.
        destruct ks; inversion Heqkss1; inversion H; repeat subst; destruct ss[@i]; inversion H0;
        subst; eauto. }
      rewrite H2, H3 in H1.
      cutrewrite (h = hplus h1 hF) in H1; [|inversion Heqkss1; congruence].
      cutrewrite (h' = hplus h2 hF) in H1; [|inversion Heqkss2; congruence].
      apply naborts_red_s in H1; eauto.
      inversion Heqkss2.
      cutrewrite (ks1 = ss); [|destruct ks; inversion Heqkss1; inversion H; congruence].
      apply (redk_Seq eq_refl H0 H1 eq_refl eq_refl).
    - cutrewrite (ks1 = ss); [|destruct ks; inversion Heqkss1; inversion H; congruence].
      cutrewrite (ks2 = ss'); [|destruct ks'; inversion Heqkss2; inversion H0; congruence].
      assert (hplus h2 hF = hplus h1 hF) as H12eq.
      { destruct ks, ks'; inversion Heqkss1; inversion Heqkss2; inversion H; inversion H0;
        congruence. }
      cutrewrite (h1 = h2); [| eapply (hplus_cancel_l (h := hplus h1 hF) Hdis1 Hdis2); congruence].
      apply (redk_Barrier eq_refl eq_refl H1).
  Qed.
End ParNAborts.
  
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
  | ty_var : forall (v : var) (ty : type), le_type (g v) ty = true -> typing_exp (Evar v) ty
  | ty_num : forall (n : Z) (ty : type), typing_exp (Enum n) ty
  | ty_binop : forall (op : binop_exp) (e1 e2 : exp) (ty1 ty2 : type), 
                typing_exp e1 ty1 -> typing_exp e2 ty2 ->
                typing_exp (Ebinop op e1 e2) (join ty1 ty2).

  Inductive typing_bexp : bexp -> type -> Prop := 
  | ty_comp : forall op (e1 e2 : exp) (ty1 ty2 : type),
      typing_exp e1 ty1 -> typing_exp e2 ty2 ->
      typing_bexp (Bcomp op e1 e2) (join ty1 ty2)
  | ty_bool : forall op (e1 e2 : bexp) (ty1 ty2 : type),
      typing_bexp e1 ty1 -> typing_bexp e2 ty2 ->
      typing_bexp (Bbool op e1 e2) (join ty1 ty2)
  | ty_unary : forall op (e : bexp) (ty : type),
      typing_bexp e ty -> typing_bexp (Bunary op e) ty.

  Inductive typing_lexp : loc_exp -> type -> Prop :=
  | ty_sloc : forall e ty, typing_exp e ty -> typing_lexp (Sh e) ty
  | ty_gloc : forall e ty, typing_exp e ty -> typing_lexp (Gl e) ty
  | ty_offset : forall e e' ty1 ty2, typing_lexp e ty1 -> typing_exp e' ty2 ->
                                     typing_lexp (loc_offset e e') (join ty1 ty2).

  Inductive typing_cmd : cmd -> type -> Prop :=
  | ty_skip : forall (pc : type), typing_cmd Cskip pc
  | ty_assign : forall (v : var) (e : exp) (pc ty : type) (cty : option CTyp),
                  typing_exp e ty -> le_type (join ty pc) (g v) = true ->
                  typing_cmd (v ::T cty ::= e) pc
  | ty_read : forall (v : var) (e : loc_exp) (pc ty : type) (cty : option CTyp),
                typing_lexp e ty -> le_type (join ty pc) (g v) = true ->
                typing_cmd (v ::T cty ::= [e]) pc
  | ty_write : forall (e1 : loc_exp) (e2 : exp) (pc : type),
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
    low_eq s1 s2 -> g x = Hi -> low_eq (var_upd s1 x v1) (var_upd s2 x v2).
  Proof.
    unfold var_upd; intros heq hhi y; destruct (var_eq_dec y x); subst.
    - intros h; rewrite hhi in h; inversion h.
    - intros h; apply heq in h; eauto.
  Qed.

  Lemma low_eq_eq_exp (e : exp) (s1 s2 : stack) :
    low_eq s1 s2 -> typing_exp e Lo -> edenot e s1 = edenot e s2.
  Proof.
    intros heq hty; induction e; simpl; eauto; 
    try now (inversion hty; destruct ty1, ty2; unfold join in *; try congruence;
             rewrite IHe1, IHe2; eauto).
    - inversion hty; specialize (heq x).
      destruct (g x); unfold le_type in H0; try congruence; eauto.
  Qed.

  Lemma low_eq_eq_lexp (e : loc_exp) (s1 s2 : stack) :
    low_eq s1 s2 -> typing_lexp e Lo -> ledenot e s1 = ledenot e s2.
  Proof.
    intros; induction e; simpl; f_equal; inversion H0; auto using low_eq_eq_exp.
    destruct ty1, ty2; inversion H3.
    erewrite IHe, low_eq_eq_exp; eauto.
  Qed.
  
  Lemma low_eq_eq_bexp (be : bexp) (s1 s2 : stack) :
    low_eq s1 s2 -> typing_bexp be Lo -> bdenot be s1 = bdenot be s2.
  Proof.
    intros heq hty; induction be; simpl; eauto.
    - inversion hty; subst.
      destruct ty1, ty2; inversion H3.
      cutrewrite (edenot e1 s1 = edenot e1 s2); [ | eapply low_eq_eq_exp; eauto].
      cutrewrite (edenot e2 s1 = edenot e2 s2); [ | eapply low_eq_eq_exp; eauto].
      eauto.
    - inversion hty.
      destruct ty1, ty2; inversion H3.
      rewrite IHbe1, IHbe2; eauto.
    - inversion hty.
      rewrite (IHbe H0); eauto.
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
      cutrewrite (join ty Hi = Hi) in H6; [ | destruct ty; eauto].
      assert (g x = Hi) by (destruct (g x); inversion H6; eauto).
      destruct hcomp as [heq ?];
        repeat split; destruct st1 as [s1 h1]; simpl; eauto.
      intros y; unfold var_upd; destruct (var_eq_dec y x); subst.
      + intros H'; congruence.
      + specialize (heq y); eauto.
    - inversion htng1; subst.
      cutrewrite (join ty Hi = Hi) in H7; [ | destruct ty; eauto].
      assert (g x = Hi) by (destruct (g x); inversion H7; eauto).
      destruct st1 as [s' h'], hcomp as [heq hdisj]; simpl in *.
      repeat split; eauto; simpl.
      intros y; unfold var_upd; destruct (var_eq_dec y x); subst.
      + intros H'; congruence.
      + specialize (heq y); simpl; eauto.
    - subst; destruct st1, hcomp; unfold st_compat in *; simpl in *; repeat split; eauto.
      apply pdisjC. apply (pdisj_upd _ _ H0); apply pdisjC; eauto.
    - inversion htng1.
  Qed.

  Lemma st_compat_sym (st1 st2 : pstate) : st_compat st1 st2 -> st_compat st2 st1.
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
    pose proof (non_interference_hi htng1 (st_compat_sym hc2) ev1) as [hc3 hc4].
    subst; split; eauto.
    apply st_compat_sym; eauto.
  Qed.

  Lemma non_interference_big (ty : type) (c : cmd) (st1 st2 st1' st2' : pstate) (t1 t2 : terminal) :
    typing_cmd c ty -> st_compat st1 st2 ->
    c / st1 || t1 / st1' -> c / st2 || t2 / st2' -> t1 = t2 /\ st_compat st1' st2'.
  Proof.
    intros htng hcomp ev1 ev2.
    revert hcomp ev2; generalize st2 st2' t2; clear st2 st2' t2; induction ev1;
    intros st2 st2' t2 hcomp ev2; unfold st_compat in *.
    - inversion ev2; repeat split; subst; intuition eauto.
    - inversion htng; subst.
      inversion ev2; subst.
      + pose proof (IHev1 H1 _ _ _ hcomp H6) as H; clear IHev1; rename H into IHev1.
        destruct IHev1 as [hteq ?]; split; eauto.
        inversion hteq; subst; eauto.
      + pose proof (IHev1 H1 _ _ _ hcomp H2) as H; clear IHev1; rename H into IHev1.
        destruct IHev1 as [H ?]; inversion H.
    - inversion htng; subst.
      inversion ev2; subst.
      + pose proof (IHev1_1 H1 _ _ _ hcomp H6) as [H ?]; inversion H.
      + pose proof (IHev1_1 H1 _ _ _ hcomp H2) as [_ hcomp'].
        apply (IHev1_2 H3 _ _ _ hcomp' H7).
    - inversion htng; subst.
      rename H3 into htngb, H5 into htng1, H6 into htng2.
      inversion ev2; subst.
      + destruct ty0.
        * assert (join ty Hi = Hi) as Hr by (destruct ty; eauto); rewrite Hr in *; clear Hr.
          eapply (non_interference_hi2 htng1 htng1 hcomp ev1 H7).
        * destruct ty; [eapply (non_interference_hi2 htng1 htng1 hcomp ev1 H7)|].
          apply (IHev1 htng1 _ _ _ hcomp); eauto.
      + destruct ty0.
        * assert (join ty Hi = Hi) as Hr by (destruct ty; eauto); rewrite Hr in *; clear Hr.
          eapply (non_interference_hi2 htng1 htng2 hcomp ev1 H7).
        * destruct ty; [eapply (non_interference_hi2 htng1 htng2 hcomp ev1 H7)|].
          pose proof (low_eq_eq_bexp (proj1 hcomp) htngb); congruence.
    - inversion htng; subst.
      rename H3 into htngb, H5 into htng1, H6 into htng2.
      inversion ev2; subst.
      + destruct ty0.
        * assert (join ty Hi = Hi) as Hr by (destruct ty; eauto); rewrite Hr in *; clear Hr.
          eapply (non_interference_hi2 htng2 htng1  hcomp ev1 H7).
        * destruct ty; [eapply (non_interference_hi2 htng2 htng1 hcomp ev1 H7)|].
          pose proof (low_eq_eq_bexp (proj1 hcomp) htngb); congruence.
      + destruct ty0.
        * assert (join ty Hi = Hi) as Hr by (destruct ty; eauto); rewrite Hr in *; clear Hr.
          eapply (non_interference_hi2 htng2 htng2 hcomp ev1 H7).
        * destruct ty; [eapply (non_interference_hi2 htng2 htng2 hcomp ev1 H7)|].
          apply (IHev1 htng2 _ _ _ hcomp); eauto.
    - inversion ev2; subst.
      inversion H4; subst.
      + assert (typing_cmd (Cif b (c;; Cwhile b c) SKIP) ty).
        { inversion htng; subst; repeat (econstructor; eauto).
          destruct ty, ty0; eauto. }
        apply (IHev1 H _ _ _ hcomp H4).
      + inversion H7; subst.
        inversion ev1; subst; try (inversion H9; subst; tauto).
        destruct ty; inversion htng; subst.
        * cutrewrite (join Hi ty = Hi) in H3; [|eauto].
          pose proof (st_compat_sym hcomp).
          assert (typing_cmd (c ;; Cwhile b c) Hi) by (econstructor; eauto).
          pose proof (non_interference_hi H0 H H9).
          destruct H2 as [? H']; split; [eauto | apply (st_compat_sym H')].
        * destruct ty.
          { assert (typing_cmd (Cwhile b c) Hi) by (econstructor; eauto).
            assert (typing_cmd (c;; Cwhile b c) Hi) by (econstructor; eauto).
            pose proof (non_interference_hi H0 (st_compat_sym hcomp) H9).
            destruct H2 as [? H']; split; [eauto | apply (st_compat_sym H')]. }
          pose proof (low_eq_eq_bexp (proj1 hcomp) H1); congruence.
    - inversion ev2; subst; simpl in *; repeat split; eauto; [|  intuition eauto].
      destruct ty; inversion htng; subst.
      + inversion H4; apply hi_low_eq; intuition eauto.
        destruct ty, (g x); unfold le_type in *; simpl in *; inversion H4; eauto.
      + intros y hlo; pose proof ((proj1 hcomp) y hlo); unfold var_upd; destruct (var_eq_dec y x); eauto; subst.
        eapply low_eq_eq_exp; intuition eauto.
        destruct ty, (g x); simpl in H4; inversion H4; inversion hlo; eauto.
    - inversion ev2; subst; simpl in *; repeat split; [ | intuition eauto].
      destruct ty; inversion htng; subst.
      + apply hi_low_eq; intuition eauto.
        destruct ty, (g x); unfold le_type in *; simpl in *; inversion H5; intuition eauto.
      + intros y hlo; pose proof ((proj1 hcomp) y hlo); unfold var_upd; destruct (var_eq_dec y x); eauto; subst.
        destruct ty, (g x); simpl in H5; inversion H5; inversion hlo; eauto.
        assert (ledenot e s = ledenot e s0) by (apply low_eq_eq_lexp; intuition eauto).
        rewrite H1 in *.
        eapply pheap_disj_eq; intuition eauto.
    - inversion ev2; subst; simpl in *; repeat split; intuition eauto.
      apply (pheap_disj_disj _ _ H1 H0 H5).
    - inversion ev2; subst; repeat split; intuition eauto.
  Qed.

  Theorem non_interference_p1 (ty : type) (c : cmd) (st1 st2 st1' st2' : pstate) :
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
          (j1 : nat) :
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

  Lemma weaken_type (ty ty' : type) (c : cmd) : le_type ty' ty = true -> typing_cmd c ty -> typing_cmd c ty'.
  Proof.
    intros le htyp; revert ty' le; induction htyp; intros ty' hle; try (constructor; eauto).
    - econstructor; eauto. 
      destruct ty, pc, ty', (g v); eauto.
    - econstructor; eauto.
      destruct ty, pc, ty', (g v); eauto.
    - econstructor; eauto; [apply IHhtyp1 | apply IHhtyp2]; destruct ty, ty', pc; eauto.
    - econstructor; eauto; apply IHhtyp; destruct ty, ty', pc; eauto.
    - destruct ty'; inversion hle; constructor.
  Qed.

  Hint Resolve weaken_type.
  Lemma preservation_big (ty  : type) (c c' : cmd) (st st' : pstate) (j : nat) (t : terminal) :
    typing_cmd c ty -> c / st || t / st' -> t = Some (j, c') -> exists ty', typing_cmd c' ty'.
  Proof.
    intros htyp heval; generalize dependent ty; revert j c'; induction heval; intros j' c'' ty htyp; 
    inversion 1; subst; try tauto; inversion htyp; subst.
    - pose proof (IHheval j' c1' ty H2 eq_refl) as [ty' ?];
      exists Lo; econstructor; eauto.
    - eapply IHheval2; eauto.
    - eapply IHheval; destruct ty0, ty; eauto.
    - eapply IHheval; destruct ty0, ty; eauto.
    - assert (typing_cmd (Cif b (c;; Cwhile b c) SKIP) (join ty ty0)).
      repeat econstructor; eauto; destruct ty, ty0; eauto.
      apply (IHheval j' c'' (join ty ty0) H eq_refl).
    - exists Lo; constructor.
  Qed.
End NonInter.

Section Substitution.
  (* from CSLsound.v *)
  Fixpoint subE x e e0 := 
    match e0 with 
      | Evar y => (if var_eq_dec x y then e else Evar y)
      | Enum n => Enum n
      | Ebinop op e1 e2 => Ebinop op (subE x e e1) (subE x e e2)
    end.
  Fixpoint sublE x e e0 := 
    match e0 with 
      | Sh e0 => Sh (subE x e e0)
      | Gl e0 => Gl (subE x e e0)
      | loc_offset e1 e2 => loc_offset (sublE x e e1) (subE x e e2) 
    end.
  (* b[x/e]*)
  Fixpoint subB x e b :=
    match b with
    | Bcomp op e1 e2 => Bcomp op (subE x e e1) (subE x e e2)
    | Bbool op b1 b2 => Bbool op (subB x e b1) (subB x e b2)
    | Bunary op b1 => Bunary op (subB x e b1)
    end.

  Lemma subE_assign : forall (x : var) (e e' : exp) (s : stack),
    edenot (subE x e e') s = edenot e' (var_upd s x (edenot e s)).
  Proof.
    intros; induction e'; simpl; eauto; unfold var_upd; 
    repeat match goal with [ |- context[if ?X then _ else _]] => 
                           destruct X
           end; try congruence; eauto; f_equal; eauto;
    rewrite IHe'1, IHe'2 in *; tauto.
  Qed.

  Lemma sublE_assign : forall (x : var) (e : exp) (e' : loc_exp) (s : stack),
    ledenot (sublE x e e') s = ledenot e' (var_upd s x (edenot e s)).
  Proof.
    intros; induction e'; simpl; try destruct p; simpl; eauto; rewrite subE_assign; eauto.
    rewrite IHe'; auto.
  Qed.

  Lemma subB_assign : forall (x : var) (e : exp) (b : bexp) (s : stack),
    bdenot (subB x e b) s = bdenot b (var_upd s x (edenot e s)).
  Proof.
    intros; induction b; simpl;
    repeat match goal with [ |- context[if Z.eq_dec ?x ?y then _ else _]] => 
                           destruct (Z.eq_dec x y) end;
    repeat match goal with [ |- context[if Z_lt_dec ?x ?y then _ else _]] => 
                           destruct (Z_lt_dec x y) end;
    repeat rewrite subE_assign in *; congruence.
  Qed.
End Substitution.

Notation simple_heap := (PHeap.heap Z).

Section GlobalSemantics.
  Variable nblk : nat.
  Variable ntrd : nat.

  Record g_state :=
    Gs {blks : Vector.t (klist ntrd) nblk;
        sh_hp : Vector.t simple_heap nblk;
        gl_hp : simple_heap}.

  Import VectorNotations.

  Definition sh_gl_heap (sh gh : simple_heap) : heap :=
    fun (l : loc) => match l with
      | SLoc l => sh l
      | GLoc l => gh l
    end.

  Definition bs_of_gs (gs : g_state) (bid : Fin.t nblk) :=
    ((blks gs)[@bid], (sh_gl_heap (sh_hp gs)[@bid] (gl_hp gs))).

  Definition abort_g (gs : g_state) :=
    exists (gid : Fin.t nblk), abort_k (bs_of_gs gs gid).
  
  Reserved Notation "gs '==>g' gs'" (at level 40).
  Inductive red_g : g_state -> g_state -> Prop :=
    | redg_Seq : forall (gs1 : g_state) (bid : Fin.t nblk) ks' gh' gh'' sh'',
        (bs_of_gs gs1 bid)  ==>k (ks', gh') ->
        (forall l, gh' l = (sh_gl_heap sh'' gh'') l) ->
        gs1 ==>g Gs (replace (blks gs1) bid ks') (replace (sh_hp gs1) bid sh'') gh''
  where
    "gs ==>g gs'" := (red_g gs gs').
End GlobalSemantics.