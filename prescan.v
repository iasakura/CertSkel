(* 
  parallel prescan algorithm 
  
  loop invariant
  f_c(i) = let 2 ^ k * n := i + 1 in
           let m := max (2 ^ k, offset) in
           sum (i + 1 - m, m, f)
 *)

(* 
original code (from Barrier Invariants: ...) 

// data, out, flag, idx: arrays in shared memory
unsigned offset, d, left, right, temp;
// (i) test each element with predicate p
flag[tid] = p(data[tid]);

// (ii) compute indices for compaction
barrier(); // ϕload

if (tid < n/2) {
  idx[2∗tid] = flag[2∗tid]; idx[2∗tid + 1] = flag[2∗tid + 1];
}
// (ii)(a) upsweep offset = 1;
for (d = n/2; d > 0; d /= 2) {
  barrier(); // ϕus
  if (tid < d) {
    left = offset ∗ (2 ∗ tid + 1) − 1;
    right = offset ∗ (2 ∗ tid + 2) − 1;
    idx[right] += idx[left];
  }
  offset ∗= 2;
}

// (ii)(b) downsweep 
if (tid == 0) idx[n−1] = 0;
for (d = 1; d < n; d ∗= 2) {
  offset /= 2;
  barrier(); // ϕds
  if (tid < d) { 
    left = offset ∗ (2 ∗ tid + 1) − 1;
    right = offset ∗ (2 ∗ tid + 2) − 1;
    temp = idx[left];
    idx[left] = idx[right]; idx[right] += temp;
  }
}
barrier(); // ϕspec
// (iii) compaction if (flag[tid]) out[idx[tid]] = data[tid];
*)

Require Import GPUCSL scan_lib.

Section Prescan.
Notation Tid := (Var 0).
Notation In := (Var 1). 
Notation Sum := (Var 2).
Notation Pres := (Var 3).

Notation D := (Var 4).
Notation Offset := (Var 5).
Notation Tmp1 := (Var 6).
Notation Tmp2 := (Var 7).

Infix "+C" := (Eplus) (at level 50).
Infix "*C" := (Emult) (at level 40).
Infix "-C" := (Esub) (at level 50).
Infix "<C" := (Blt) (at level 70).

Notation leftC ARR := (ARR +C Offset *C (Enum 2 *C Tid +C Enum 1) -C Enum 1).
Notation rightC ARR := (ARR +C Offset *C (Enum 2 *C Tid +C Enum 2) -C Enum 1).

Notation Zn := Z.of_nat.

Variable f_ini : nat -> Z.
Variable ntrd : nat.

Hypothesis ntrd_is_p2 : exists e, ntrd = 2 ^ e.
Lemma ntrd_neq_0 : ntrd <> 0.
Proof.
  destruct ntrd_is_p2; rewrite H; apply Nat.pow_nonzero; auto.
Qed.

Require Import Recdef.

Function rdiv2 n {wf lt n} :=
  match n with
    | 0 => 0
    | _ => if Nat.eq_dec (n mod 2) 0 then S (rdiv2 (n / 2)) else 0
  end%nat.
Proof.
  intros; destruct Nat.eq_dec; try omega.
  apply Nat.div_lt; omega.
  apply lt_wf.
Defined.

Definition upInv (i : nat) :=
  Ex (offset d : nat) (f : nat -> Z), 
    !(Tid === Zn i) **
    !(Offset === Zn offset) **
    !(D === Zn d) **
    !(pure ((d = 0) /\ (offset = ntrd * 2) \/ (d * offset = ntrd))) **
    !(pure (forall i, f i = let m := min (2 ^ rdiv2 (i + 1)) offset in
                      sum_of (i + 1 - m) m f_ini)) **
    (if lt_dec i (ceil2 d) then is_array Sum (Nat.max 2 offset) f (i * (Nat.max 2 offset)) else emp).

Definition bspec n :=
  if Nat.eq_dec n 0 then
    (MyVector.init (fun i : Fin.t ntrd => 
       Ex (offset d : nat) (f : nat -> Z), 
       !(Tid === Zn (nf i)) **
       !(Offset === Zn offset) **
       !(D === Zn d) **
       !(pure ((d = 0) /\ (offset = ntrd * 2) \/ (d * offset = ntrd))) **
       !(pure (forall i, f i = let m := min (2 ^ rdiv2 (i + 1)) offset in
                               sum_of (i + 1 - m) m f_ini)) **
       (if lt_dec (nf i) d then
          is_array Sum (Nat.max 2 offset) f ((nf i) * (Nat.max 2 offset))
        else emp)),
     MyVector.init (fun i : Fin.t ntrd => 
       Ex (offset d : nat) (f : nat -> Z), 
       !(Tid === (Zn (nf i))) **
       !(Offset === Zn offset) **
       !(D === Zn d) **
       !(pure ((d = 0) /\ (offset = ntrd * 2) \/ (d * offset = ntrd))) **
       !(pure (forall i, f i = let m := min (2 ^ rdiv2 (i + 1)) offset in
                               sum_of (i + 1 - m) m f_ini)) **
       (if lt_dec (nf i) (ceil2 d) then is_array Sum (offset * 2) f ((nf i) * offset * 2) else emp)))
  else default ntrd.

Definition upsweep (i : nat) :=
  Offset ::= 1%Z ;;
  D ::= Zn ntrd ;;
  WhileI (upInv i) (0%Z <C D) (
    Cbarrier 0 ;;
    Cif (Tid <C D) (
      Tmp1 ::= [leftC Sum] ;;
      Tmp2 ::= [rightC Sum] ;;
      [rightC Sum] ::= Tmp1 +C Tmp2
    ) (Cskip) ;;
    Offset ::= Offset *C 2%Z ;;
    D ::= D>>1
  ).

Ltac ex_dest_in H id :=
  lazymatch type of H with
    | ((Ex _, _) ** _) _ _ => apply ex_lift_l_in in H; destruct H as [id H]
    | (_ ** (Ex _, _)) _ _ => apply ex_lift_r_in in H; destruct H as [id H]
end.

(* TODO: ex_lift_rに対応 *)
Ltac sep_ex :=
  lazymatch goal with
    | [ |- ((Ex _, _) ** _) _ _] => apply ex_lift_l
  end.

Lemma fin_lt (n : nat) (i : Fin.t n) : (nf i) < n.
Proof.
  destruct (Fin.to_nat i); simpl; auto.
Qed.

Lemma is_array_unfold Arr len' f : forall s len,
  len' < len ->
  forall stc, 
    stc ||= is_array Arr len f s <=>
        is_array Arr len' f s **
        (Arr +C (Zn (len' + s))%Z -->p (1, f (len' + s))) **
        is_array Arr (len - len' - 1) f (S (len' + s)).
Proof.
  induction len'; intros s len Hlen stc.
  - destruct len; try omega; simpl.
    rewrite <-minus_n_O, emp_unit_l; reflexivity.
  - destruct len; [inversion Hlen|]; simpl.
    rewrite IHlen'; try omega.
    rewrite <-plus_n_Sm; simpl; rewrite sep_assoc; autorewrite with sep. reflexivity.
Qed.

Hint Rewrite Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_sub : sep.
Arguments div _ _ : simpl never.
Arguments Nat.max _ _ : simpl never.

Lemma div_pow2 : forall e n m, n * m = 2 ^ e -> exists e1 e2, n = 2 ^ e1 /\ m = 2 ^ e2.
Proof.
  induction e; intros n m Hnm.
  - exists 0, 0; simpl.
    apply mult_is_one; auto.
  - rewrite pow_succ_r in Hnm; try omega.
    assert (n mod 2 = 0 \/ n mod 2 = 1) by (pose proof (Nat.mod_upper_bound n 2); omega).
    rewrite (Nat.div_mod n 2) in Hnm; auto; auto.
    destruct H; rewrite H in Hnm.
    + rewrite <-plus_n_O in Hnm.
      rewrite <-mult_assoc, Nat.mul_cancel_l in Hnm; auto.
      apply IHe in Hnm; try omega; destruct Hnm as (e1 & e2 & Hnm); exists (S e1), e2.
      rewrite (Nat.div_mod n 2), H; auto; simpl. omega.
    + assert (m mod 2 = 0 \/ m mod 2 = 1) by (pose proof (Nat.mod_upper_bound m 2); omega).
      rewrite (Nat.div_mod m 2) in Hnm; auto; auto.
      destruct H0; rewrite H0 in Hnm.
      rewrite <-plus_n_O in Hnm.
      rewrite <-mult_comm, <-mult_assoc, Nat.mul_cancel_l in Hnm; auto.
      apply IHe in Hnm as (e1 & e2 & Hnm); exists e2, (S e1).
      rewrite (Nat.div_mod m 2), (Nat.div_mod n 2), H, H0; simpl; omega.
      ring_simplify in Hnm. 
      cutrewrite (4 * (n / 2) * (m / 2) + 2 * (n / 2) + 2 * (m / 2) + 1 =
                  2 * (2 * (n / 2) * (m / 2) + (n / 2) + (m / 2)) + 1) in Hnm; [omega|].
      ring.
Qed.

Lemma rdiv2_mult (n m : nat) : m <> 0 -> 2 ^ n <= 2 ^ rdiv2 (2 ^ n * m).
Proof.
  intros Hm0; remember (2 ^ n * m) as nm eqn:eqnm; revert n m eqnm Hm0; functional induction (rdiv2 nm).
  - intros; symmetry in eqnm; apply mult_is_O in eqnm; omega.
  - intros n' m Hnm Hm0.
    destruct n'; subst; [simpl; autorewrite with sep;
                         pose proof (Nat.pow_nonzero 2 (rdiv2 (m / 2))); omega|].
    rewrite !Nat.pow_succ_r', <-Nat.mul_le_mono_pos_l; auto.
    eapply (IHn _ m); auto.
    rewrite Nat.pow_succ_r'. 
    cutrewrite (2 * 2 ^ n' * m = 2 ^ n' * m * 2); [|ring]; rewrite Nat.div_mul; auto.
  - intros n' m Hnm Hm0.
    destruct n'; auto; subst.
    clear e0; rewrite Nat.pow_succ_r' in _x0. rewrite <-mult_assoc, mult_comm in _x0.
    rewrite  Nat.mod_mul in _x0; omega.
Qed.


Lemma is_array_unfold' Arr len f : forall s,
  0 < len ->
  forall stc, 
    stc ||= is_array Arr len f s <=>
        is_array Arr (len - 1) f s **
        (Arr +C (Zn (s + len - 1)) -->p (1, f (s + len - 1))).
Proof.
  induction len; intros s Hlen stc; try omega.
  destruct len.
  - simpl; rewrite <-plus_n_Sm, <-plus_n_O; simpl;
    rewrite emp_unit_l, emp_unit_r, <-minus_n_O; reflexivity.
  - remember (S len); simpl.
    rewrite IHlen; try omega.
    subst; simpl; rewrite <-!minus_n_O.
    rewrite <-(plus_n_Sm s (S len)); simpl; rewrite <-minus_n_O, sep_assoc. reflexivity.
Qed.

Hint Resolve fin_lt.

Lemma upsweep_correct (i : Fin.t ntrd) :
  CSL bspec i 
      (is_array Sum 1 f_ini (nf i))
      (upsweep (nf i))
      (if Nat.eq_dec (nf i) 0 then 
         Ex f, 
           !(pure (forall i, f i = let m := 2 ^ rdiv2 i in sum_of (i + 1 - m) m f)) ** 
           is_array Sum (ntrd * 2) f 0
       else emp).
Proof.
  pose proof ntrd_neq_0 as ntrd_neq_0.
  unfold upsweep.
  eapply rule_seq; [hoare_forward; intros ? ? [v H] | ].
  { remember 1 in H. subA_normalize_in H. simpl in H. subst; exact H. }
  eapply rule_seq; [hoare_forward; intros ? ? [v H] | ].
  { remember 1 in H; subA_normalize_in H. simpl in H. subst. exact H. }
  hoare_forward.
  Hint Unfold bspec upInv.
  
  eapply rule_seq; [hoare_forward|].
  { intros s h H.
    ex_dest_in H offset; ex_dest_in H d; ex_dest_in H f.
    sep_ex; exists offset; sep_ex; exists d; sep_ex; exists f.
    sep_split_in H; sep_normal; sep_split; eauto.
    change_in H.
    { unfold_pures; unfold ceil2 in H; destruct Nat.eq_dec; try omega.
      exact H. }
    sep_rewrite_in_r emp_unit_r H. apply H. }

  { autounfold; simpl; intros ? ? H; rewrite MyVector.init_spec in H. 
    sep_rewrite_in emp_unit_r H. exact H. }
  
  repeat hoare_forward; revert x x0 x1; intros offset d fc.
  eapply rule_seq. eapply rule_if_disj.
  
  { eapply Hbackward. 
    Focus 2.
    { intros s h H; sep_normal_in H; sep_split_in H.
      change_in H.
      { unfold_pures.
        Lemma ceil2_leq (n : nat) : n <= ceil2 n.
        Proof.
          unfold ceil2; destruct Nat.eq_dec; omega.
        Qed.
        destruct lt_dec.
        2: rewrite HP, HP1 in l; rewrite <-Nat2Z.inj_lt in l; pose proof (ceil2_leq d); omega.
        assert (Hoff0 : offset <> 0) by (intros Hc; subst; destruct HP2; omega).
        sep_rewrite_in is_array_unfold' H; try omega.
        sep_rewrite_in is_array_unfold H. 
        2: instantiate (1 := offset - 1); omega.
        cutrewrite (offset - 1 + nf i * offset * 2 = offset * (2 * nf i + 1) - 1) in H.
        Focus 2.
        { cutrewrite (offset * (2 * nf i + 1) = nf i * offset * 2 + offset); [|ring]. 
          generalize (nf i * offset * 2); intros; omega. } Unfocus.
        cutrewrite (nf i * offset * 2 + offset * 2 - 1 = offset * (2 * nf i + 2) - 1) in H.
        Focus 2.
        { cutrewrite (offset * (2 * nf i + 2) = nf i * offset * 2 + offset * 2); [|ring].
          omega. } Unfocus.

        autorewrite with sep in H;
          [|cutrewrite (1 = 1 * 1); [|auto]; apply Nat.mul_le_mono; omega..].
        assert ((Sum +C (Zn offset * (Zn 2 * Zn (nf i) + Zn 1) - Zn 1)%Z ===
                 Sum +C Zn offset *C (2 *C Zn (nf i) +C 1) -C 1) s emp_ph)%Z.
        { unfold_conn; simpl. omega. }
        sep_rewrite_in (mps_eq1) H; [|apply H0].
        assert ((Sum +C (Zn offset * (Zn 2 * Zn (nf i) + Zn 2) - Zn 1)%Z ===
                 Sum +C (Offset *C (2 *C Tid +C 2) -C 1)) s emp_ph)%Z.
        { Arguments Z.mul _ _ : simpl never.
          unfold_conn. simpl. congruence. }
        sep_normal_in H. sep_lift_in H 3.
        sep_rewrite_in (mps_eq1) H; [|apply H1].
        exact H. }
      (* Arguments Z.add _ _ : simpl never. *)
      (* Arguments Z.mul _ _ : simpl never. *)
      (* Arguments plus : simpl never. *)
      (* Arguments mult : simpl never. *)
      sep_combine_in H; exact H. } Unfocus.
    eapply rule_seq; [hoare_forward; intros ? ? H; exact H |].
    eapply rule_seq; [hoare_forward; intros ? ? H; exact H |].
    hoare_forward; intros ? ? H; exact H. }

  apply rule_skip.
  eapply Hforward.
  apply (rule_disj (Q1 := (upInv (nf i))) (Q2 := (upInv (nf i)))).  
  3: intros s h [H1 | H2]; eauto.
  eapply rule_seq; [hoare_forward; intros s h [v H]; subA_normalize_in H; ex_intro v H; simpl in H; exact H | ].
  repeat hoare_forward.
  intros s h [v H]; subA_normalize_in H. simpl in H; sep_split_in H.
  unfold_pures; subst; autorewrite with sep in *.
  exists (offset * 2), (d / 2).
  exists (fun x => if Nat.eq_dec ((x + 1) mod (offset * 2)) 0 then
                     (fc x + fc (x - offset)%nat)%Z
                   else fc x).
  sep_split; autorewrite with sep in *; eauto.
  - unfold_conn; rewrite HP3 in *; rewrite <-Nat2Z.inj_lt in l. 
    destruct HP6; try omega.
    pose proof (Nat.div_mod d 2).
    destruct ntrd_is_p2 as [e ntrd_2e]; rewrite ntrd_2e in H0; 
    pose proof (div_pow2 _ _ _ H0) as (e1 & e2 & Hdo).
    destruct e1; destruct Hdo; subst; [simpl; unfold div; simpl|].
    left; split; eauto; simpl in H0; omega.
    autorewrite with sep; auto.
    rewrite pow_succ_r in H0; try omega; rewrite <-H0; right; ring.
  - unfold_conn; intros ix.
    destruct Nat.eq_dec; rewrite !HP7.
    + assert (offset <> 0) by (destruct offset; destruct HP6; omega).
      rewrite (Nat.div_mod (ix + 1) (offset * 2)), e; try omega; autorewrite with sep.
    
    
      assert (exists e, offset = 2 ^ e) as [eoff Hoff].
      { destruct HP6 as [[? ?]|?]; destruct ntrd_is_p2 as [? ?].
        - subst; exists (S x); simpl; omega.
        - subst. apply div_pow2 in H2; destruct H2 as [? [? [? ?]]]; eexists; eauto. }
      assert ((ix + 1) / (2 ^ eoff * 2) <> 0).
      { rewrite Nat.div_small_iff; try omega.
        intros Hlt; rewrite Nat.mod_small in e; auto; omega. }
      assert (exists k, ix + 1 = 2 ^ eoff * 2 * k /\ k <> 0) as [kix [Hix1 ?]].
      { rewrite (Nat.div_mod (ix + 1) (2 ^ eoff * 2)); try omega; eexists; split.
        subst; rewrite e, <-plus_n_O. reflexivity.
        auto. }
      subst. rewrite Nat.min_r.
      2: rewrite <-mult_assoc; apply rdiv2_mult; omega.
      assert (2 ^eoff <= ix).
      { cutrewrite (ix = 2 ^ eoff * 2 * kix-1); [|omega].
        rewrite (mult_comm _ 2); simpl; autorewrite with sep.
        destruct kix; rewrite mult_comm; simpl; try omega.
        generalize (2 ^ eoff) H0; intros; destruct n; simpl. omega.
        generalize (kix * S (n + S n)); intros; omega. }
      rewrite <-Nat.add_sub_swap; auto.
      rewrite Hix1.
      cutrewrite (2 ^ eoff * 2 * kix - 2 ^ eoff = 2 ^ eoff * (2 * kix - 1)); [|].
      2: rewrite mult_minus_distr_l, mult_assoc, mult_1_r; auto.
      rewrite Nat.min_r; [|apply rdiv2_mult; omega].
      rewrite Nat.min_r; [|rewrite (mult_comm (2 ^ eoff) 2), <-Nat.pow_succ_r'; apply rdiv2_mult].
      2: rewrite mult_comm, Nat.div_mul; auto.
      rewrite (mult_comm (2 ^ eoff * 2) kix), Nat.div_mul; try omega.
      cutrewrite (2 ^ eoff * (2 * kix - 1) - 2 ^ eoff = 2 ^ eoff * 2 * kix - 2 ^ eoff * 2).
      2: rewrite mult_minus_distr_l, <-Nat.sub_add_distr; f_equal; ring.
      cutrewrite (2 ^ eoff * 2 = 2 ^ eoff + 2 ^ eoff); [|omega].
      rewrite sum_of_concat, Z.add_comm; f_equal.
      f_equal. 
      rewrite Nat.sub_add_distr, <-le_plus_minus; auto.
      destruct kix; simpl; try omega; rewrite mult_comm; simpl. generalize (kix * (2 ^ eoff + 2 ^ eoff)); intros; omega.
    + cutrewrite (min (2 ^ rdiv2 (ix + 1)) offset = min (2 ^ rdiv2 (ix + 1)) (offset * 2)); auto.
      
Definition downsweep :=
  D ::= 1 ;;
  WhileI (FalseP) (D <C len) (
    Offset ::= Offset >>1 ;;
    Cif (Tid <C D) (
      Tmp1 ::= [leftC Sum] ;;
      Tmp2 ::= [rightC Pres] ;;
      [leftC Pres] ::= Tmp2 ;;
      [rightC In] ::= Tmp1 +C Tmp2
    ) (Cskip) ;;
    Cbarrier 1 ;;
   D ::= D *C 2
  ).

