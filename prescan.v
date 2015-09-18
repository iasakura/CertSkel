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
     if lt_dec i (dbl d) then 
       !(pure (forall i, i < ntrd * 2 ->
                 f i = let m := min (2 ^ rdiv2 (i + 1)) offset in
                       sum_of (i + 1 - m) m f_ini)) **
        (is_array Sum (Nat.max 2 offset) f (i * (Nat.max 2 offset)))
     else
       emp.

  Definition bspec n :=
    if Nat.eq_dec n 0 then
      (MyVector.init (fun i : Fin.t ntrd => 
         Ex (offset d : nat) (f : nat -> Z), 
         !(Offset === Zn offset) **
         !(D === Zn d) **
         !(pure ((d = 0) /\ (offset = ntrd * 2) \/ (d * offset = ntrd))) **
         !(pure (0 < d)) **
         if lt_dec (nf i) (d * 2) then
              !(pure (forall i, i < ntrd * 2 ->
                                f i = let m := min (2 ^ rdiv2 (i + 1)) offset in
                                      sum_of (i + 1 - m) m f_ini)) **
            is_array Sum (Nat.max 2 offset) f ((nf i) * (Nat.max 2 offset))
         else emp),
       MyVector.init (fun i : Fin.t ntrd => 
         Ex (offset d : nat) (f : nat -> Z), 
           !(Offset === Zn offset) **
           !(D === Zn d) **
           !(pure ((d = 0) /\ (offset = ntrd * 2) \/ (d * offset = ntrd))) **
           !(pure (0 < d)) **
           if lt_dec (nf i) d then
             !(pure (forall i, i < ntrd * 2 ->
                               f i = let m := min (2 ^ rdiv2 (i + 1)) offset in
                                     sum_of (i + 1 - m) m f_ini)) **
              is_array Sum (offset * 2) f ((nf i) * offset * 2)
           else emp))
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
        (is_array Sum 2 f_ini (nf i * 2) ** !(Tid === Zn (nf i)))
        (upsweep (nf i))
        (if Nat.eq_dec (nf i) 0 then 
           Ex f, 
           !(pure (forall i, i < ntrd * 2 ->
                             f i = let m := 2 ^ rdiv2 (i + 1) in sum_of (i + 1 - m) m f_ini)) ** 
            is_array Sum (ntrd * 2) f 0
         else emp).
  Proof.
    pose proof ntrd_neq_0 as ntrd_neq_0.
    unfold upsweep.
    (* the 1st command *)
    eapply rule_seq; [hoare_forward; intros ? ? [v H] | ].
    { remember 1 in H. subA_normalize_in H. simpl in H. subst; exact H. }
    (* the snd command *)
    eapply rule_seq; [hoare_forward; intros ? ? [v H] | ].
    { remember 1 in H; subA_normalize_in H. simpl in H. subst. exact H. }
    hoare_forward.
    Hint Unfold bspec upInv.
    
    (* loop body *)
    (* barrier *)
    eapply rule_seq; [hoare_forward|].
    (* the barrier precondition holds *)
    { intros s h H.
      ex_dest_in H offset; ex_dest_in H d; ex_dest_in H f.
      sep_ex; exists offset; sep_ex; exists d; sep_ex; exists f.
      sep_split_in H. sep_normal; sep_split; eauto.
      { unfold_pures; unfold_conn; omega. }
      change_in H.
      { unfold_pures; unfold dbl in H; destruct Nat.eq_dec; try omega.
        exact H. }
      clear HP HP1 HP2 HP3.
      sep_combine_in H. apply H. }
    
    (* transform the barrier postcondition *)
    { autounfold; simpl; intros ? ? H; rewrite MyVector.init_spec in H.
      ex_dest_in H o; ex_dest_in H d; ex_dest_in H f.
      sep_normal_in H.
      ex_intro f H; ex_intro d H; ex_intro o H; simpl in H.
      exact H. }
    
    repeat hoare_forward; revert x x0 x1; intros offset d fc.
    eapply rule_seq. eapply rule_if_disj.
    
    (* then case of the branch *)
    { eapply Hbackward. 
      (* unfold the is_array predicate *)
      Focus 2.
      { intros s h H; sep_normal_in H; sep_split_in H.
        change_in H.
        { unfold_pures.
          Lemma ceil2_leq (n : nat) : n <= ceil2 n.
          Proof.
            unfold ceil2; destruct Nat.eq_dec; omega.
          Qed.
          destruct lt_dec.
          2: rewrite HP0, HP3 in l; rewrite <-Nat2Z.inj_lt in l; pose proof (ceil2_leq d);
             apply n in l; destruct l.
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
          unfold_conn. simpl.  repeat f_equal; auto. }
        sep_normal_in H. sep_lift_in H 4.
        sep_rewrite_in (mps_eq1) H; [|apply H1].
        exact H. }
      sep_combine_in H; exact H. } Unfocus.
    (* execute rest of commands *)
    eapply rule_seq; [hoare_forward; intros ? ? H; exact H |].
    eapply rule_seq; [hoare_forward; intros ? ? H; exact H |].
    hoare_forward; intros ? ? H; exact H. }

    (* else case *)
    apply rule_skip.

    (* rest of commands *)
    eapply Hforward.
    apply (rule_disj (Q1 := (upInv (nf i))) (Q2 := (upInv (nf i)))).  
    3: intros s h [H1 | H2]; eauto.

    (* rest of commands (then case) *)
    eapply rule_seq; [hoare_forward; intros s h [v H]; subA_normalize_in H; ex_intro v H; simpl in H; exact H | ].
    (* the loop invariant is preserved *)
    repeat hoare_forward.
    intros s h [v H]; subA_normalize_in H. simpl in H; sep_split_in H.
    unfold_pures; subst; autorewrite with sep in *.
    exists (offset * 2), (d / 2).
    set (fc' := fun x => if Nat.eq_dec ((x + 1) mod (offset * 2)) 0 then
                     (fc x + fc (x - offset)%nat)%Z
                   else fc x).
    exists fc'.
    destruct lt_dec; try omega.

    Focus 2.
    { rewrite HP7 in l; rewrite <-Nat2Z.inj_lt in l.
      destruct HP5; try omega.
      destruct ntrd_is_p2 as [? Hntrd]; rewrite Hntrd in H0; apply div_pow2 in H0 as (? & ? & ? & ?).
      subst; rewrite dbl_inv in n. tauto. } Unfocus.

    sep_split; autorewrite with sep in *; eauto.
    - unfold_conn; rewrite HP7 in *; rewrite <-Nat2Z.inj_lt in l. 
      destruct HP5; try omega.
      pose proof (Nat.div_mod d 2).
      destruct ntrd_is_p2 as [e ntrd_2e]; rewrite ntrd_2e in H0; 
      pose proof (div_pow2 _ _ _ H0) as (e1 & e2 & Hdo).
      destruct e1; destruct Hdo; subst; [simpl; unfold div; simpl|].
      left; split; eauto; simpl in H0; omega.
      autorewrite with sep; auto.
      rewrite pow_succ_r in H0; try omega; rewrite <-H0; right; ring.
    - unfold_conn; intros ix Hix; unfold fc' in *.
      destruct Nat.eq_dec; rewrite !HP9; try omega.
      + assert (offset <> 0) by (destruct offset; destruct HP6; omega).
        rewrite (Nat.div_mod (ix + 1) (offset * 2)), e; try omega; autorewrite with sep.
        
        assert (exists e, offset = 2 ^ e) as [eoff Hoff].
        { destruct HP5 as [[? ?]|?]; destruct ntrd_is_p2 as [? ?].
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
        destruct ntrd_is_p2 as [en Hen]; rewrite Hen in HP5.
        destruct HP5 as [? | HP5]; try omega; apply div_pow2 in HP5 as (eoff & ed & Heoff & Hed);subst.
        assert (Hle : rdiv2 (ix + 1) <= ed).
        2: apply (Nat.pow_le_mono_r 2) in Hle; try omega; rewrite !Min.min_l; omega.
        apply Nat.nlt_ge; intros Hc; unfold lt in Hc.
        
        Lemma rdiv2_div (x y : nat) : x <= rdiv2 y -> y mod (2 ^ x) = 0.
        Proof.
          revert x; functional induction (rdiv2 y); intros x Hx.
          - apply Nat.mod_0_l, Nat.pow_nonzero; omega.
          - destruct x; [simpl; auto|].
            clear e0; rewrite <-Nat.div_exact in _x0; auto; rewrite Nat.pow_succ_r', _x0.
            rewrite Nat.mul_mod_distr_l; auto; rewrite IHn; omega.
          - assert (x = 0) by omega; subst; simpl; auto.
        Qed.
        
        apply rdiv2_div in Hc; rewrite Nat.pow_succ_r', mult_comm in Hc; auto.
    - destruct HP5 as [? | HP5]; try omega.
      assert (offset <> 0) by (destruct offset; rewrite mult_comm in HP5; omega).
      cutrewrite (offset * 2 - 1 - (offset - 1) = offset) in H; [|omega].
      rewrite !mult_plus_distr_l, mult_1_r, minus_Sn_m in H; [|destruct offset; try omega; generalize (S offset * nf i); intros; try omega].
      simpl in H; rewrite <-minus_n_O in H; cutrewrite (offset * nf i + offset * nf i = offset * nf i * 2) in H; [|omega].
      rewrite (mult_comm (nf i) offset) in H.
      assert (Heq1 : ((Sum +C Zn offset *C (2%Z *C Tid +C 2%Z)) -C 1%Z ===
                                                                   Sum +C Zn (offset * nf i * 2 + offset + offset - 1)) s emp_ph).
      { unfold_conn; repeat autorewrite with sep; [|destruct offset; try omega; generalize (S offset * nf i * 2); intros; omega]; simpl.
        rewrite HP7. rewrite Z.add_sub_assoc. 
        ring_simplify. reflexivity. }
      sep_rewrite_in mps_eq1 H; [|exact Heq1]; clear Heq1.
      assert (Heq1 : ((Sum +C Zn offset *C (2%Z *C Tid +C 1%Z)) -C 1%Z ===
                                                                   Sum +C Zn (offset * nf i * 2 + offset - 1)) s emp_ph).
      { unfold_conn; repeat autorewrite with sep; [|destruct offset; try omega; generalize (S offset * nf i * 2); intros; omega]; simpl.
        rewrite HP7; ring_simplify; reflexivity. }
      sep_lift_in H 1; sep_rewrite_in mps_eq1 H; [|exact Heq1]; clear Heq1.
      (* sep_lift_in H 2. sep_lift_in H 3. sep_lift_in H 3. *)
      
      Lemma is_array_change (e : exp) (f1 f2 : nat -> Z) n :
        forall s, (forall x, x < n -> f1 (x + s) = f2(x + s)) ->
                  forall stc,
                    stc ||= is_array e n f1 s <=> is_array e n f2 s.
      Proof.
        induction n; simpl; intros s Hf; try reflexivity.
        intros stc; rewrite IHn.
        cutrewrite (f1 s = f2 s); [reflexivity|].
        pose proof (Hf 0); rewrite plus_O_n in H; rewrite H; omega.
        intros x Hx; rewrite <-Nat.add_succ_comm; apply Hf; omega.
      Qed.
      assert (Heq :fc (offset * nf i * 2 + offset - 1) =
                   fc' (offset * nf i * 2 + offset - 1)); [|rewrite Heq in H; clear Heq].
      unfold fc'; destruct Nat.eq_dec; auto.
      cutrewrite (offset * nf i * 2 + offset - 1 + 1 = offset * 1 + nf i * (offset * 2)) in e.
      rewrite Nat.mod_add, Nat.mul_mod_distr_l in e; simpl in e; try omega.
      rewrite <-Nat.add_sub_swap; try omega. 
      2: destruct offset; try omega; generalize (S offset * nf i * 2); intros; try omega.
      rewrite Nat.add_sub; ring.
      sep_rewrite_in (is_array_change Sum fc fc') H.
      Focus 2.
      { intros x Hx; unfold fc'; destruct Nat.eq_dec; auto.
        cutrewrite (x + offset * nf i * 2 + 1 = x + 1 + nf i * (offset * 2)) in e; [|ring].
        rewrite Nat.mod_add, <-Nat.div_exact in e; try omega.
        destruct ((x + 1) / (offset * 2)); rewrite (mult_comm (offset * 2)) in e; simpl in e; try omega.
        generalize (n * (offset * 2)) e; intros; omega. } Unfocus.
      sep_rewrite_in (is_array_change Sum fc fc') H.
      Focus 2.
      { intros x Hx; unfold fc'; destruct Nat.eq_dec; auto.
        cutrewrite (x + (offset * nf i * 2 + offset) + 1 = offset + x + 1 + nf i * (offset * 2)) in e; [|ring].
        rewrite Nat.mod_add, <-Nat.div_exact in e; try omega.
        destruct ((offset + x + 1) / (offset * 2)); rewrite (mult_comm (offset * 2)) in e; simpl in e; try omega.
        generalize (n * (offset * 2)) e; intros; omega. } Unfocus.
      assert (Heq : (Tmp1 +C Tmp2 === fc' (offset * nf i * 2 + offset + offset - 1)) s emp_ph).
      { unfold_conn; simpl; rewrite HP1, HP2; unfold fc'.
        cutrewrite (offset * nf i * 2 + offset + offset - 1 + 1 = 
                    (nf i + 1) * (offset * 2)).
        rewrite Nat.mod_mul; simpl; try omega; rewrite Z.add_comm; do 2 f_equal.
        f_equal; ring.
        rewrite <-Nat.sub_add_distr, (plus_comm 1 offset), Nat.sub_add_distr.
        f_equal; rewrite Nat.add_sub; ring.
        rewrite Nat.sub_add; [ring|].
        generalize (offset * nf i * 2); intros; omega. }
      sep_lift_in H 1; sep_rewrite_in (mps_eq2) H; [|exact Heq].
      sep_lift_in H 1. sep_lift_in H 2. sep_lift_in H 3. sep_lift_in H 3.
      sep_rewrite_in_r (is_array_unfold') H; try omega.
      sep_lift_in H 1. sep_lift_in H 2. 
      sep_rewrite_in_r (is_array_unfold') H; try omega.
      
      rewrite Nat.max_r; try omega.
    
      Lemma is_array_concat e f len1 len2 : forall s stc,
        stc||=
           is_array e len1 f s ** is_array e len2 f (s + len1) <=>
           is_array e (len1 + len2) f s.
      Proof.
        induction len1; simpl.
        - intros; rewrite emp_unit_l, <-plus_n_O; reflexivity.
        - intros. rewrite <-Nat.add_succ_comm, <-sep_assoc, IHlen1; reflexivity.
      Qed.

      sep_rewrite_in is_array_concat H.
      cutrewrite (offset + offset = offset * 2) in H; [|ring].
      cutrewrite (offset * nf i * 2 =  nf i * (offset * 2)) in H; [auto|ring].
    - (* rest of commands (else case) *)
      eapply Hbackward.
      (* in this case, thread does not have any heap resources *)
      Focus 2.
      { intros s h H; sep_split_in H.
        change_in H.
        { unfold_pures.
          destruct lt_dec .
          rewrite HP4, HP1, <-Nat2Z.inj_lt in n; apply n in l; destruct l.
          exact H.  }
        sep_combine_in H. exact H. } Unfocus.
      
      (* execute rest of commands *)
      eapply rule_seq; [hoare_forward; intros s h [v H]; subA_normalize_in H; ex_intro v H; exact H|].
      simpl; repeat hoare_forward. 
      intros s h [v H]; subA_normalize_in H. simpl in H.
      sep_split_in H. unfold upInv; unfold_pures.
      exists (2 * offset), (d /2), fc.
      destruct ntrd_is_p2 as [en Hen].
      destruct HP4 as [[? ?] | HP4]; [subst; simpl in *; try omega|].
      rewrite Hen in HP4; destruct (div_pow2 _ _ _ HP4) as (ed & eoff & Hed & Heoff).
      autorewrite with sep in *; try omega; sep_split;
      try now (unfold_conn; simpl; omega || congruence || eauto); eauto.
      + destruct ed; [left; simpl; auto|].
        * subst. split. cbv. auto. simpl in HP4. omega.
        * subst. right. autorewrite with sep; auto.
          rewrite <-HP4. rewrite Nat.pow_succ_r'. ring.
      + subst; rewrite dbl_inv.
        destruct lt_dec; rewrite HP6, <-Nat2Z.inj_lt in *; try tauto.
    - unfold upInv; intros s h H.
      ex_dest_in H offset; ex_dest_in H d; ex_dest_in H f.
      sep_split_in H.
      unfold_pures.
      assert (d = 0); [|subst].
      { apply Nat2Z.inj; rewrite <-HP2; simpl; omega. }
      unfold dbl in H; simpl in H.
      destruct lt_dec, Nat.eq_dec; try omega; sep_split_in H; unfold_pures.
      exists f; unfold_pures.
      + sep_split.
        unfold_conn; intros; rewrite HP4; try omega.
        rewrite Min.min_l; eauto.
      
        Lemma rdiv2_eq n : n <> 0 -> exists m, n = 2 ^ rdiv2 n * m /\ m mod 2 = 1.
        Proof.
          intros; functional induction (rdiv2 n); try omega.
          - clear e0; rewrite <-Nat.div_exact in _x0; try omega.
            assert (n / 2 <> 0) by (rewrite mult_comm in _x0; rewrite _x0, Nat.div_mul; try omega).
            apply IHn0 in H0 as (m & H1 & H2).
            exists m; rewrite Nat.pow_succ_r', <-mult_assoc, <-H1; split; auto.
          - exists n; split; [simpl; omega |].
                   assert(n mod 2 = 0 \/ n mod 2 = 1).
                   pose proof (Nat.mod_upper_bound n 2). omega.
                   destruct H0; omega. 
        Qed.
        destruct HP3 as [[_ HP3] | ]; try omega; subst.
      
        Lemma rdiv2_leq (i n e : nat) : 
          n = 2 ^ e -> i <= n -> 2 ^ rdiv2 i <= n.
        Proof.
          assert (i = 0 \/ i <> 0) as [H | H] by omega.
          - subst; simpl; intros; subst.
            pose proof (Nat.pow_nonzero 2 e); omega.
          - destruct (rdiv2_eq i H) as [m [Him1 Him2]]; intros; subst n; rewrite Him1 in H1.
            rewrite mult_comm in H1; destruct m; simpl in *; try omega.
            generalize (m * 2 ^ rdiv2 i) H1; intros.  omega.
        Qed.

        destruct ntrd_is_p2 as [en Hen]; rewrite Hen.
        rewrite mult_comm, <-Nat.pow_succ_r'.
        eapply rdiv2_leq; eauto. simpl. omega.
      
        rewrite e in H; simpl in H.
        destruct HP3 as [[_ HP3] | ]; try omega; subst.
        rewrite Nat.max_r in H; eauto.
        omega.

      + apply H.
    - intros s h H; sep_split_in H; unfold upInv.
      unfold_pures.
      exists 1, ntrd, f_ini; sep_split; auto.
      unfold_conn; simpl.
      omega.
      
      unfold dbl; destruct Nat.eq_dec; try omega.
      pose proof (fin_lt ntrd i).
      destruct lt_dec; try omega.
      sep_split; [unfold_conn|].
      intros i0.
      rewrite Nat.min_r, Nat.add_sub; simpl; try omega.
      pose proof (Nat.pow_nonzero 2 (rdiv2 (i0 + 1))); try omega.
      rewrite Nat.max_l; eauto.
  Qed.
  Import Bdiv.

  Lemma bspec0_preserved : 
    Aistar_v (fst (bspec 0)) |= Aistar_v (snd (bspec 0)).
  Proof.
    unfold bspec; simpl. intros s h H.
    apply sc_v2l in H.
    rewrite (vec_to_list_init0 _ emp) in H.
    erewrite ls_init_eq0 in H.
    Focus 2.
    { intros i Hi.
      destruct (Fin.of_nat i ntrd) as [|Hex] eqn:Heq; [|destruct Hex; omega].
      rewrite (Fin_nat_inv Heq). reflexivity. } Unfocus.
  
    apply sc_v2l.
    rewrite (vec_to_list_init0 _ emp).
    erewrite ls_init_eq0.
    Focus 2.
    { intros i iH.
      destruct (Fin.of_nat i ntrd) as [|Hex] eqn:Heq; [|destruct Hex; omega].
      rewrite (Fin_nat_inv Heq). reflexivity. } Unfocus.
    
    sep_rewrite_in (ls_exists0 0 (n := ntrd)) H; auto; destruct H as [offsets H]; sep_split_in H.
    sep_rewrite_in (ls_exists0 0 (n := ntrd)) H; auto; destruct H as [ds H]; sep_split_in H.
    sep_rewrite_in (ls_exists0 (fun _ : nat => 0%Z) (n := ntrd)) H; auto; destruct H as [fcs H]; sep_split_in H.
    repeat sep_rewrite_in (@ls_star ntrd) H.
    repeat sep_rewrite_in (@ls_pure ntrd) H; sep_split_in H.
    
    Lemma vars_eq0 s (E : exp) len (f : nat -> nat) :
      len <> 0 ->
      conj_xs (ls_init 0 len (fun i => (E === Zn (f i)))) s emp_ph -> 
      exists v, forall i, i < len -> f i = v.
    Proof.
      intros Hlen Hconj; exists (f 0); intros i Hil; destruct i; simpl; auto.
      pose proof (@ls_emp _ _ 0 Hconj) as H0; rewrite ls_init_spec in H0; destruct lt_dec; try omega.
      pose proof (@ls_emp _ _ (S i) Hconj) as HS; rewrite ls_init_spec in HS; destruct lt_dec; try omega.
      unfold_pures. rewrite HS in H0; apply Nat2Z.inj in H0; auto.
    Qed.
    destruct ntrd_is_p2 as [e Hen].
    assert (ntrd <> 0) by (pose proof (Nat.pow_nonzero 2 e); omega).
    
    pose proof (vars_eq0 s Offset ntrd _  H0 HP2) as [offset Hoff]; auto.
    pose proof (vars_eq0 s D ntrd _  H0 HP3) as [d Hd]; auto.
    
    pose proof (@ls_emp _ _ 0 HP4) as Hdof; rewrite ls_init_spec in Hdof; simpl in Hdof.
    destruct (lt_dec 0 ntrd); try omega.
    rewrite Hoff, Hd in Hdof; try omega.

    pose proof (@ls_emp _ _ 0 HP5) as Hd0; rewrite ls_init_spec in Hd0; simpl in Hd0.
    destruct (lt_dec 0 ntrd); try omega.
    rewrite Hd in Hd0; try omega.

    unfold_pures.
    destruct Hdof as [| Hdof]; try omega.
    
    erewrite ls_init_eq0 in H; [|intros; rewrite Hd, Hoff; auto; reflexivity].
    
    sep_rewrite (ls_exists0 0 (n:=ntrd)); auto; exists offsets; sep_split; auto.
    sep_rewrite (ls_exists0 0 (n:=ntrd)); auto; exists ds; sep_split; auto.
    set (fc' := fun i =>
                  (nth (i / Nat.max 2 offset) fcs (fun _:nat=>0%Z)) i).
    sep_rewrite (ls_exists0 (fun _:nat => 0%Z) (n:=ntrd)); auto; exists (nseq ntrd fc'); sep_split.
    rewrite length_nseq; unfold_conn; auto.

    repeat sep_rewrite (@ls_star ntrd). 
    repeat sep_rewrite (@ls_pure ntrd).
    repeat sep_split; auto.

    rewrite <-(firstn_skipn (d * 2) (ls_init _ _ _)) in H.
    rewrite firstn_init, skipn_init in H.
    apply conj_xs_app in H.
    lazymatch type of H with
    | ((_ ** conj_xs (ls_init ?b ?n ?P)) _ _) =>
      evar (fc : nat -> assn); 
        sep_rewrite_in (@ls_init_eq' _ P fc n b) H; unfold fc in *
    end.
    Focus 2.
    intros i Hi; destruct lt_dec; try omega.
    instantiate (1 := fun _ => emp); reflexivity.
    sep_rewrite_in init_emp_emp H; sep_normal_in H.
    
    erewrite ls_init_eq0 in H.
    Focus 2.
    { intros; destruct lt_dec; rewrite Nat.min_glb_lt_iff in H1; try omega; reflexivity. } Unfocus.
    sep_rewrite_in (@ls_star) H; sep_rewrite_in (@ls_pure) H; sep_split_in H.

    sep_rewrite (@ls_init_eq0).
    Focus 2.
    { intros i Hi; rewrite Hd, Hoff; auto; reflexivity. } Unfocus.
    rewrite <-(firstn_skipn (d) (ls_init _ _ _)).  
    rewrite firstn_init, skipn_init; apply conj_xs_app.
    lazymatch goal with
    | [|- ((_ ** conj_xs (ls_init ?b ?n ?P)) _ _)] =>
      evar (Q : nat -> assn); 
        sep_rewrite (@ls_init_eq' _ P Q n b); unfold Q in *
    end.
    Focus 2.
    { intros; destruct lt_dec; try omega.
      instantiate (1 := fun _ : nat => emp); reflexivity. } Unfocus.
    sep_rewrite init_emp_emp; sep_normal.
    assert (d <= ntrd).
    { destruct offset; simpl in Hdof; try omega.
      rewrite mult_comm in Hdof; simpl in Hdof.
      generalize (offset * d) Hdof; intros; try omega. } 
    rewrite Min.min_l; eauto.

    sep_rewrite @ls_init_eq0; [|intros; destruct lt_dec; try omega; reflexivity].
    assert (0 < offset).
    { destruct offset; rewrite mult_comm in Hdof; simpl in Hdof; try omega. }
    sep_rewrite (@ls_star); sep_rewrite (@ls_pure); sep_split.
    - apply ls_emp'; rewrite init_length; intros i Hid; rewrite ls_init_spec; destruct lt_dec; 
      [| unfold TrueP; eauto].
      unfold_conn; intros j Hjn; rewrite nth_nseq; destruct (lt_dec (i+0) ntrd); try omega.
      destruct (leb ntrd (0 + i)) eqn:Hni; [apply leb_iff in Hni; omega|].
      unfold fc'.
      
      apply (ls_emp _ _ (j / Nat.max 2 offset)) in HP6; rewrite ls_init_spec in HP6.
      assert (0 < Nat.max 2 offset).
      { unfold Nat.max; destruct (Nat.max_dec 2 offset) as [Heq | Heq]; rewrite Heq; try omega. }
      assert (d * 2 <= ntrd \/ ntrd < d * 2) as [Hd2n | Hd2n] by omega.
      + rewrite Nat.min_l in HP6; eauto.
        assert (j / (Nat.max 2 offset) < d * 2).
        { apply Nat.div_lt_upper_bound; try omega.
          rewrite Nat.max_comm.
          destruct (Nat.max_spec offset 2).
          destruct H4; unfold Nat.max; rewrite H5.
          assert (offset = 1) by omega.
          rewrite H6 in Hdof; try omega.
          destruct H4; unfold Nat.max; rewrite H5.
          rewrite mult_assoc, (mult_comm offset d); rewrite Hdof; eauto. }
        destruct lt_dec; try omega.
        unfold_pures; apply (HP6 j); eauto.
      + rewrite Nat.min_r in HP6; try omega.
        assert (offset < 2).
        rewrite <-Hdof in Hd2n; apply Nat.mul_lt_mono_pos_l in Hd2n; eauto.
        rewrite Nat.max_l in *; try omega.
        assert (j / 2 < ntrd) by (apply Nat.div_lt_upper_bound; omega).
        destruct lt_dec; try omega.
        apply HP6; eauto.
    - assert (offset < 2 \/ 2 <= offset) as [Ho2 | Ho2] by omega.
      + assert (offset = 1) as Ho1 by omega.
        assert (d = ntrd) as Hdn by (rewrite Ho1 in Hdof; omega).
        unfold fc'; subst d offset.
        rewrite Nat.max_l in *; try omega.
        rewrite Nat.min_r in H; try omega.

        Lemma is_array_conj (e : exp) (n m : nat) (f : nat -> nat -> Z) :
          m <> 0 ->
          forall s stc,
            stc ||= conj_xs (ls_init s n (fun i => is_array e m (f i) (i * m))) <=>
                    is_array e (m * n) (fun i => f (i / m) i) (m * s).
        Proof.
          induction n; simpl; intros Hm s stc.
          - rewrite mult_0_r; simpl; reflexivity.
          - rewrite <-mult_n_Sm, plus_comm.
            rewrite <-is_array_concat.
            rewrite IHn; eauto.
            rewrite <-mult_n_Sm.
            lazymatch goal with
              | [|- ?stc ||= ?X ** ?Y <=> ?Z ** ?W] =>
                assert (Heq : stc ||= X <=> Z); [|rewrite Heq; reflexivity]
            end.
          rewrite mult_comm; apply is_array_change; intros x Hxm.
          rewrite mult_comm, Nat.div_add; eauto; rewrite Nat.div_small; eauto.
        Qed.

        sep_rewrite_in is_array_conj H; eauto; rewrite mult_0_r in H.
        erewrite ls_init_eq0.
        Focus 2.
        { intros i Hid.
          rewrite !mult_1_l.
          cutrewrite (i * 1 * 2 = i * 2); [|omega].
          rewrite nth_nseq; destruct (leb ntrd i) eqn:Heq; [apply leb_iff in Heq; omega|].
          reflexivity. } Unfocus.
        sep_rewrite is_array_conj; try omega.
        rewrite mult_0_r.
        apply H.
      + assert (d * 2 <= ntrd) by (apply (mult_le_compat_l _ _ d) in Ho2; rewrite <-Hdof; eauto).
        rewrite Nat.min_l in *; eauto.
        rewrite Nat.max_r in *; eauto.
        sep_rewrite_in is_array_conj H; try omega.
        
        erewrite ls_init_eq0.
        Focus 2.
        { intros i Hid.
          rewrite <-mult_assoc.
          rewrite nth_nseq; destruct (leb ntrd i) eqn:Heq; [apply leb_iff in Heq; omega|].
          reflexivity. } Unfocus.
        sep_rewrite is_array_conj; try omega.
        rewrite mult_0_r in *.
        cutrewrite (offset * 2 * d = offset * (d * 2)); [|ring].
        sep_rewrite_in is_array_change H; [apply H|].
        intros x Hx.
        unfold fc'.
        
        rewrite Nat.max_r; try omega.
Qed.
      
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

