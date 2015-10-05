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

  Infix "+C" := (Eplus) (at level 50, left associativity).
  Infix "*C" := (Emult) (at level 40, left associativity).
  Infix "-C" := (Esub) (at level 50, left associativity).
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

  Lemma div_pow2 : forall e n m, n * m = 2 ^ e -> exists e1 e2, n = 2 ^ e1 /\ m = 2 ^ e2 /\ e1 + e2 = e.
  Proof.
    induction e; intros n m Hnm.
    - exists 0, 0; simpl in *.
      apply mult_is_one in Hnm; repeat split; tauto.
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
        (Ex f, 
           (if Nat.eq_dec (nf i) 0 then 
              !(pure (forall i, i < ntrd * 2 ->
                                f i = let m := 2 ^ rdiv2 (i + 1) in sum_of (i + 1 - m) m f_ini)) ** 
               is_array Sum (ntrd * 2) f 0
            else emp) ** !(Tid === Zn (nf i)) ** !(Offset === Zn (ntrd * 2))).
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
          - subst. apply div_pow2 in H2; destruct H2 as (? & ? & ? & ? & _); eexists; eauto. }
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
        destruct HP5 as [? | HP5]; try omega; apply div_pow2 in HP5 as (eoff & ed & Heoff & Hed & _);subst.
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
      + sep_split; eauto.
        destruct HP3 as [[_ HP3] | ?]; try omega.
        rewrite HP3 in HP1; apply HP1.
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

      + exists f; sep_split; eauto.
        destruct HP3 as [[_ HP3]|?]; try omega.
        rewrite HP3 in HP1; apply HP1.
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
      

Definition downInv (i : nat) :=
  Ex (offset d : nat) (f : nat -> Z),
    !(Tid === Zn i) **
    !(Offset === Zn offset) **
    !(D === Zn d) **
    !(pure (d * offset = ntrd * 2)) **
    (if lt_dec i (ceil2 (d / 2)) then
       let p := if Nat.eq_dec d 1 then 1 else 2 in
       !(pure (forall j : nat,
           i * (offset * p) <= j < (i + 1) * (offset * p) ->
           if Nat.eq_dec ((j + 1) mod offset) 0 then
             f j = sum_of 0 ((j + 1) - offset) f_ini
           else
             f j = (let m := 2 ^ rdiv2 (j + 1) in sum_of (j + 1 - m) m f_ini))) **
        (is_array Sum (offset * p) f (i * (offset * p)))
     else emp).

Definition downsweep (i : nat) :=
  D ::= 1%Z ;;
  WhileI (downInv i) (D <C Zn (ntrd * 2)) (
    Offset ::= Offset >>1 ;;
    Cbarrier 1 ;;
    Cif (Tid <C D) (
      Tmp1 ::= [leftC Sum] ;;
      Tmp2 ::= [rightC Sum] ;;
      [leftC Sum] ::= Tmp2 ;;
      [rightC Sum] ::= Tmp1 +C Tmp2
    ) (Cskip) ;;
    D ::= D *C 2%Z
  ).
  
Definition bspec1 n :=
   if Nat.eq_dec n 1 then
    (MyVector.init (fun i : Fin.t ntrd =>
       let i := nf i in
       Ex (offset d : nat) (f : nat -> Z),
         !(Offset === Zn offset) **
         !(D === Zn d) **
         !(pure (d * offset = ntrd)) **
         !(pure (d < ntrd * 2)) **
         (if lt_dec i (ceil2 (d / 2)) then
            let p := if Nat.eq_dec d 1 then 1 else 2 in
            !(pure (forall j : nat, 
                i * (offset * 2 * p) <= j < (i + 1) * (offset * 2 * p) ->
                if Nat.eq_dec ((j + 1) mod (offset * 2)) 0 then
                  f j = sum_of 0 (j + 1 - (offset * 2)) f_ini
                else
                  f j = (let m := 2 ^ rdiv2 (j + 1) in sum_of (j + 1 - m) m f_ini))) **
              (is_array Sum (offset * 2 * p) f (i * (offset * 2 * p)) )
           else emp)),
     MyVector.init (fun i : Fin.t ntrd =>
       let i := nf i in
       Ex (offset d : nat) (f : nat -> Z),
         !(Offset === Zn offset) **
         !(D === Zn d) **
         !(pure (d * offset = ntrd)) **
         !(pure (d < ntrd * 2)) **
         (if lt_dec i d then
             !(pure (forall j : nat, 
                i * (offset * 2) <= j < (i + 1) * (offset * 2) ->
                if Nat.eq_dec ((j + 1) mod (offset * 2)) 0 then
                  f j = sum_of 0 (j + 1 - (offset * 2)) f_ini
                else
                  f j = (let m := 2 ^ rdiv2 (j + 1) in sum_of (j + 1 - m) m f_ini))) **
              (is_array Sum (offset * 2) f  (i * (offset * 2)))
           else emp)))
  else default ntrd.

Lemma downsweep_correct (i : Fin.t ntrd) :
  CSL bspec1 i
      (Ex f : nat -> Z,
         (!(Offset === Zn (ntrd * 2)) **
          (if Nat.eq_dec (nf i) 0 then
              !(pure
                  (forall i0 : nat,
                     i0 < ntrd * 2 ->
                     if Nat.eq_dec i0 (ntrd * 2 - 1) then f i0 = 0%Z
                     else f i0 = (let m := 2 ^ rdiv2 (i0 + 1) in sum_of (i0 + 1 - m) m f_ini))) **
               is_array Sum (ntrd * 2) f 0
           else emp)) **
       !(Tid === Zn (nf i)))
      (downsweep (nf i))
      (Ex f : nat -> Z,
         !(pure
             (forall j : nat, (nf i * 2) <= j < (nf i + 1) * 2 -> f j = sum_of 0 j f_ini)) **
          (is_array Sum 2 f ((nf i) * 2) )).
Proof.
  pose proof ntrd_neq_0 as ntrd_neq_0.
  destruct ntrd_is_p2 as [en Hntrd2].
  unfold downsweep.
  eapply rule_seq.
  { repeat hoare_forward. intros ? ? [v H]. subA_normalize_in H. simpl in H. ex_intro x H. exact H. }
  simpl; repeat hoare_forward.

  (* loop inv ** ~b => postcondition *)
  Focus 2.
  { unfold downInv; intros s h H.
    ex_dest_in H offset; ex_dest_in H d; ex_dest_in H f.
    sep_normal_in H; sep_split_in H.
    unfold_pures.
    assert (d = ntrd * 2).
    { destruct offset; rewrite mult_comm in HP2; simpl in *; try omega.
      rewrite HP1, <-Nat2Z.inj_lt in n.
      generalize (offset * d) HP2; intros; omega. }
    assert (offset = 1).
    { rewrite H0 in HP2; rewrite <-(mult_1_r (ntrd * 2)) in HP2 at 2.
      rewrite Nat.mul_cancel_l in HP2; omega. }
    rewrite H0, Nat.div_mul in H; unfold ceil2 in H; destruct Nat.eq_dec; try omega.
    destruct lt_dec; [|destruct Fin.to_nat; simpl in *; omega].
    exists f; sep_split_in H; sep_split; eauto.
    unfold_pures; unfold_conn; intros j Hj.
    subst offset; simpl in HP4; rewrite HP4; try omega; [f_equal; omega|].
    destruct Nat.eq_dec; omega.
    subst offset; destruct Nat.eq_dec; try omega; simpl in H. eauto. } Unfocus.

  (* precondition => loop inv *)
  Focus 2.
  { unfold downInv; intros s h H.
    sep_split_in H; exists (ntrd * 2), 1, x; unfold ceil2; simpl.
    sep_split; eauto.
    - unfold_conn; omega.
    - destruct Nat.eq_dec, lt_dec; try omega; eauto; sep_split_in H; sep_split.
      unfold_pures; unfold_conn; intros j Hj.
      rewrite e in Hj; autorewrite with sep in Hj.
      assert (j < ntrd * 2) by omega.
      specialize (HP2 j H0); destruct Nat.eq_dec; subst.
      cutrewrite (2 ^ en * 2 - 1 + 1 = 2 ^ en * 2); [|omega]; rewrite Nat.mod_same, minus_diag; simpl; omega.
      rewrite Nat.mod_small; try omega; destruct Nat.eq_dec; try omega.
      rewrite e, mult_1_r; eauto. } Unfocus.

  Hint Unfold downInv.
  autounfold.
  eapply Hbackward.
  Focus 2.
  { intros ? ? H; ex_dest_in H offset; ex_dest_in H d; ex_dest_in H f; sep_normal_in H.
    ex_intro f H; ex_intro d H; ex_intro offset H; simpl in H; exact H. } Unfocus.
  repeat hoare_forward. revert x0 x1 x2; intros offset d f.
  eapply rule_seq; [hoare_forward; intros s h [v H]; subA_normalize_in H; ex_intro v H; exact H|].
  simpl.

  (* loop invariant is preserved *)
  repeat hoare_forward.
  eapply rule_seq; [hoare_forward|].
  
  { intros s h H;
    apply ex_lift_l; exists (offset / 2); apply ex_lift_l; exists d; apply ex_lift_l; exists f.
    sep_split_in H.
    assert (pure (d * (offset / 2) = ntrd) s emp_ph).
    { unfold_pures; unfold_conn.
      rewrite <-Nat.divide_div_mul_exact; eauto.
      rewrite HP3, Nat.div_mul; eauto.
      unfold Nat.divide, divide; rewrite Hntrd2 in HP3, l.
      Lemma pow_S (n e : nat) : n ^ e * n = n ^ (S e).
      Proof.
        rewrite mult_comm; simpl; reflexivity.
      Qed.
      Hint Rewrite pow_S : sep.
      rewrite HP2, <-Nat2Z.inj_lt in l.
      autorewrite with sep in *.
      apply div_pow2 in HP3 as (ed & eoff & Hed & Heof & Hdof); destruct eoff.
      cutrewrite (d = 2 ^ S en) in l; [|rewrite <-Hdof, Hed, <-Nat.pow_lt_mono_r_iff in l]; omega.
      subst offset; simpl; exists (2 ^ eoff); omega. }
    sep_normal; sep_split; eauto.
    - unfold_pures; unfold_conn; rewrite Zdiv2_div in HP; subst; simpl.
      rewrite div_Zdiv; eauto.
    - unfold_pures; unfold_conn.
      rewrite HP2, <-Nat2Z.inj_lt in l; omega.
    - assert (Hoff : offset / 2 * 2 = offset); [|rewrite Hoff].
      { unfold_pures.
        rewrite mult_comm; rewrite <-Nat.divide_div_mul_exact; eauto.
        rewrite mult_comm, Nat.div_mul; eauto.
        rewrite Hntrd2 in HP3; autorewrite with sep in HP3; apply div_pow2 in HP3 as (e1 & e2 & ? & ? & ?).
        destruct e2; subst offset; [unfold div in H0; simpl in H0; try omega|].
        unfold Nat.divide, divide; exists (2 ^ e2); simpl; omega. }
      unfold lt in *.
      clear HP HP1 HP2 HP3 HP3 H0 Hoff; sep_combine_in H; apply H. } 
      
  simpl; rewrite MyVector.init_spec; intros s h H.
  clear d f x x0.
  ex_dest_in H o; ex_dest_in H d'; ex_dest_in H f'; sep_normal_in H.
  ex_intro f' H; ex_intro d' H; ex_intro o H; simpl in H. exact H.

  repeat hoare_forward.
  clear offset d f x0.
  rename x1 into off; rename x2 into d; rename x3 into f.

  eapply rule_seq; [apply rule_if_disj|].
  eapply Hbackward.
  Focus 2.
  { intros s h H; sep_normal_in H; sep_split_in H.
    change_in H.
    { unfold_pures.
      rewrite HP0, HP3, <-Nat2Z.inj_lt in l; destruct lt_dec; [|unfold lt in *; omega].
      exact H. }
    sep_split_in H.
    change_in H.
    { unfold_pures.
      cutrewrite (off * 2 = off + off) in H; [|omega].
      sep_rewrite_in_r is_array_concat H.
      rewrite <-HP1 in ntrd_neq_0; apply Nat.neq_mul_0 in ntrd_neq_0 as [Hd0 Hof0].
      sep_rewrite_in is_array_unfold' H; try omega.
      sep_normal_in H; sep_lift_in H 2.
      sep_rewrite_in is_array_unfold' H; try omega.
      assert (Heq : (Sum +C Zn (nf i * (off + off) + off + off - 1) ===
                     Sum +C Offset *C (2%Z *C Tid +C 2%Z) -C 1%Z) s emp_ph).
      { unfold_conn; simpl; autorewrite with sep; try ring.
        simpl; rewrite HP, HP3, Z.add_sub_assoc. unfold lt; ring.
        generalize (nf i * (off + off)); intros; omega. }
      sep_rewrite_in mps_eq1 H; [|exact Heq]. clear Heq.
      assert (Heq : (Sum +C Zn (nf i * (off + off) + off - 1) ===
                     Sum +C Offset *C (2%Z *C Tid +C 1%Z) -C 1%Z) s emp_ph).
      { unfold_conn; simpl; autorewrite with sep; try ring.
        simpl; rewrite HP, HP3. unfold lt; ring.
        generalize (nf i * (off + off)); intros; omega. }
      sep_lift_in H 3.
      sep_rewrite_in mps_eq1 H; [|exact Heq]. clear Heq.
      exact H. }
    sep_combine_in H. exact H. } Unfocus.

  eapply rule_seq; [hoare_forward; intros ? ? H; exact H|].
  eapply rule_seq; [hoare_forward; intros ? ? H; exact H|].
  eapply rule_seq; [hoare_forward; intros ? ? H; exact H|].
  hoare_forward.

  intros s h H; exact H.

  eapply Hbackward.
  Focus 2.
  { intros s h H; sep_split_in H.
    change_in H.
    { unfold_pures.
      rewrite HP1, HP4, <-Nat2Z.inj_lt in n; destruct lt_dec; try (unfold lt in *; omega). 
      exact H. }
    sep_combine_in H; sep_normal_in H; exact H. } Unfocus.

  apply rule_skip.

  eapply Hforward.
  apply rule_disj; hoare_forward; intros s h [d' H]; subA_normalize_in H.
  
  - instantiate (1 := downInv (nf i)); unfold downInv; simpl in H.
    sep_split_in H; unfold_pures.
    set (fc' := fun j =>
      if Nat.eq_dec j (off * (2 * nf i + 2) - 1) then
        (f (nf i * (off * 2) + (off * 2) - 1)%nat + f (nf i * (off * 2) + off - 1)%nat)%Z
      else if Nat.eq_dec j (off * (2 * nf i + 1) - 1) then
        f (nf i * (off * 2) + off * 2 - 1)
      else f j).
    (* set (fc' := fun j => *)
    (*          if Nat.eq_dec (j + 1 mod off) 0 then *)
    (*            sum_of 0 (j + 1 - off) f_ini *)
    (*          else *)
    (*            sum_of (j + 1 - 2 ^ rdiv2 (j + 1)) (2 ^ rdiv2 (j + 1)) f_ini). *)
    cutrewrite (off + off = off * 2) in HP0; [|ring].
    rewrite <-plus_assoc in HP0; cutrewrite (off + off = off * 2) in HP0; [|ring].
    cutrewrite (off + off = off * 2) in HP1; [|ring].
    exists off, (d * 2); exists fc';
    sep_split; eauto.
    + unfold_conn; simpl; autorewrite with sep; simpl; omega.
    + unfold_conn; simpl; rewrite <-HP4; ring.
    + rewrite Hntrd2 in HP4; pose proof (div_pow2 _ _ _ HP4) as (e1 & e2 & Hd2 & Hoff2 & He1e2).
      rewrite Hd2; autorewrite with sep; eauto.
      rewrite HP6, HP3, <-Nat2Z.inj_lt in l; destruct lt_dec; [|unfold lt in *; omega].
      assert (Hoff0 : off <> 0) by (rewrite Hoff2; eauto).
      sep_split.
      { intros j Hj; unfold fc'.
        destruct (Nat.eq_dec (2 ^ S e1) 1).
        { simpl in e. pose proof (Nat.pow_nonzero 2 e1). omega. }
        clear n.
        destruct (Nat.eq_dec ((j + 1) mod off) 0).
        - pose proof (HP9 (nf i * (off * 2) + off * 2 - 1)).
          assert (Ht : nf i * (off * 2) <= nf i * (off * 2) + off * 2 - 1 < 
                       (nf i + 1) * (off * 2)).
          { split.
            - generalize (nf i * (off * 2)); intros; omega.
            - cutrewrite (nf i * (off * 2) + off * 2 - 1 =
                          (nf i + 1) * (off * 2) - 1); [|f_equal; ring].
              apply lt_minus; try omega.
              (* cutrewrite (1 = 1 * 1); [|eauto]; apply Nat.mul_le_mono; omega. *) }
          
          specialize (H0 Ht); clear Ht.
          
          cutrewrite (nf i * (off * 2) + off * 2 - 1 + 1 =
                      nf i * (off * 2) + off * 2) in H0; [|generalize (nf i * (off * 2)); intros; omega].
          assert (Heq : nf i * (off * 2) + (off * 2) = (nf i + 1) * (off * 2)) by ring.
          rewrite Heq in H0.
          rewrite Nat.mod_mul in H0; simpl in H0; eauto; rewrite <-Heq in H0; try omega; rewrite H0.
          clear Heq.
        
          pose proof (HP9 (nf i * (off * 2) + off - 1)).
          assert (Ht : nf i * (off * 2) <= nf i * (off * 2) + off  - 1 < (nf i + 1) * (off * 2)).
          { cutrewrite ((nf i + 1) * (off * 2) = nf i * (off * 2) + off * 2); [|ring].
            split; generalize (nf i * (off * 2)); intros; omega. }
          specialize (H1 Ht).
          cutrewrite (nf i * (off * 2) + off - 1 + 1 = off + nf i * (off * 2)) in H1; [|generalize (nf i * (off * 2)); intros; omega].
          assert (Heq : nf i * (off * 2) + off = off + nf i * (off * 2)) by ring. 
          rewrite Heq in H1.
          rewrite Nat.mod_add in H1; try omega; rewrite Nat.mod_small in H1; try omega.
          destruct Nat.eq_dec; try omega.
          rewrite <-Heq in H1; rewrite H1.
        
          rewrite Nat.add_sub.
        
          Lemma rdiv2_inv (e n : nat) : 2 ^ rdiv2 (2 ^ e * (2 * n + 1)) = 2 ^ e.
          Proof.
            induction e; rewrite rdiv2_equation.
            - rewrite pow_0_r, mult_1_l; remember (2 * n + 1); destruct n0; eauto.
              rewrite Heqn0, mult_comm, plus_comm, Nat.mod_add; eauto.
            - remember (2 ^ S e * (2 * n + 1)).
              assert (n0 <> 0).
              rewrite Heqn0; intros H; ring_simplify in H.
              assert (2 ^ (1 + e) <> 0) by (apply Nat.pow_nonzero; eauto).
              generalize (2 * 2 ^ (1 + e) * n) H0 H; intros; omega.
              destruct n0; try omega.
              rewrite Heqn0, Nat.pow_succ_r'.
              rewrite <-mult_assoc, mult_comm, Nat.mod_mul; eauto; simpl.
              cutrewrite (n + (n + 0) + 1 = 2 * n + 1); [|omega]; rewrite Nat.div_mul; eauto.
          Qed.
        
          cutrewrite (nf i * (off * 2) + off = off * (2 * nf i + 1)); [|ring].
          rewrite Hoff2, rdiv2_inv.
          clear Heq.
          assert (Heq: 2 ^ e2 * (2 * nf i + 1) - 2 ^ e2 = nf i * (2 ^ e2 * 2) + 0); [|rewrite Heq; clear Heq].
          { rewrite mult_plus_distr_l, mult_1_r, Nat.add_sub. ring. }
          destruct Nat.eq_dec.
          + rewrite <-sum_of_concat; f_equal.
            rewrite e0. rewrite <-Hoff2.
            rewrite <-Nat.add_sub_swap; try omega.
            rewrite Nat.add_sub. 
            rewrite mult_plus_distr_l, <-Nat.add_sub_assoc; f_equal;  [ring | omega..].
            rewrite mult_plus_distr_l; generalize (off * (2 * nf i)); intros; omega.
          
          + destruct Nat.eq_dec; try omega.
            * specialize (HP9 (nf i * (off * 2) + off * 2 - 1)).
              rewrite e0; f_equal.
              rewrite Nat.sub_add.
              rewrite Nat.mul_add_distr_l, mult_1_r, Nat.add_sub; ring.
              cutrewrite (1 = 1 * 1); [|auto]; apply Nat.mul_le_mono; simpl.
              pose proof (Nat.pow_nonzero 2 e2); omega.
              omega.
            * Lemma mod_range (n m k : nat) :
                m <> 0 -> m * k <= n < m * (k + 1) -> n / m = k.
              Proof.
                intros Hm Hn; rewrite (div_mod n m) in Hn; eauto; destruct Hn as [Hn1 Hn2].
                assert (n / m < k \/ n / m = k \/ k < n / m) as [Hknm | [Hknm | Hknm]] by omega.
                - assert (m * S (n / m)  <= m * k) by (apply mult_le_compat_l; try omega).
                  rewrite mult_succ_r in H.
                  pose proof (Nat.mod_upper_bound n m Hm); omega.
                - eauto.
                - assert (m * (k + 1) <= m * (n / m)) by (apply mult_le_compat_l; try omega).
                  omega.
              Qed.
              assert (nf i * (off * 2)  < j + 1 <= (nf i + 1) * (off * 2)) by omega.
              rewrite <-Nat.div_exact in e; try eauto; rewrite e in H2; destruct H2 as [Hj1 Hj2].
              cutrewrite (nf i * (off * 2) = off * (2 * nf i)) in Hj1; [|ring].
              apply <-Nat.mul_lt_mono_pos_l in Hj1; try omega.
              cutrewrite ((nf i + 1) * (off * 2) = off * (2 * nf i + 2)) in Hj2; [|ring].
              apply <-Nat.mul_le_mono_pos_l in Hj2; try omega.

              Lemma add_l_sub_r n m k : n + m = k -> n = k - m.
              Proof.
                omega.
              Qed.
              
              assert ((j + 1) / off = 2 * nf i + 1 \/ (j + 1) / off = 2 * nf i + 2)
                as [Hjoff | Hjoff] by omega;
              rewrite Hjoff in e; apply add_l_sub_r in e; rewrite e in n0; rewrite e in n1;
              elimtype False; [apply n1 | apply n0]; f_equal; subst off; ring.

        - destruct Nat.eq_dec.
          rewrite e, Nat.sub_add in n.
          rewrite mult_comm, Nat.mod_mul in n; congruence.
          cutrewrite (1 = 1 * 1); [|eauto]; apply Nat.mul_le_mono; omega.
          
          destruct Nat.eq_dec.
          rewrite e, Nat.sub_add in n.
          rewrite mult_comm, Nat.mod_mul in n; congruence.
          cutrewrite (1 = 1 * 1); [|eauto]; apply Nat.mul_le_mono; omega.
          
          pose proof (HP9 _ Hj).
          destruct Nat.eq_dec.
          
          rewrite <-Nat.div_exact in e; try omega.
          assert (nf i * (off * 2) < j + 1 <= (nf i + 1) * (off * 2)) by omega.
          rewrite e in H1; destruct H1 as [Hj1 Hj2].
          rewrite (mult_comm (off * 2)), <-Nat.mul_lt_mono_pos_r in Hj1; try omega.
          rewrite (mult_comm (off * 2)), <-Nat.mul_le_mono_pos_r in Hj2; try omega.
          assert ((j + 1) / (off * 2) = nf i + 1) by omega.
          rewrite H1 in e; apply add_l_sub_r in e; rewrite e in n0; elimtype False; 
          apply n0; f_equal. ring.

          apply H0. }

      { destruct (Nat.eq_dec (2 ^ S e1) 1).
        { simpl in e. pose proof (Nat.pow_nonzero 2 e1). omega. }
        
        cutrewrite (off * 2 = off + off); [|omega].
        Ltac sep_rewrite_r lem :=
          lazymatch goal with
            | |- ?X _ _ => pattern X
          end; erewrite <-lem; cbv beta.

        sep_rewrite_r is_array_concat.
        (* rewrite <-HP2 in ntrd_neq_0; apply Nat.neq_mul_0 in ntrd_neq_0 as [Hd0 Hof0]. *)
        sep_rewrite is_array_unfold'; try omega.
        sep_normal; sep_lift 2.
        sep_rewrite is_array_unfold'; try omega.
        sep_normal.
        assert (Heq : (Sum +C Zn (nf i * (off + off) + off + off - 1) ===
                       Sum +C Offset *C (2%Z *C Tid +C 2%Z) -C 1%Z) s emp_ph).
        { unfold_conn; simpl; autorewrite with sep; try ring.
          simpl; rewrite HP2, HP6. unfold lt; ring.
          generalize (nf i * (off + off)); intros; omega. }
        sep_rewrite mps_eq1; [|exact Heq]. clear Heq.
        assert (Heq : (Sum +C Zn (nf i * (off + off) + off - 1) ===
                       Sum +C Offset *C (2%Z *C Tid +C 1%Z) -C 1%Z) s emp_ph).
        { unfold_conn; simpl; autorewrite with sep; try ring.
          simpl; rewrite HP2, HP6. unfold lt; ring.
          generalize (nf i * (off + off)); intros; omega. }
        sep_lift 3.
        sep_rewrite mps_eq1; [|exact Heq]. clear Heq.
        
        unfold fc'.
        destruct Nat.eq_dec.
        ring_simplify in e.
        
        Lemma minus_inj (n m k : nat) : n - k = m - k -> k <= n -> k <= m -> n = m.
        Proof.
          intros Hnmk Hkn Hkm.
          omega.
        Qed.

        apply minus_inj in e; try omega.
        cutrewrite (nf i * (off + off) + off = off * (2 * nf i + 1)) in e; [|ring].
        rewrite Nat.mul_cancel_l in e; try omega.
        generalize (nf i * (off + off)); intros; try omega.
        cutrewrite (1 = 1 * 1); [|eauto]; apply Nat.mul_le_mono; simpl; omega.

        cutrewrite (nf i * (off + off) + off - 1 = off * (2 * nf i + 1) - 1);
          [| f_equal; ring].
        destruct Nat.eq_dec; try omega.

        sep_rewrite_r (@is_array_change Sum f).
        
        Focus 2.
        { intros x0 Hx0.
          cutrewrite (off * (2 * nf i + 2) - 1 = nf i * (off + off) + off + off - 1); [|f_equal; ring].
          rewrite <-Nat.add_sub_assoc; try omega.
          rewrite (plus_comm x0 (nf i * (off + off) + off)).
          destruct Nat.eq_dec; try omega.
          destruct Nat.eq_dec; eauto.
          cutrewrite (nf i * (off + off) + off = off * (2 * nf i + 1)) in e0; [|ring].
          assert (1 <= off * (2 * nf i + 1)).
          { cutrewrite (1 = 1 * 1); [|eauto]; apply Nat.mul_le_mono; simpl; omega. }
          generalize (off * (2 * nf i + 1)) e0 H0; intros; omega. } Unfocus.

        sep_cancel.
        sep_cancel.

        cutrewrite (nf i * (off + off) + off + off - 1 = off * (2 * nf i + 2) - 1); [|f_equal; ring].
        destruct Nat.eq_dec; try omega.
        sep_cancel.

        sep_rewrite_r (@is_array_change Sum f).
        exact H0.

        intros x0 Hx0.
        cutrewrite (off * (2 * nf i + 2) - 1 = nf i * (off + off) + off + off - 1); [|f_equal; ring].
        rewrite <-Nat.add_sub_assoc; try omega.
        rewrite (plus_comm x0 (nf i * (off + off))).
        destruct Nat.eq_dec; try omega.
        destruct Nat.eq_dec; eauto.
        cutrewrite (nf i * (off + off) = off * (2 * nf i)) in e3; [|ring].
        rewrite Nat.mul_add_distr_l in e3.
        omega. }
      
  - instantiate (1 := (downInv (nf i))).
    sep_split_in H.
    sep_rewrite_in_r emp_unit_r H.
    sep_split_in H.
    simpl in *. unfold_pures.
    unfold downInv.
    exists off, (d * 2), f.
    sep_split; try now (eauto; unfold_conn; simpl; eauto).
    
    + unfold_conn; simpl; autorewrite with sep; eauto.
      rewrite <-HP2; apply HP.

    + unfold_conn; rewrite <-HP3; ring.

    + rewrite Hntrd2 in HP3; apply div_pow2 in HP3 as (e1 & e2 & Hd & Hof & Hdof); rewrite Hd.
      rewrite pow_S, pow_divS; try omega.
      rewrite HP2, HP5, Hd, <-Nat2Z.inj_lt in n; try omega.
      rewrite ceil2_pow; destruct lt_dec; try (unfold lt in *; omega); eauto.

  - unfold downInv; intros s h [H | H]; apply H.

Time Qed.

Lemma bspec1_preserved : 
  Aistar_v (fst (bspec1 1)) |= Aistar_v (snd (bspec1 1)).
Proof.
  unfold bspec1; simpl; intros s h H.
  
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
    
  destruct ntrd_is_p2 as [e Hen].
  assert (ntrd <> 0) by (pose proof (Nat.pow_nonzero 2 e); omega).
    
  pose proof (vars_eq0 s Offset ntrd _  H0 HP2) as [offset Hoff]; auto.
  pose proof (vars_eq0 s D ntrd _  H0 HP3) as [d Hd]; auto.
    
  pose proof (@ls_emp _ _ 0 HP4) as Hdof; rewrite ls_init_spec in Hdof; simpl in Hdof.
  destruct (lt_dec 0 ntrd); try omega.
  rewrite Hoff, Hd in Hdof; try omega.
  
  pose proof (@ls_emp _ _ 0 HP5) as Hdn2; rewrite ls_init_spec in Hdn2; simpl in Hdn2.
  destruct (lt_dec 0 ntrd); try omega.
  rewrite Hd in Hdn2; try omega.

  unfold_pures.
    
  erewrite ls_init_eq0 in H; [|intros; rewrite Hd, Hoff; auto; reflexivity].
  
  sep_rewrite (ls_exists0 0 (n:=ntrd)); auto; exists offsets; sep_split; auto.
  sep_rewrite (ls_exists0 0 (n:=ntrd)); auto; exists ds; sep_split; auto.
  set (fc' := fun i =>
                (nth (i / (offset * 2 * if Nat.eq_dec d 1 then 1 else 2)) fcs (fun _:nat=>0%Z)) i).
  sep_rewrite (ls_exists0 (fun _:nat => 0%Z) (n:=ntrd)); auto; exists (nseq ntrd fc'); sep_split.
  rewrite length_nseq; unfold_conn; auto.

  repeat sep_rewrite (@ls_star ntrd). 
  repeat sep_rewrite (@ls_pure ntrd).
  repeat sep_split; auto.

  erewrite ls_init_eq0; [|intros; rewrite Hoff, Hd, nth_nseq; destruct (leb ntrd i) eqn:Hleb; 
                          try apply leb_iff in Hleb; try omega; reflexivity].
  
  (* destruct (Nat.eq_dec d 1); [rewrite e0 in *|]. *)
  
  (* erewrite ls_init_eq0 in H. *)
  (* Focus 2. *)
  (* { intros i Hi; unfold ceil2, div; simpl; rewrite !mult_1_r. reflexivity. } Unfocus. *)
  
  rewrite <-(firstn_skipn (ceil2 (d / 2)) (ls_init _ _ _)) in H.
  rewrite firstn_init, skipn_init in H.
  apply conj_xs_app in H.
  lazymatch type of H with
  | ((_ ** conj_xs (ls_init ?b ?n ?P)) _ _) =>
    evar (fc : nat -> assn); 
      sep_rewrite_in (@ls_init_eq' _ P fc n b) H; unfold fc in *
  end.
  Focus 2.
  { intros i Hi; destruct lt_dec; try omega.
    instantiate (1 := fun _ => emp); reflexivity. } Unfocus.
  sep_rewrite_in init_emp_emp H; sep_normal_in H.

  destruct ntrd_is_p2 as [en Hntrd2].
  pose proof ntrd_neq_0.
  assert (ceil2 (d / 2) <= ntrd).
  { rewrite Hntrd2 in Hdof; pose proof (div_pow2 _ _ _ Hdof) as (ed & eo & Hed & Heo & Hedo).
    rewrite Hed; destruct ed; autorewrite with sep; try omega.
    - unfold div, ceil2; simpl; omega.
    - rewrite Hntrd2; apply Nat.pow_le_mono_r; omega. }
  
  rewrite Nat.min_l in H; try omega.

  erewrite ls_init_eq0 in H.
  Focus 2.
  { intros i Hi; destruct lt_dec; try omega; reflexivity. } Unfocus.
    
  rewrite <-(firstn_skipn d (ls_init _ _ _)).  
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
  clear Q.

  assert (d <= ntrd).
  { rewrite Hntrd2 in Hdof; apply div_pow2 in Hdof as (ed & eo & Hed & Heo & Hedo).
    rewrite Hed, Hntrd2; apply Nat.pow_le_mono_r; omega. }
  
  rewrite Nat.min_l; try omega.
  erewrite ls_init_eq0.
  Focus 2.
  { intros i Hi; destruct lt_dec; try omega; reflexivity. } Unfocus.

  sep_rewrite (@ls_star d).
  sep_rewrite_in (@ls_star (ceil2 (d / 2))) H.
  sep_rewrite (@ls_pure d).
  sep_rewrite_in (@ls_pure (ceil2 (d / 2))) H.
  sep_split_in H.

  rewrite Hntrd2 in Hdof; apply div_pow2 in Hdof as (ed & eo & Hed & Heo & Hedo).
  destruct ed; rewrite Hed in HP6, H.
  - unfold div in HP6, H; simpl in HP6, H.
    unfold fc'; rewrite Hed; simpl; sep_split; sep_normal_in HP6.
    + sep_normal; intros j Hj.
      unfold_pures.
      rewrite plus_0_r, mult_1_r in *; specialize (HP6 _ Hj).
      assert (j / (offset * 2) = 0) by (rewrite Nat.div_small; omega).
      rewrite H4; apply HP6.
    + sep_normal; sep_normal_in H.
      rewrite mult_1_r in H; sep_rewrite_r (is_array_change Sum (nth 0 fcs (fun _ : nat => 0%Z))); eauto.
      intros x Hx; rewrite plus_0_r, Nat.div_small; try omega.
  - unfold fc'. autorewrite with sep in *; try omega; sep_split.
    + apply ls_emp'; rewrite init_length; intros i Hi.
      rewrite ls_init_spec; destruct lt_dec; try omega.
      simpl; intros j Hj.
      assert (d <> 1) by (rewrite Hed; simpl; pose proof (Nat.pow_nonzero 2 ed); try omega).
      destruct Nat.eq_dec; try omega.
      apply (ls_emp _ _ (j / (offset * 2 * 2))) in HP6; rewrite ls_init_spec in HP6.
      destruct Hj as [Hj1 Hj2].
      assert (offset <> 0) by (rewrite Heo; apply Nat.pow_nonzero; eauto).
      assert (j / (offset * 2 * 2) < 2 ^ ed).
      { assert (offset <> 0) by (rewrite Heo; apply Nat.pow_nonzero; eauto).
        apply Nat.div_lt_upper_bound; try omega.
        assert ((i + 1) * (offset * 2) <= offset * 2 * 2 * 2 ^ ed).
        cutrewrite (offset * 2 * 2 * 2 ^ ed = 2 * 2 ^ ed * (offset * 2)); [|ring].
        apply Nat.mul_le_mono_pos_r; try omega.
        cutrewrite (2 * 2 ^ ed = 2 ^ S ed); [|simpl; ring].
        rewrite <-Hed; omega.
        omega. }
      rewrite <-Hed in HP6; destruct (Nat.eq_dec d 1); try omega.
      destruct lt_dec; try omega; simpl in HP6.
      unfold_pures; specialize (HP6 j).
      apply HP6; split; [apply div_mult; try omega|].
      rewrite (Nat.div_mod j (offset * 2 * 2)) at 1; try omega; rewrite Nat.mul_add_distr_r, mult_1_l.
      rewrite mult_comm; pose proof (Nat.mod_upper_bound j (offset * 2 * 2)); try omega.
    + assert (d <> 1) by (rewrite Hed; simpl; pose proof (Nat.pow_nonzero 2 ed); omega).
      rewrite <-Hed in H; destruct Nat.eq_dec; try omega.
      assert (offset <> 0) by (rewrite Heo; apply Nat.pow_nonzero; eauto). 
      apply is_array_conj in H; try omega.
      apply is_array_conj; try omega.
      rewrite mult_0_r in *; rewrite Hed; rewrite Nat.pow_succ_r';
      cutrewrite (offset * 2 * (2 * 2 ^ ed) = offset * 2 * 2 * 2 ^ ed); [|ring].
      apply H.
Qed.

Infix "==C" := Beq (at level 70).

Definition prescan :=
  ( Offset ::= 1%Z;;
    D ::= Zn ntrd;;
    Cwhile (0%Z <C D) (
      BARRIER  (0);;
      Cif (Tid <C D) (
        Tmp1 ::=  [Sum +C Offset *C (2%Z *C Tid +C 1%Z) -C 1%Z];;
        Tmp2 ::=  [Sum +C Offset *C (2%Z *C Tid +C 2%Z) -C 1%Z];;
        [Sum +C Offset *C (2%Z *C Tid +C 2%Z) -C 1%Z]::=Tmp1 +C Tmp2)
        (SKIP) ;;
      Offset ::= Offset *C 2%Z;;
      D ::= D >>1)) ;;
  Cif (Tid ==C 0%Z) ([ Sum +C (Zn (ntrd * 2 - 1)) ] ::= 0%Z ) (SKIP) ;;
  ( D ::= 1%Z;;
    Cwhile (D <C Zn (ntrd * 2)) (
      Offset ::= Offset >>1;;
      BARRIER  (1);;
      Cif (Tid <C D) (
        Tmp1 ::=  [Sum +C Offset *C (2%Z *C Tid +C 1%Z) -C 1%Z];;
        Tmp2 ::=  [Sum +C Offset *C (2%Z *C Tid +C 2%Z) -C 1%Z];;
        [Sum +C Offset *C (2%Z *C Tid +C 1%Z) -C 1%Z]::=Tmp2;;
        [Sum +C Offset *C (2%Z *C Tid +C 2%Z) -C 1%Z]::=Tmp1 +C Tmp2)
        (SKIP) ;;
      D ::= D *C 2%Z)).

Lemma barriers_step0 C1 C2 st1 st2 :
  C1 / st1 ==>s C2 / st2 ->
  forall b, List.In b (barriers C2) -> List.In b (barriers C1).
Proof.
  induction 1; simpl; intros; eauto.
  - apply in_app_iff in H0; apply in_app_iff.
    destruct H0; eauto.
  - apply in_app_iff; eauto.
  - apply in_app_iff; eauto.
  - rewrite app_nil_r, in_app_iff in H; eauto.
    destruct H; eauto.
Qed.

Lemma barriers_step C1 C2 st1 st2 :
  C1 / st1 ==>p C2 / st2 ->
  forall b, List.In b (barriers C2) -> List.In b (barriers C1).
Proof.
  destruct 1.
  intros; eapply barriers_step0 in H7; eauto.
Qed.

Lemma wait_barriers1 C : forall b C',
  wait C = Some (b,  C') -> List.In b (barriers C).
Proof.
  induction C; try now inversion 1.
  - simpl; intros; rewrite List.in_app_iff.
    destruct (wait C1) as [[? ?] |]; inversion H; subst.
    left; eapply IHC1; eauto.
  - simpl; intros; eauto.
    inversion H; eauto.
Qed.

Lemma wait_barriers2 C : forall b C',
  wait C = Some (b,  C') ->
  forall b0, List.In b0 (barriers C') -> List.In b0 (barriers C).
Proof.
  induction C; intros b' C'; try now inversion 1.
  simpl; intros.
  destruct (wait C1) as [[? ?]|]; inversion H; subst.
  simpl in H0; rewrite List.in_app_iff in H0; destruct H0.
  rewrite List.in_app_iff; left; eapply IHC1; eauto.
  rewrite List.in_app_iff; eauto.
Qed.
  
Lemma bspec_irr' : forall n nt bs1 bs2 Q (i : Fin.t nt) C s h,
  safe_nt bs1 i n C s h Q ->
  (List.Forall (fun i => bs1 i = bs2 i) (barriers C) ) ->
  safe_nt bs2 i n C s h Q.
Proof.
  induction n; intros; simpl in *; eauto.
  repeat lazymatch goal with
    | [H : _ /\ _ |- _] => destruct H
  end; repeat split; eauto.
  - intros.
    destruct (H4 hF h0 c' ss' H6 H7 H8) as (h' & ph' & ? & ? & ? & ?).
    exists h', ph'; repeat split; eauto.
    eapply IHn; eauto.
    apply Forall_forall; rewrite Forall_forall in H0.
    intros; apply H0.
    eapply barriers_step0 in H8; eauto.
  - intros.
    destruct (H5 j c' H6) as (phP & ph' & ? & ? & ? & ?).
    exists phP, ph'; repeat split; eauto.
    + unfold pre_j in *.
      rewrite Forall_forall in H0; erewrite <-H0; eauto.
      eapply wait_barriers1; eauto.
    + intros; specialize (H10 phQ H11).
      rewrite Forall_forall in H0; unfold post_j in *; erewrite <- H0 in H12; eauto.
      specialize (H10 H12).
      eapply IHn; eauto.
      apply Forall_forall; intros; apply H0; eauto.
      eapply wait_barriers2; eauto.
      eapply wait_barriers1; eauto.
Qed.

Lemma bspec_irr (nt : nat) : forall bs1 bs2 P Q (i : Fin.t nt) C,
  CSL bs1 i P C Q ->
  (List.Forall (fun i => bs1 i = bs2 i) (barriers C) ) ->
  CSL bs2 i P C Q.
Proof.
  unfold CSL, CSL.safe_nt; intros.
  eapply bspec_irr'; eauto.
Qed.

Lemma prescan_correct (i : Fin.t ntrd) : 
  CSL (fun n => if Nat.eq_dec n 0 then bspec n
                else if Nat.eq_dec n 1 then bspec1 n
                else default ntrd) i
      (is_array Sum 2 f_ini (nf i * 2) ** !(Tid === Zn (nf i)))
      prescan
      (Ex f : nat -> Z,
      !(pure
          (forall j : nat,
             nf i * 2 <= j < (nf i + 1) * 2 -> f j = sum_of 0 j f_ini)) **
       is_array Sum 2 f (nf i * 2)).
Proof.
  unfold prescan.
  eapply rule_seq.
  { lazymatch goal with
      | [|- CSL _ _ _ ?C _] => cutrewrite (C = upsweep (nf i)); [|reflexivity]
    end.
    eapply bspec_irr.
    eapply upsweep_correct.
    simpl; apply Forall_forall; intros.
    simpl in H; destruct H as [|[]]; subst; simpl; eauto. }
  { eapply rule_seq.
    eapply rule_if_disj.
    - eapply Hbackward.
      Focus 2.
      { intros s h H.
        ex_dest_in H f; sep_split_in H.
        change_in H.
        { unfold_pures; rewrite e in HP0.
          cutrewrite (0%Z = Zn 0) in HP0; [|eauto].
          apply Nat2Z.inj in HP0; rewrite <-HP0 in H; simpl in H.
          exact H. }
        sep_split_in H.
        sep_rewrite_in is_array_unfold' H; simpl in H; try omega.
        sep_combine_in H.
        ex_intro f H; exact H.
        destruct ntrd_is_p2 as [e He]; rewrite He; pose proof (Nat.pow_nonzero 2 e); try omega. }
      Unfocus.

      repeat hoare_forward.
      intros s h H; ex_intro x H; exact H.

    - apply rule_skip.

    - eapply Hbackward.
      lazymatch goal with
        | [|- CSL _ _ _ ?C _] => cutrewrite (C = downsweep (nf i)); [|reflexivity]
      end.
      eapply bspec_irr.
      eapply downsweep_correct.
      simpl; apply Forall_forall; intros.
      simpl in H; destruct H as [|[]]; subst; simpl; eauto.
      intros s h [[f H]| H].
      exists (fun x => if Nat.eq_dec x (ntrd * 2 - 1) then 0%Z else f x).
      + sep_split_in H; sep_split; eauto.
        unfold_pures; rewrite HP0 in e; cutrewrite (0%Z = Zn 0) in e; [|auto].
        apply Nat2Z.inj in e; rewrite e; simpl; sep_split.
        * intros i0 Hi0; specialize (HP2 i0 Hi0).
          destruct Nat.eq_dec; eauto.
        * assert (ntrd <> 0) by (destruct ntrd_is_p2 as [? Hn]; rewrite Hn; apply Nat.pow_nonzero; eauto).
          sep_rewrite is_array_unfold'; try omega.
          simpl; destruct Nat.eq_dec; try omega.
          sep_lift 1; sep_cancel.
          sep_rewrite is_array_change; [apply H|].
          intros x Hx; rewrite <-plus_n_O; destruct Nat.eq_dec; try omega.
      + ex_dest_in H f; exists f; sep_split_in H; sep_split; eauto.
        unfold_pures; rewrite HP0 in n; cutrewrite (0%Z = Zn 0) in n; [|auto].
        rewrite Nat2Z.inj_iff in n; destruct Nat.eq_dec; try omega; eauto. }
Qed.

Definition G (v : var) :=
  if var_eq_dec v Tid then Hi
  else if var_eq_dec v Tmp1 then Hi
  else if var_eq_dec v Tmp2 then Hi
  else Lo.

Lemma typing_prescan : typing_cmd G prescan Lo.
Proof.
  unfold prescan.
  (repeat econstructor); (repeat instantiate (1 := Lo)); try reflexivity.
  constructor.
  repeat (instantiate (1 := Lo)); reflexivity.
  repeat (instantiate (1 := Lo)); reflexivity.
  repeat (instantiate (1 := Lo)); reflexivity.
  constructor.
  repeat (instantiate (1 := Lo)); reflexivity.
  repeat (instantiate (1 := Lo)); reflexivity.
  repeat (instantiate (1 := Lo)); reflexivity.
  Grab Existential Variables.
  apply Lo.
Qed.

Lemma low_assn_emp G : low_assn G emp.
Proof.
  intros s1 s2 h Hl; split; intros H; exact H.
Qed.

Lemma low_assn_mp G E1 E2 q :
  typing_exp G E1 Lo ->
  typing_exp G E2 Lo ->
  low_assn G (E1 -->p (q, E2)).
Proof.
  intros H1 H2 s1 s2 h Hl.
  simpl; unfold_conn; split; simpl; intros H.
  erewrite (@low_eq_eq_exp G E1), (@low_eq_eq_exp G E2); eauto.
  apply low_eq_sym; auto.
  apply low_eq_sym; auto.
  erewrite (@low_eq_eq_exp G E1), (@low_eq_eq_exp G E2); eauto.
Qed.

Lemma low_assn_star G P Q : 
  low_assn G P -> low_assn G Q ->
  low_assn G (P ** Q).
Proof.
  intros HP HQ; unfold "**"; intros s1 s2 h Hl; simpl.
  specialize (HP s1 s2); specialize (HQ s1 s2); simpl in *.
  split; intros (ph1 & ph2 & H); exists ph1, ph2.
  rewrite HP, HQ in H; [exact H|auto..].
  rewrite HP, HQ; [exact H|auto..].
Qed.

Lemma low_assn_is_array G E n f : forall s,
  G E = Lo ->
  CSL.low_assn G (is_array E n f s).
Proof.
  induction n; simpl in *; intros s He.
  - apply low_assn_emp.
  - apply low_assn_star.
    apply low_assn_mp.
    cutrewrite (Lo = join Lo Lo); [|reflexivity].
    repeat constructor; auto.
    constructor.
    apply IHn; auto.
Qed.

Lemma low_assn_ex {T : Type} G (P : T -> assn) :
  (forall x, low_assn G (P x)) ->
  low_assn G (Ex x, P x).
Proof.
  unfold low_assn, indeP.
  intros Hl s1 s2 h Hlow; simpl.
  split; intros [x H]; exists x; simpl in *.
  rewrite Hl.
  exact H.
  apply low_eq_sym; eauto.
  rewrite Hl.
  exact H.
  eauto.
Qed.

Lemma low_assn_pure G P :
  low_assn G (pure P).
Proof.
  intros s1 s2 h Hlow; simpl. unfold Apure; split; auto.
Qed.

Lemma low_assn_ban G P :
  low_assn G P ->
  low_assn G !(P).
Proof.
  intros Hl s1 s2 h Hlow; simpl.
  unfold ban, "//\\"; intros.
  unfold low_assn, indeP in Hl; simpl in Hl.
  rewrite Hl; eauto.
  split; intros H; exact H.
Qed.

Lemma low_assn_eeq E1 E2 G:
  typing_exp G E1 Lo ->
  typing_exp G E2 Lo ->
  low_assn G (E1 === E2).
Proof.
  intros H1 H2; unfold_conn; intros s1 s2 h Hlow; simpl.
  erewrite (@low_eq_eq_exp G E1); eauto.
  erewrite (@low_eq_eq_exp G E2); eauto.
  split; auto.
Qed.

Ltac prove_low_assn :=
  match goal with
    | [|- low_assn _ (Ex _, _) ] => apply low_assn_ex; intros
    | [|- low_assn _ (_ ** _) ] => apply low_assn_star
    | [|- low_assn _ ( !(_) ) ] => apply low_assn_ban
    | [|- low_assn _ ( _ === _) ] => apply low_assn_eeq
    | [|- low_assn _ (pure _) ] => apply low_assn_pure
    | [|- low_assn _ (if ?X then _ else _) ] => destruct X
    | [|- low_assn _ (is_array _ _ _ _) ] => apply low_assn_is_array
    | [|- low_assn _ emp ] => apply low_assn_emp
    | _ => now (unfold low_assn, indeP; intros; tauto)
  end.
Hint Constructors typing_exp.

Lemma default_wf n (s : stack) (h : pheap) : 
  Aistar_v (fst (default n)) s h -> Aistar_v (snd (default n)) s h.
Proof.
  cutrewrite (fst (default n) = snd (default n)); tauto.
Qed.

Lemma mps_precise E1 E2 E2' q st : forall h1 h2 h1' h2' ,
  (E1 -->p (q, E2)) st h1 ->
  (E1 -->p (q, E2')) st h1' ->
  pdisj h1 h2 -> pdisj h1' h2' -> phplus h1 h2 = phplus h1' h2' ->
  h1 = h1'.
Proof.
  intros; unfold_conn_all.
  destruct h1 as [h1 ?], h1' as [h1' ?]; simpl in *.
  apply pheap_eq; extensionality x.
  apply (f_equal (fun f => f x)) in H3; unfold phplus in H3.
  specialize (H1 x); specialize (H2 x).
  rewrite H, H0 in *.
  destruct (Z.eq_dec x (edenot E1 st)).
  destruct (h2 x) as [[? ?]|], (h2' x) as [[? ?]|]; try eauto; inversion H3; congruence.
  eauto.
Qed.

Lemma is_array_precise E f f' st n : forall s (h1 h2 h1' h2' : pheap),
  (is_array E n f s) st h1 ->
  (is_array E n f' s) st h1' ->
  pdisj h1 h2 -> pdisj h1' h2' -> phplus h1 h2 = phplus h1' h2' ->
  h1 = h1'.
Proof.
  induction n; simpl; intros.
  - apply emp_emp_ph_eq in H; apply emp_emp_ph_eq in H0; congruence.
  - destruct H as (ph1 & ph2 & ? & ? & ? & ?).
    destruct H0 as (ph1' & ph2' & ? & ? & ? & ?).
    assert (ph1 = ph1').
    { assert (pdisj ph1 (phplus ph2 h2)).
      { apply pdisj_padd_expand; eauto. rewrite H6; eauto. }
      assert (pdisj ph1' (phplus ph2' h2')).
      { apply pdisj_padd_expand; eauto. rewrite H9; eauto. }
      eapply mps_precise; [exact H | exact H0 | exact H10 | exact H11 | ..].
      rewrite <-H6 in H1.
      rewrite <-H9 in H2.
      apply pdisj_padd_expand in H1; eauto.
      apply pdisj_padd_expand in H2; eauto.
      rewrite <-!padd_assoc; try tauto.
      rewrite H9, H6; eauto. }
    cut (PHeap.this h1 = PHeap.this h1').
    { intros; destruct h1, h1'; apply pheap_eq; simpl in *; eauto. }
    rewrite <-H6, <-H9; rewrite H10; repeat f_equal.
    rewrite <-H9, <-H6 in H3.
    rewrite (@phplus_comm ph1 ph2) in H3; eauto.
    rewrite (@phplus_comm ph1' ph2') in H3; eauto.
    rewrite <-H6, (@phplus_comm ph1 ph2) in H1; eauto.
    apply pdisj_padd_expand in H1; eauto.
    rewrite <-H9, (@phplus_comm ph1' ph2') in H2; eauto.
    apply pdisj_padd_expand in H2; eauto.
    destruct H1, H2.
    eapply IHn.
    eauto. eauto.
    instantiate (1 := (phplus_pheap H11)); simpl; eauto.
    instantiate (1 := (phplus_pheap H12)); simpl; eauto.
    simpl.
    repeat (rewrite <-padd_assoc; eauto).
Qed.

Theorem prescan_correct_par :
  CSLp ntrd G 
    (is_array Sum (ntrd * 2) f_ini 0)
    prescan
    (Ex f, 
     !(pure
         (forall j : nat,
          j < ntrd * 2 -> f j = sum_of 0 j f_ini)) **
      (is_array Sum (ntrd * 2) f 0)).
Proof.
  set (Ps := MyVector.init (fun i : Fin.t ntrd => is_array Sum 2 f_ini (nf i * 2))).
  set (Qs := MyVector.init (fun i : Fin.t ntrd =>
          Ex f : nat -> Z,
            !(pure
                (forall j : nat,
                   nf i * 2 <= j < (nf i + 1) * 2 -> f j = sum_of 0 j f_ini)) **
             is_array Sum 2 f (nf i * 2))).
  eapply rule_par with (Ps := Ps) (Qs := Qs) (E := G)
         (bspec := (fun n => if Nat.eq_dec n 0 then bspec n
                else if Nat.eq_dec n 1 then bspec1 n
                else default ntrd)).
  - pose proof ntrd_neq_0; destruct ntrd; eexists; eauto; omega.
  - intros i; split; intros tid; repeat destruct Nat.eq_dec;
    unfold bspec, bspec1; subst; simpl; rewrite MyVector.init_spec;
    unfold CSL.low_assn; repeat prove_low_assn; eauto. 
  - intros i st; repeat destruct Nat.eq_dec; subst.
    apply bspec0_preserved.
    apply bspec1_preserved.
    apply default_wf.
  - 
    
    Ltac sep_destruct_in H :=
      match type of H with
        | ((Ex _, _) _ _) => destruct H as [? H]; sep_destruct_in H
        | _ => sep_split_in H
      end.

    Ltac prove_precise :=
      match goal with
        | [|- precise _] =>
          intros h1 h2 h1' h2' s Hsat Hsat' Hdis Hdis' Heq; simpl in *;
          sep_destruct_in Hsat; sep_destruct_in Hsat'; unfold_pures;
          repeat match goal with
            | [ H : s ?X = Zn _, H': s ?X = Zn _ |- _ ] => rewrite H', Nat2Z.inj_iff in H
          end; subst;
          try (match type of Hsat with
            | (if ?X then _ else _) _ _ => destruct X
          end; sep_split_in Hsat; sep_split_in Hsat')
      end.
    Hint Resolve is_array_precise precise_emp.

    intros i tid; repeat destruct Nat.eq_dec; subst; simpl; rewrite !MyVector.init_spec; split;
    try prove_precise; eauto; tauto.

  - intros s h H; unfold Ps.
    sep_rewrite sc_v2l.
    rewrite (vec_to_list_init0 _ emp).
    erewrite ls_init_eq0.
    Focus 2.
    { intros i iH.
      destruct (Fin.of_nat i ntrd) as [|Hex] eqn:Heq; [|destruct Hex; omega].
      rewrite (Fin_nat_inv Heq). reflexivity. } Unfocus.

    sep_rewrite is_array_conj; try omega.
    rewrite mult_0_r, mult_comm.
    sep_rewrite is_array_change; [apply H|auto].

  - unfold Qs; intros s h H.
    sep_rewrite_in sc_v2l H.
    rewrite (vec_to_list_init0 _ emp) in H.
    erewrite ls_init_eq0 in H.
    Focus 2.
    { intros i iH.
      destruct (Fin.of_nat i ntrd) as [|Hex] eqn:Heq; [|destruct Hex; omega].
      rewrite (Fin_nat_inv Heq). reflexivity. } Unfocus.

    sep_rewrite_in (ls_exists0 (fun _:nat=>0%Z) (n := ntrd)) H; destruct H as [fs H].
    sep_rewrite_in (@ls_star ntrd) H; sep_split_in H.
    sep_rewrite_in (@ls_pure ntrd) H; sep_split_in H.

    exists (fun i => List.nth (i / 2) fs (fun _:nat=>0%Z) i).
    sep_split.
    + unfold_conn_in HP.
      intros j Hj.

      apply (ls_emp _ _ (j / 2)) in HP0; rewrite ls_init_spec in HP0.
      assert (j / 2 < ntrd) by (apply Nat.div_lt_upper_bound; omega).
      destruct lt_dec; try omega; unfold_pures.
      rewrite <-HP0; split; try omega.
      apply div_mult; omega.
      rewrite Nat.mul_add_distr_r.
      rewrite (Nat.div_mod j 2) at 1; try omega.
      pose proof (Nat.mod_upper_bound j 2); omega.

    + apply is_array_conj in H; try omega.
      rewrite mult_0_r, mult_comm in H; apply H.


  - intros tid; unfold Ps; rewrite MyVector.init_spec.
    unfold CSL.low_assn; prove_low_assn.
    reflexivity.

  - intros tid; unfold Qs; rewrite MyVector.init_spec.
    unfold CSL.low_assn.
    repeat prove_low_assn.
  - apply typing_prescan.
  - intros tid; unfold Ps, Qs; rewrite !MyVector.init_spec.
    apply prescan_correct.
    Grab Existential Variables.
    apply ntrd.
Qed.
End Prescan.