Set Implicit Arguments.
Unset Strict Implicit.

Require Import GPUCSL.
Require Import scan_lib.
Section Fold.

(* Var *)
Notation TID := (Var 0).
Notation BID := (Var 1).
Notation I := (Var 2).
Notation St := (Var 3).
Notation T1 := (Var 4).
Notation T2 := (Var 5).
Notation ARR := (Var 6).
Notation SARR := (Var 7).

Definition If (b : bexp) (c : cmd) := Cif b c.

Variable ntrd : nat.
Variable nblk : nat.
Notation nt_gr := (nblk * ntrd).
Variable len : nat.
Hypothesis ntrd_neq_0 : ntrd <> 0.
Hypothesis ntrd_is_p2 : exists e : nat, ntrd = 2 ^ e.
Hypothesis nblk_neq_0 : nblk <> 0.

Variable f : nat -> Z.

Notation f_ss := (skip_sum nt_gr 0 len f).

Definition INV2 i :=
  Ex (s e : nat) fc,
    !(TID === Enum' i) **
    !(St === Enum' s) **
    !(pure (s = (2 ^ e / 2))) **
    !(pure (if lt_dec i (ceil2 s) then
              fc i = skip_sum (dbl s) 0 (ntrd * 2) f_ss i /\
              fc (i + s) = skip_sum (dbl s) 0 (ntrd * 2) f_ss (i + s)
            else True)) **
    !(pure (s <= ntrd)) **
    (if Nat.eq_dec s 0 then
       nth i (distribute 1 (Sh ARR) (ntrd * 2) fc (nt_step 1) 0) emp
     else
       nth i (distribute s (Sh ARR) (ntrd * 2) fc (nt_step s) 0) emp).

Definition INV1 tid :=
  Ex (ix : nat),
    !(TID === Enum' tid) **
    !(I === Enum' (ix * nt_gr + tid)) **
    !(Apure (ix * nt_gr + tid < len + nt_gr)%nat) **
    !(T2 === skip_sum nt_gr 0 (ix * nt_gr) f tid) **
    skip_arr (Gl ARR) 0 len nt_gr f tid **
    (Ex v, Sh SARR +o Enum' tid -->p (1%Qc, v)).

Open Scope bexp_scope.

Close Scope bexp_scope.
Definition fold_ker (i : nat) :=
  I ::= (TID +C BID *C Z.of_nat ntrd) ;;
  T2 ::= [ Gl ARR +o I ] ;;
  I ::= I +C Z.of_nat ntrd *C Z.of_nat nblk ;;
  WhileI (INV1 i) ( I <C Z.of_nat len ) (
    T1 ::= [ Gl ARR +o I ] ;;
    T2 ::= T1 +C T2
  )%exp;;
  Cbarrier 0;;
  St ::= Enum' ntrd ;;
  WhileI (INV2 i) ( Enum' 0 < St ) (
    If ( Evar TID <C St ) (
      T1 ::= [ Gl ARR +o TID ] ;;
      T2 ::= [ Gl ARR +o (TID + St) ] ;;
      [ Gl ARR +o TID ] ::= T1 + T2
    ) (SKIP) ;;
    St ::= St >>1 ;;
    Cbarrier 0
  )%exp.

Definition fold_ker' : cmd := fold_ker 0.

Definition binv0 : Vector.t assn ntrd * Vector.t assn ntrd :=
  (MyVector.init (fun i : Fin.t ntrd =>
   let tid := nat_of_fin i in
   Ex s fc,
     !(St === Enum' s) **
      let tid := nat_of_fin i in
      !(pure (if lt_dec tid (dbl s) then fc tid = skip_sum (dbl s) 0 (ntrd * 2) f tid else True)) **
      nth tid (distribute (dbl s) (Gl ARR) (ntrd * 2) fc (nt_step (dbl s)) 0) emp **
      !(pure (dbl s <= ntrd))),
   MyVector.init (fun i => 
   let tid := nat_of_fin i in
   Ex s fc, 
     !(St === Enum' s) **
      let tid := nat_of_fin i in
      !(pure (if lt_dec tid (ceil2 s) then
                fc tid = skip_sum (dbl s) 0 (ntrd * 2) f tid /\
                fc (tid + s) = skip_sum (dbl s) 0 (ntrd * 2) f (tid + s)
              else True)) **
      nth tid (distribute (ceil2 s) (Gl ARR) (ntrd * 2) fc (nt_step (ceil2 s)) 0) emp **
      !(pure (dbl s <= ntrd)))).

Arguments div _ _ : simpl never.
Lemma nf_lt (n : nat) (i : Fin.t n) : nf i < n.
  destruct Fin.to_nat; simpl; eauto.
Qed.

Require Import Psatz.

Lemma id_lt_nt_gr i j n m : i < n -> j < m -> i + j * n < m * n.
Proof.
  intros.
  assert (i + j * n < n + j * n) by omega.
  assert (n + j * n <= m * n) by nia.
  omega.
Qed.

Lemma nt_gr_neq_0 : nt_gr <> 0.
Proof.
  apply Nat.neq_mul_0; tauto.
Qed.

Hint Resolve nf_lt.
Hint Resolve nt_gr_neq_0 id_lt_nt_gr nf_lt.

Theorem fold_ker_correct (tid : Fin.t ntrd) (bid : Fin.t nblk) :
  nt_gr <= len ->
  CSL (fun i => match i with O => binv0 | _ => default ntrd end) tid
  (Ex f',
   skip_arr (Sh SARR) 0 (ntrd * 2) ntrd  f' (nf tid) **
   skip_arr (Gl ARR ) 0 len        nt_gr f  (nf tid + nf bid * ntrd) **
   !(TID === Z_of_fin tid) **
   !(BID === Z_of_fin bid))
  (fold_ker (nat_of_fin tid))
  (Ex fc,
     nth (nat_of_fin tid) (distribute 1 (Gl ARR) (ntrd * 2) fc (nt_step 1) 0) emp **
     skip_arr (Gl ARR ) 0 len        nt_gr f (nf tid + nf bid * ntrd) **
     !(pure (if Nat.eq_dec (nf tid) 0 then (fc 0 = sum_of 0 (ntrd * 2) f) else True))).
Proof.
  intros Hnlen.
  unfold fold_ker, skip_arr.
  pose proof (nf_lt tid) as nf_lt.
  assert (Hnt_gr : nf tid + nf bid * ntrd < nt_gr) by eauto.
  hoare_forward.
  eapply rule_seq.
  { hoare_forward.
    intros ? ? [v H].
    unfold skip_arr in *. subA_normalize_in H. simpl in H. exact H. }

  eapply rule_seq.
  { repeat hoare_forward.
    eapply Hbackward.
    Focus 2. {
      intros s h H.
      sep_split_in H.
      change_in H.
      { unfold_pures.
        sep_lift_in H 1.
        assert (Heq : 0 = 0 * nt_gr) by auto.
        rewrite Heq in H at 1; clear Heq.
        sep_rewrite_in skip_arr_unfold' H; [|try first [now eauto | nia]..].
        exact H. }
      assert (Heq : (Gl ARR +o Zn (0 * nt_gr + (nf tid + nf bid * ntrd)) ===l
                     Gl ARR +o I) s (emp_ph loc)).
      { unfold_pures. unfold_conn; simpl; f_equal. nia. }
      sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
      sep_combine_in H; exact H. } Unfocus.
    hoare_forward. simpl. intros ? ? H; exact H. }

  eapply rule_seq.
  { hoare_forward. intros ? ? [v H]. subA_normalize_in H. simpl in H.
    ex_intro v H; exact H. }

  eapply rule_seq.
  { repeat hoare_forward; unfold INV1, skip_arr.
    - eapply rule_seq.
      { eapply Hbackward.
        Focus 2. { 
        intros s h H.
        apply ex_lift_l_in in H; destruct H as [ix H].
        sep_split_in H.
        change_in H.
        { unfold_pures.

          
          


  (* introduction *)
  unfold fold_ker.
  assert (Htid : nat_of_fin tid < ntrd) by (destruct (Fin.to_nat tid); simpl in *; try omega).
  remember (ntrd * 2) eqn:Hntrd2.

  (* exec the 1st command *)
  eapply rule_seq.
  { hoare_forward.
    simpl; intros ? ? [v H].
    eapply scRw in H; [|intros ? ? H'; subA_normalize_in H'; exact H' | intros ? ? H'; exact H'].
    simpl in H; exact H. }

  (* the loop invariant holds before the loop *)
  hoare_forward.
  Focus 3.
  { unfold INV; intros s h H.
    destruct ntrd_is_p2 as [e Hntrd].
    exists (ntrd), (S e), f.
    sep_split_in H; unfold_pures; sep_split; autorewrite with sep in *; auto.
    - destruct (lt_dec (nf tid) (ceil2 ntrd)); [|unfold_conn; auto].
      unfold dbl in *; destruct Nat.eq_dec; try omega.
      split; rewrite skip_sum1; try omega.
    - red; auto.
    - destruct (Nat.eq_dec _ _); [omega | congruence]. } Unfocus.

  (* make the precondition normal form *)
  eapply Hbackward.
  Focus 2.
  { unfold INV; intros s h H.
    sep_split_in H; destruct H as (st & e & fc & H).
    sep_combine_in H.
    ex_intro st H; ex_intro e H; ex_intro fc H.
    simpl in H.    
    exact H. } Unfocus.
  
  apply rule_ex; intros fc. apply rule_ex; intros e. apply rule_ex; intros st.
  eapply rule_seq.

  eapply rule_if_disj.
  (* then case *)
  { eapply Hbackward.
    Focus 2.
    (* unfold the skip array *) 
    { unfold INV; intros s h H.
      sep_split_in H.
      change_in H.
      { unfold_pures.
        destruct Nat.eq_dec; [omega|].
        cutrewrite (0 = 0 * st) in H; [|auto].
        apply skip_arr_unfold' in H; simpl; try omega; simpl in H.
        cutrewrite (st + 0 = 1 * st) in H; [|omega].
        sep_rewrite_in skip_arr_unfold' H; try omega.
        rewrite mult_1_l in H; exact H. }
      sep_combine_in H.
      exact H. } Unfocus.

    (* execute first read command *)
    eapply rule_seq.
    { hoare_forward. 
      intros ? ? H; exact H. }

    (* execute second read command *)
    eapply rule_seq.
    { rewrite Nat2Z.inj_add.

      (* eapply Hbackward. *)
      (* Focus 2.  *)
      (*   intros s ? Hf. *)
      (*   sep_normal_in Hf. *)
      (*   sep_split_in Hf. *)
      (*   assert ((Gl ARR +o (Z.of_nat st + Z_of_fin tid) ===l Gl ARR +o (TID + St)) s (emp_ph loc)). *)
      (*   unfold_conn_all; simpl in *. *)
      (*   f_equal. omega. *)
      (*   find_enough_resource (Gl ARR +o (TID + St)) Hf. *)
      (*   sep_combine_in Hf; *)
      (*   exact Hf. *)
      (* eapply Hforward; [ *)
      (*   eapply rule_frame; *)
      (*   [eapply rule_read; idtac "ok!!!"; prove_indeE | prove_inde] | prove_inde ]. *)
      
      hoare_forward. 
      intros ? ? H; exact H. }
    
    (* execute the write command *)
    { hoare_forward.
      intros ? ? H; exact H. } }

  (* else case *)
  apply rule_skip.

  (* rests of loop commands *)
  eapply Hforward.
  eapply rule_disj.
  (* then case *)
  - (* update s *)
    eapply rule_seq; [hoare_forward|].
    { intros s h H.
      destruct H as [st' H].
      subA_normalize_in H. simpl in H.
      ex_intro st' H; exact H. }

    (* the barrier instruction *)
    hoare_forward.
    instantiate (1 := INV (nf tid)).
    set (fc' := (fun i => if Nat.eq_dec i (nf tid) then (fc i + fc (i + st)%nat)%Z else fc i)).
    destruct e as [|e].

    + (* crush the case (e=0) *)
      forward_barr. Focus 2.
      { simpl; rewrite MyVector.init_spec.
        intros s h H; sep_normal_in H; sep_split_in H.
        unfold_conn_in (HP3, HP4, HP5); simpl in HP3, HP4, HP5.
        assert (FalseP s h) by (subst; simpl in HP3; congruence). 
        instantiate (1 := FalseP). destruct H0. } Unfocus.
      intros; unfold_conn; repeat destruct H; tauto.

    + (* fold skip array *)
      eapply Hbackward. Focus 2.
      { intros s h H; sep_split_in H.
        assert ((T1 + T2 === (fc (nf (tid)) + fc (st + nf tid)%nat)%Z) s (emp_ph loc)) by
            (unfold_conn_all; simpl in *; omega).
        fold (2 ^ S (S e) / 2) in *.
        assert (Hst : st = 2 ^ (S e) / 2) by (unfold_conn_in HP6; auto).
        cutrewrite (2 ^ (S e) = 2 ^ e * 2) in Hst; [|simpl; omega].
        rewrite Nat.div_mul in Hst; auto.
        sep_rewrite_in mps_eq2 H; [|exact H0].

        assert (nf tid < st)
          by (unfold_conn_all; simpl in *; destruct (Z_lt_dec (s TID) x); (congruence||omega)).
        sep_rewrite_in (@nth_dist_change (nat_of_fin tid) (Gl ARR) fc fc') H;
          try now (subst; auto || unfold_conn_all; simpl in *; omega).
        2 : rewrite <-!plus_n_O; intros; unfold fc'; destruct Nat.eq_dec; auto; omega.
        cutrewrite (st + (st + 0) = 2 * st) in H; [|omega].
        assert ((Gl ARR +o (TID + x) ===l Gl ARR +o Z.of_nat (1 * st + nf tid))%exp s (emp_ph loc)).
        { unfold_conn_all; simpl; simplify_loc; rewrite !Nat2Z.inj_add, Z.add_0_r; simpl in*; omega. }
        sep_rewrite_in (@mps_eq1 (Gl ARR +o (TID + x))%exp ) H; [|exact H2].
        cutrewrite (fc (nf tid) + fc (st + nf tid)%nat = fc' (0 * st + nf tid)%nat)%Z in H; [|].
        2: unfold fc'; destruct Nat.eq_dec; unfold_conn_all; simpl in *; [f_equal; f_equal; omega| omega].
        cutrewrite (fc (st + nf tid)%nat = fc' (1 * st + nf tid)%nat)%Z in H; [|].
        2: unfold fc'; destruct Nat.eq_dec; unfold_conn_all; simpl in *; [omega|f_equal; omega].
        sep_rewrite_in_r skip_arr_unfold' H; (omega || auto).
        2: unfold_conn_in HP8; omega.
        assert ((Gl (ARR + TID)%exp ===l Gl ARR +o Z.of_nat (0 * st + nf tid)) s (emp_ph loc)).
        { unfold_conn_all; simpl in *; simplify_loc; omega. }
        sep_rewrite_in mps_eq1 H; [|exact H3].
        sep_rewrite_in_r skip_arr_unfold' H; (omega || auto).
        clear HP0 HP1 HP2 H0.
        sep_combine_in H. exact H. } Unfocus.

      (* barrier pre holds at barrier (then) *)
      forward_barr. Focus 2.
      { autorewrite with sep; auto.
        simpl; rewrite MyVector.init_spec. 
        intros s h H; sep_normal_in H; sep_split_in H.
        apply ex_lift_l; exists (2 ^ e / 2); apply ex_lift_l; exists fc'.
        do 3 (sep_normal; sep_split).
        - unfold_pures. autorewrite with sep in *; auto; simpl. 
          unfold_conn; simpl; congruence.
        - unfold_pures; unfold_conn; autorewrite with sep in *.
          unfold fc' in *; clear fc'; subst st; rewrite ceil2_pow in HP4.
          destruct Nat.eq_dec; try omega; destruct (lt_dec); auto.
          destruct HP4 as [Heq1 Heq2]; rewrite Heq1, Heq2; autorewrite with sep.
          cutrewrite (2 ^ S e = 2^e*2); [|simpl; omega].
          cutrewrite (0 = 0 * 2 * (2^e * 2)); [|omega]; apply (skip_sum_double) ; omega.
        - rewrite dbl_inv.
          unfold_conn_all; simpl in *; omega.
        - sep_normal. 
          rewrite dbl_inv.
          cutrewrite (2 ^ e = st); [|unfold_conn_all; congruence].
          sep_combine_in H; sep_cancel. exact H. } Unfocus.
      
      (* loop invariant is preserved *)
      intros s h H; unfold INV; clear fc'.
      apply ex_lift_l_in in H; destruct H as (s0 & H).
      apply ex_lift_l_in in H; destruct H as (fc' & H); sep_split_in H.
      exists (2 ^ e / 2), e, fc'.
      assert ((St === Z.of_nat (2 ^ e / 2)) s (emp_ph loc)).
      { unfold_conn_in (HP, HP2, HP3); simpl in HP2, HP3; rewrite HP2, HP3 in HP; simpl in HP.
        rewrite Zdiv2_div in HP. rewrite div_Zdiv; auto. }
      assert (s0 = 2 ^ e / 2).
        { unfold_conn_in (HP8, H0); rewrite HP8 in H0; simpl in H0.
          apply Nat2Z.inj in H0; auto. }
      sep_split; try now (unfold_conn_all; (auto || omega)).
      * unfold_conn_in (HP8, H0); rewrite HP8 in H0; simpl in H0; apply Nat2Z.inj in H0;
        rewrite H0 in HP9.
        apply HP9.
      * unfold_conn_in (HP5, HP3); simpl in HP5, HP3; unfold_conn.
        assert (2 ^ e <> 0) by (apply Nat.pow_nonzero; auto).
        assert (2 ^ e / 2 < 2 ^ e) by (apply Nat.div_lt; omega).
        omega.
      * unfold ceil2 in H; destruct Nat.eq_dec; subst; destruct Nat.eq_dec; (omega || auto).
  - eapply Hbackward.
    Focus 2.
    { (* fold skip array to emp *)
      intros s h H.
      sep_normal_in H; sep_split_in H.
      change_in H.
      { unfold_pures.
        assert (Hsh : emp s h); [|apply Hsh].
        { destruct (Nat.eq_dec st 0); subst; simpl in H; [omega|].
          rewrite nth_overflow in H; [|rewrite distribute_length; omega]; auto. } }
      assert (pure (st <= nf tid) s (emp_ph loc)) by (unfold_pures; unfold_conn; omega).
      sep_combine_in H; sep_normal_in H; exact H. } Unfocus.
    
    (* update s *)
    eapply rule_seq; [hoare_forward|].
    { intros s h [v H].
      subA_normalize_in H. simpl in H. 
      sep_split_in H.
      subst_expr v. subst_expr st.
      sep_combine_in H. exact H. }
    forward_barr.
    Focus 2.
    { (* barrier pre holds at barrier (else) *)
      intros s h H; simpl; rewrite MyVector.init_spec.
      sep_normal_in H; sep_split_in H.
      apply ex_lift_l; exists ((2 ^ e) / 2 / 2).
      apply ex_lift_l; exists fc.
      sep_rewrite_in_r emp_unit_r H; sep_split_in H.
      do 3 sep_normal; sep_split.
      unfold_conn_all; simpl in *; autorewrite with sep in *; auto.
      - unfold_pures; destruct (lt_dec (nf tid) (dbl _)); unfold_conn; auto.
        rewrite HP1 in *; rewrite <-Nat2Z.inj_lt in n0.
        destruct e as [|e]; [cbv in l; inversion l|].
        autorewrite with sep in l0; autorewrite with sep in n0; auto; omega.
      - unfold_pures; unfold_conn.
        destruct e as [|e]; [cbv in l; inversion l|].
        autorewrite with sep; auto. autorewrite with sep in HP4; auto.
      - destruct e as [|e]; [unfold_pures; cbv in HP2; inversion HP2|].  
        change_; [intros Hf|].
        { autorewrite with sep in HP5; auto; unfold_pures.
          rewrite HP1 in n0; rewrite <-Nat2Z.inj_lt in n0.
          rewrite nth_overflow; [|rewrite distribute_length; autorewrite with sep in *; omega].
          exact Hf. }
        sep_combine_in H; sep_cancel; exact H. } Unfocus.

    (* loop invariant is preserved *)
    instantiate (1 := INV (nf tid)); unfold INV; intros; apply ex_lift_l_in in H; destruct H as [s0 H].
    apply ex_lift_l_in in H; destruct H as [fc' H].
    sep_split_in H.
    unfold_pures.
    destruct e; [cbv in l; congruence|].
    autorewrite with sep in *; auto.  clear HP3 HP7.
    exists (2 ^ e / 2), e, fc'; sep_split; try now simpl; first [eauto | omega | congruence];
    autorewrite with sep; auto.
    + rewrite HP1 in n0; rewrite <-Nat2Z.inj_lt in n0; unfold_conn.
      destruct e as [|e]; [destruct (lt_dec _ (ceil2 (_/_))) as [Hlt | ?]; unfold_conn; auto |].
      unfold ceil2 in Hlt; simpl in n0, Hlt; omega.

      autorewrite with sep; auto; simpl in *.
      destruct lt_dec; [omega | unfold_conn; auto].
    + unfold_conn; destruct e; [cbv; omega|autorewrite with sep; auto].
      simpl in HP4; omega.
    + cutrewrite (2%Z = Z.of_nat 2) in HP0; [|auto]; rewrite <-div_Zdiv in HP0; auto. simpl in HP0.
      rewrite HP6 in HP0; apply Nat2Z.inj in HP0; subst.
      destruct e; [unfold div, ceil2 in *; simpl in *; auto|].
      autorewrite with sep in *; auto.
      destruct Nat.eq_dec; [apply Nat.pow_nonzero in e0; auto; destruct e0|].
      apply H.
  - unfold_conn; intros; tauto.
  - intros s h H; unfold INV in *.
    apply ex_lift_l_in in H; destruct H as [? H].
    apply ex_lift_l_in in H; destruct H as [? H].
    apply ex_lift_l_in in H; destruct H as [fc' H].
    sep_split_in H.
    assert (x = 0).
    { unfold_conn_in (HP, HP1); simpl in HP, HP1; destruct Z_lt_dec; simpl in HP; try congruence.
      rewrite HP1 in n0; cutrewrite (0%Z = Z.of_nat 0) in n0; [|auto]; rewrite <-Nat2Z.inj_lt in n0.
      omega. }
    subst; simpl in *.
    exists fc'.
    sep_split; auto.
    destruct (Nat.eq_dec (nf tid) 0); [|cbv; tauto].
    rewrite e in HP3; simpl in HP3; destruct HP3.
    unfold dbl in H0; simpl in H0.
    rewrite skip_sum_sum in H0. auto.
Qed.

  
Definition ty_env_fold (v : var) :=
  if var_eq_dec v TID then Hi
  else if var_eq_dec v T1 then Hi
  else if var_eq_dec v T2 then Hi
  else Lo.

Lemma typing_fold : typing_cmd ty_env_fold fold_ker' Lo.
Proof.
  repeat constructor.
  econstructor.
  instantiate (1:=Lo); constructor.
  reflexivity.
  repeat econstructor.
  instantiate (1:=Lo); reflexivity.
  constructor.
Qed.


Lemma barrier_wf : Bdiv.Aistar_v (fst binv0) |= Bdiv.Aistar_v (snd binv0).
Proof.
  simpl; intros s h H.
  apply sc_v2l in H.
  rewrite (vec_to_list_init0 _ emp) in H.
  erewrite ls_init_eq0 in H.
  Focus 2.
  { intros i iH.
    destruct (Fin.of_nat i ntrd) as [|Hex] eqn:Heq; [|destruct Hex; omega].
    rewrite (Fin_nat_inv Heq). reflexivity. } Unfocus.
  apply sc_v2l.
  rewrite (vec_to_list_init0 _ emp).
  erewrite ls_init_eq0.
  Focus 2.
  { intros i iH.
    destruct (Fin.of_nat i ntrd) as [|Hex] eqn:Heq; [|destruct Hex; omega].
    rewrite (Fin_nat_inv Heq). reflexivity. } Unfocus.

  sep_rewrite_in (ls_exists0 0 (n := ntrd)) H; auto; destruct H as [vs H].
  sep_split_in H.
  sep_rewrite_in (ls_exists0 (fun _ : nat => 0%Z) (n:=ntrd)) H; auto; destruct H as [fs H].
  sep_split_in H.

  repeat sep_rewrite_in (@ls_star ntrd) H.

  repeat sep_rewrite_in (@ls_pure ntrd) H; sep_split_in H.
  
  assert (exists s0, forall i, i < ntrd -> nth i vs 0 = s0) as [s0 Hs0].
  { destruct vs as [|s0 vs]; [cbv in HP; omega|].
    exists s0; intros i.
    destruct i; simpl; auto.
    pose proof (@ls_emp _ _ 0 HP1); rewrite ls_init_spec in H0; destruct lt_dec; try omega.
    pose proof (@ls_emp _ _ (S i) HP1); rewrite ls_init_spec in H1; destruct lt_dec; try omega.
    unfold_conn_all; simpl in *.
    assert (Z.of_nat s0 = Z.of_nat (nth i vs 0)) by congruence.
    apply Nat2Z.inj in H2; congruence. }
  pose proof (@ls_emp _ _ 0 HP3) as Hs0ntrd; rewrite ls_init_spec in Hs0ntrd;
  destruct lt_dec; unfold_conn_in Hs0ntrd; try omega.
  rewrite Hs0 in Hs0ntrd; try omega.
  
  erewrite ls_init_eq0 in H; [|intros; rewrite Hs0; auto; reflexivity].
  erewrite ls_init_eq0 in HP2; [|intros; rewrite Hs0; auto; reflexivity].
  erewrite ls_init_eq0 in HP3; [|intros; rewrite Hs0; auto; reflexivity].
  sep_rewrite (ls_exists0 0 (n:= ntrd)); auto; exists vs.
  sep_split; auto.
  sep_rewrite (ls_exists0 (fun _:nat => 0%Z) (n:=ntrd)); auto.
  set (fcc := fun i : nat =>
         (nth (i mod (dbl s0)) fs (fun _:nat=>0%Z)) i).
  exists (nseq ntrd fcc); sep_split; [rewrite length_nseq; reflexivity|].
  (repeat sep_rewrite (@ls_star ntrd)). 
  repeat sep_rewrite (@ls_pure ntrd).
  repeat sep_split; auto.

  apply ls_emp'; intros i Hi; rewrite init_length in Hi.
  rewrite ls_init_spec; destruct lt_dec; try omega; simpl.
  rewrite Hs0; auto; destruct lt_dec; [|cbv; auto].
  rewrite nth_nseq; destruct (leb ntrd i) eqn:Heq; try (apply leb_iff in Heq; omega).
  unfold fcc.

  pose proof (ceil2_dbl s0).
  repeat (rewrite Nat.mod_small; [|omega]).
  split.
  pose proof (@ls_emp _ _ i HP2); rewrite ls_init_spec in H1.
  destruct (lt_dec i ntrd); try omega.
  destruct (lt_dec (0 + i) (dbl s0)); try omega.
  apply H1.
  pose proof (@ls_emp _ _ 0 HP3); rewrite ls_init_spec in H1; destruct lt_dec; unfold_conn_in H1; try omega.
  pose proof (@ls_emp _ _ (i + s0) HP2); rewrite ls_init_spec in H2.
  destruct (lt_dec (i + s0) ntrd); try omega.
  destruct (lt_dec (0 + (i + s0)) (dbl s0)); try omega.
  apply H2.
  erewrite ls_init_eq0; [|intros; rewrite Hs0; auto; reflexivity]; auto.
  
  rewrite <-(firstn_skipn (dbl s0) (ls_init _ _ _)) in H.
  rewrite firstn_init, skipn_init in H.
  rewrite Nat.min_l in H; auto; rewrite <-plus_n_O in *; auto.
  
  apply conj_xs_app in H.
  lazymatch type of H with
    | ((_ ** conj_xs (ls_init ?b ?n ?P)) _ _) =>
      evar (fc : nat -> assn); 
      sep_rewrite_in (@ls_init_eq' _ P fc n b) H; unfold fc in *
  end.
  2: intros i Hi; simpl; rewrite nth_overflow; [|rewrite distribute_length; omega].
  2: instantiate (1 := fun _ => emp); reflexivity.
  

  sep_rewrite_in init_emp_emp H; sep_normal_in H.
  
  erewrite ls_init_eq0.
  2: intros i Hi; rewrite nth_nseq; destruct (leb ntrd i) eqn:Heq;
    try ((apply leb_iff in Heq || apply leb_iff_conv in Heq); omega).
  2: reflexivity.
  

  sep_rewrite_in equiv_from_nth H.
  Focus 3.
  { rewrite init_length; intros i Hi stc; rewrite ls_init_spec at 1.
    destruct (lt_dec i (dbl s0)); try omega.
    simpl.
    rewrite nth_dist_change; [|auto..|].
    Focus 2.
    { unfold nt_step; instantiate (1 := fcc); intros j Hj Hnt.
      rewrite <-plus_n_O in *.
      unfold fcc; rewrite Hnt; auto. } Unfocus.
    reflexivity. } Unfocus.
  2: rewrite init_length, distribute_length; auto.
  
  apply distribute_correct in H; auto.

  rewrite <-(firstn_skipn (ceil2 s0) (ls_init _ _ _)).
  rewrite firstn_init, skipn_init.
  rewrite Nat.min_l; auto; try omega.
  2 : pose proof (ceil2_dbl s0); omega.
  
  apply conj_xs_app. clear fc.
  lazymatch goal with
    | [|- ((_ ** conj_xs (ls_init ?b ?n ?P)) _ _)] =>
      evar (fc : nat -> assn); 
      sep_rewrite (@ls_init_eq' _ P fc n b); unfold fc in *
  end.
  2: intros i Hi; simpl; rewrite nth_overflow; [|rewrite distribute_length, Hs0; omega ].
  2: instantiate (1 := fun _ => emp); reflexivity.
  sep_rewrite init_emp_emp; sep_normal.

  
  sep_rewrite equiv_from_nth.
  Focus 3.
  { rewrite init_length. intros i Hi stc; rewrite ls_init_spec at 1.
    destruct (lt_dec i); try omega.
    simpl; rewrite Hs0. reflexivity.
    auto.
    pose proof (ceil2_dbl s0). omega. } Unfocus.
  2: rewrite distribute_length, init_length; auto.
  apply distribute_correct; auto.
Qed.
End Fold.