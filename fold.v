Set Implicit Arguments.
Unset Strict Implicit.

Require Import GPUCSL.
Section Fold.

(* Var *)
Notation I := (Var 1).
Notation St := (Var 2).
Notation T1 := (Var 3).
Notation T2 := (Var 4).
Notation ARR := (Var 5).

Fixpoint sum_of (s len : nat) (f : nat -> Z) :=
  match len with
    | O => 0
    | S len => f s + sum_of (S s) len f
  end%Z.

Definition skip_sum_body (f : nat -> Z)  (skip : nat) (Hskip : skip <> 0)  :
  forall (len : nat)
    (rec : forall len', len' < len -> nat -> Z)
    (s : nat), Z.
  refine (
  fun len rec s => 
    match len as l0 return l0 = len -> Z with
      | O => fun _ => 0
      | _ => fun _ => f s + rec (len - skip)%nat _ (s + skip)%nat
    end eq_refl)%Z.
  abstract omega.
Defined.

Definition skip_sum (skip : nat) (Hskip : skip <> 0) (len s : nat) (f : nat -> Z) : Z :=
  Fix lt_wf (fun _ => nat -> Z) (skip_sum_body f Hskip) len s.

Example two_neq_0 : 2 <> 0. now auto. Qed.
Eval compute in skip_sum two_neq_0 10 0 (fun i => Z.of_nat i).

Lemma Fix_eq_ok f skip (Hskip : skip <> 0) :
  forall (len : nat) (F G : forall len' : nat, len' < len -> nat -> Z),
  (forall (len' : nat) (p : len' < len), F len' p = G len' p) ->
  skip_sum_body f Hskip F = skip_sum_body f Hskip G.
Proof.
  intros; unfold skip_sum_body.
  assert (F = G) by (do 2 let x := fresh in extensionality x; auto).
  rewrite !H0; auto.
Qed.

Notation " p '>>1'" := (Ediv2 p) (at level 40, left associativity) : exp_scope.

Definition If (b : bexp) (c : cmd) := Cif b c.

Variable ntrd : nat.
Hypothesis ntrd_neq_0 : ntrd <> 0.
Hypothesis ntrd_is_p2 : exists e : nat, ntrd = 2 ^ e.

Definition arr_val_compat (len : nat) (f : nat -> Z) (sum : Z) :=
  match len with
    | O => f 0 = sum
    | _ => sum_of 0 len f = sum
  end.

Variable f : nat -> Z.

Definition INV i :=
  Ex (s e : nat) (fc : nat -> Z),
    !(TID === Enum' i) **
    !(St === Enum' s) **
    !(pure (s = (2 ^ e / 2))) **
    !(pure (arr_val_compat (2 * s) fc (sum_of 0 (2 * ntrd) f))) **
    !(pure (s <= ntrd)) **
    (if Nat.eq_dec s 0 then
       nth i (distribute 1 ARR (2 * ntrd) fc (nt_step 1) 0) emp
     else
       nth i (distribute s ARR (2 * ntrd) fc (nt_step s) 0) emp).

Open Scope bexp_scope.

Definition fold_ker' :=
  St ::= Enum' ntrd ;;
  Cwhile ( Enum' 0 < St ) (
    If ( Evar TID < St ) (
      T1 ::= [ ARR + TID ] ;;
      T2 ::= [ ARR + TID + St ] ;;
      [ ARR + TID ] ::= T1 + T2
    ) (SKIP) ;;
    St ::= St >>1 ;;
    Cbarrier 0
  )%exp.
Close Scope bexp_scope.
Definition fold_ker (i : nat) :=
  St ::= Enum' ntrd ;;
  WhileI (INV i) ( Enum' 0 < St ) (
    If ( Evar TID < St ) (
      T1 ::= [ ARR + TID ] ;;
      T2 ::= [ ARR + TID + St ] ;;
      [ ARR + TID ] ::= T1 + T2
    ) (SKIP) ;;
    St ::= St >>1 ;;
    Cbarrier 0
  )%exp.

Definition binv0 : Vector.t assn ntrd * Vector.t assn ntrd :=
  (MyVector.init (fun i : Fin.t ntrd =>
   let tid := nat_of_fin i in
   Ex s fc, 
     !(St === Enum' s) **
     !(pure (arr_val_compat (2 * s) fc (sum_of 0 (2 * ntrd) f))) **
       let tid := nat_of_fin i in
       nth tid (distribute (2 * s) ARR (2 * ntrd) fc (nt_step (2 * s)) 0) emp),
   MyVector.init (fun i => 
   let tid := nat_of_fin i in
   Ex s fc, 
     !(St === Enum' s) **
     !(pure (arr_val_compat (2 * s) fc (sum_of 0 (2 * ntrd) f))) **
       let tid := nat_of_fin i in
       nth tid (distribute s ARR (2 * ntrd) fc (nt_step s) 0) emp)).

Lemma arr_compat_same (len : nat) (fc : nat -> Z) :
  len <> 0 -> arr_val_compat len fc (sum_of 0 len fc).
Proof.
  induction len; simpl in *; auto; omega.
Qed.

Require Import SetoidClass.
Instance app_proper (s : stack) (h : pheap) : Proper (equiv_sep s ==> iff) (fun P => P s h).
Proof.
  intros P Q H.
  specialize (H h); auto.
Qed.

Ltac fold_pure H s :=
  lazymatch type of H with
    | ?X =>
      let Hf := fresh in
      assert (Hf : !(pure X) s emp_ph) by (apply pure_emp; [auto|apply emp_emp_ph]);
        clear H; rename Hf into H
end.

Ltac rewrite_sep_in lem H :=
  match type of H with
    | ?X _ _ => pattern X in H
  end; erewrite lem in H; cbv beta in H. 

Lemma sum_of_concat (l1 : nat) (fc : nat -> Z) : forall s l2,
  sum_of s (l1 + l2) fc = (sum_of s l1 fc + sum_of (l1 + s) l2 fc)%Z.
Proof.
  induction l1; [simpl; auto|].
  intros s l2; simpl. rewrite IHl1.
  rewrite plus_n_Sm; omega.
Qed.
   
Lemma shift_values (l1 : nat) (fc : nat -> Z) : forall s sft,
  (sum_of s l1 fc + sum_of (s + sft) l1 fc = sum_of s l1 (fun i => fc i + fc (i + sft)%nat))%Z.
Proof.
  induction l1; intros; simpl; auto.
  cutrewrite (S (s + sft) = S s + sft); [|omega].
  cutrewrite (
    (fc s + sum_of (S s) l1 fc + (fc (s + sft)%nat + sum_of (S s + sft) l1 fc)) =
    (fc s + (fc (s + sft)%nat + (sum_of (S s) l1 fc + sum_of (S s + sft) l1 fc))))%Z; [|ring].
  rewrite (IHl1 (S s) (sft)). omega.
Qed.

Lemma sum_of_eq (len : nat) (f1 f2 : nat -> Z) : forall s,
   (forall i, s <= i < s + len -> f1 i = f2 i) ->
   sum_of s len f1 = sum_of s len f2.
Proof.
  induction len; intros; simpl; auto.
  rewrite IHlen, (H s); auto; intros; try omega.
  apply H; omega.
Qed.

Lemma shift_arr (len : nat) (fc : nat -> Z) : forall s, 
   sum_of s (len * 2) fc = sum_of s len (fun i => if lt_dec i (s + len) then fc i + fc (i + len)%nat else fc i)%Z.
Proof.
  cutrewrite (len * 2 = len + len); [|omega].
  intros s; rewrite sum_of_concat.
  rewrite (plus_comm len s), shift_values.
  apply sum_of_eq; intros; destruct lt_dec; omega.
Qed.

Corollary shift_arr0 (len : nat) (fc : nat -> Z) : 
  sum_of 0 (len * 2) fc = sum_of 0 len (fun i => if lt_dec i len then fc i + fc (i + len)%nat else fc i)%Z.
Proof.
  apply shift_arr.
Qed.

Notation nf tid := (nat_of_fin tid).

Lemma ex_lift_l {T : Type} (P : T -> assn) (Q : assn) :
  (Ex x, P x ** Q) |= (Ex x, P x) ** Q.
Proof.
  intros; unfold_conn; destruct H as (x & H & ? & ? & ? & ? & ?).
  repeat eexists; eauto.
Qed.

Lemma sep_rewrite_var (v : var) (E : exp) (P : assn) s h:
  (v === E) s emp_ph -> P s h -> subA v E P s h.
Proof.
  unfold eeq, ban, subA'; simpl; intros.
  assert (Heq: var_upd s v (edenot E s) = s); [|rewrite Heq; auto].
  extensionality v'; unfold var_upd; rewrite <-H; destruct var_eq_dec; congruence.
Qed.

Lemma mps_eq1 (E1 E1' E2  : exp) (q : Qc) :
  forall s,
    (E1 === E1') s emp_ph ->
    s ||= E1 -->p (q, E2) <=> E1' -->p (q, E2).
Proof.
  intros s H1 h; split; intros; eapply mapsto_rewrite1; eauto;
  unfold_conn_all; simpl in *; auto.
Qed.

Lemma mps_eq2 (E1 E2 E2'  : exp) (q : Qc) :
  forall s,
    (E2 === E2') s emp_ph ->
    s ||= E1 -->p (q, E2) <=> E1 -->p (q, E2').
Proof.
  intros s H1 h; split; intros; eapply mapsto_rewrite2; eauto;
  unfold_conn_all; simpl in *; auto.
Qed.

Theorem fold_ker_correct (tid : Fin.t ntrd) : 
  CSL (fun i => match i with O => binv0 | _ => default ntrd end) tid
  (nth (nat_of_fin tid) (distribute ntrd ARR (2 * ntrd) f (nt_step ntrd) 0) emp **
   !(TID === Z_of_fin tid))
  (fold_ker (nat_of_fin tid))
  (Ex fc,
     nth (nat_of_fin tid) (distribute 1 ARR (2 * ntrd) fc (nt_step 1) 0) emp **
     !(pure (fc 0 = sum_of 0 (2 * ntrd) f))).
Proof.
  unfold fold_ker.
  assert (Htid : nat_of_fin tid < ntrd) by (destruct (Fin.to_nat tid); simpl in *; try omega).
  remember (2 * ntrd) eqn:Hntrd2.

  eapply rule_seq.
  { hoare_forward.
    simpl; intros ? ? [v H].
    eapply scRw in H; [|intros ? ? H'; subA_normalize_in H'; exact H' | intros ? ? H'; exact H'].
    simpl in H; exact H. }

  hoare_forward.
  Focus 3.
  { unfold INV. intros s h H.
    destruct ntrd_is_p2 as [e Hntrd].
    exists (ntrd), (S e), f.
    sep_split_in H; sep_split; auto.
    - rewrite Nat.pow_succ_r', mult_comm, Nat.div_mul; auto; unfold_conn; auto.
    - apply arr_compat_same; omega.
    - red; auto.
    - destruct (Nat.eq_dec _ _); [omega | congruence]. } Unfocus.

  (* make the precondition normal form *)
  eapply Hbackward.
  Focus 2.
  { unfold INV; intros s h H.
    sep_split_in H; destruct H as (st & e & fc & H).
    sep_combine_in H.
    ex_intro st H; ex_intro e H; ex_intro fc H; simpl in H.    
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

      Ltac change_in H :=
        lazymatch type of H with
          | _ ?s ?h =>
            let P := fresh "P" in 
            let Hf := fresh "H" in
            evar (P : assn); assert (Hf : P s h); unfold P in *; clear P; [| clear H; rename Hf into H]
        end.
      change_in H.
      { red in HP0, HP1, HP2; simpl in HP0, HP1, HP2.
        destruct Z_lt_dec; [|congruence]. destruct Nat.eq_dec; [omega|].
        subst; remember (2 * ntrd) as n eqn:Hntrd2.
        cutrewrite (0 = 0 * st) in H; [|auto].
        red in HP, HP5; simpl in HP, HP5; destruct (Z_lt_dec); try congruence.
        apply skip_arr_unfold' in H; try omega; simpl in H.
        cutrewrite (st + 0 = 1 * st) in H; [|omega].
        rewrite_sep_in skip_arr_unfold' H; try omega.
        rewrite mult_1_l in H; exact H. }
      sep_combine_in H.
      exact H. } Unfocus.
    (* execute first read command *)
    eapply rule_seq.
    { hoare_forward. 
      apply inde_distribute; repeat (constructor; auto).
      intros ? ? H; exact H. }

    (* execute second read command *)
    eapply rule_seq.
    { cutrewrite (Z.of_nat (st + nat_of_fin tid) = Z.of_nat st + Z.of_nat (nat_of_fin tid))%Z; [|apply Nat2Z.inj_add].
      hoare_forward. 
      apply inde_distribute; repeat (constructor; auto).
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
  - eapply rule_seq; [hoare_forward|].
    { intros s h H.
      destruct H as [st' H].
      subA_normalize_in H. simpl in H.
      ex_intro st' H; exact H. }

    (* the barrier instruction *)
    hoare_forward.
    instantiate (1 := INV (nf tid)).
    set (fc' := fun i => if lt_dec i st then (fc i + fc (i + st)%nat)%Z else fc i).
    destruct e as [|[|e]].
    Ltac forward_barr := lazymatch goal with
      | [ |- CSL ?bspec ?tid ?P (Cbarrier ?i) ?Q] =>
        eapply Hbackward; [
            eapply Hforward; [
              eapply rule_frame; 
              [eapply rule_barrier |
               unfold inde; simpl; intros; match goal with [H : False |- _] => destruct H end] |
              autounfold; simpl; repeat rewrite MyVector.init_spec in *] | ] end.
    + forward_barr. Focus 2.
      { simpl; rewrite MyVector.init_spec.
        intros s h H; sep_normal_in H; sep_split_in H.
        unfold_conn_in (HP3, HP4, HP5); simpl in HP3, HP4, HP5.
        assert (FalseP s h) by (subst; simpl in HP3; congruence). 
        instantiate (1 := FalseP). destruct H0. } Unfocus.
      intros; unfold_conn; repeat destruct H; tauto.
    + eapply Hbackward.
      Focus 2.
      { intros s h H; sep_normal_in H; sep_split_in H.
        unfold_conn_in (HP4, HP5); simpl in *; 
        lazymatch goal with [H : _ |- _] => rewrite HP4, HP5 in H end; simpl in *.
        apply (sep_rewrite_var HP) in H; subA_normalize_in H. simpl in H.
        apply (sep_rewrite_var HP0) in H; subA_normalize_in H. simpl in H.
        apply (sep_rewrite_var HP2) in H; subA_normalize_in H. simpl in H.
        assert (nf tid = 0).
        { unfold_conn_in (HP2, HP1); simpl in HP1, HP2.
          destruct Z_lt_dec; try congruence; omega. } 
        rewrite_sep_in (@nth_dist_change (nat_of_fin tid) ARR fc fc') H; try (auto || omega).
        Focus 2. { unfold fc'; intros j Hj _; destruct lt_dec; try omega. } Unfocus.
        assert (Heq : (fc (nf tid) + fc (S (nf tid)) === fc' (nf tid)) s emp_ph).
        { unfold fc'; rewrite HP5, H0; simpl; unfold_conn; auto. }
        rewrite_sep_in mps_eq2 H; [clear Heq | rewrite HP5; exact Heq].
        cutrewrite (fc (S (nf tid)) = fc' (S (nf tid))) in H; 
            [|unfold fc'; rewrite H0, HP5; simpl; unfold_conn; auto].

        Ltac rewrite_sep_r_in lem H :=
          match type of H with
            | ?X _ _ => pattern X in H
          end; rewrite <-lem in H; cbv beta in H.
        Hint Resolve Nat2Z.inj_add : zarith.
        assert (s ARR + Z.of_nat (1 + (nf tid)) = s ARR + Z.of_nat (nf tid) + 1%Z)%Z by
            (rewrite Nat2Z.inj_add; cutrewrite (Z.of_nat 1 = 1%Z); [omega|auto]). 
        find_enough_resource (ARR + Z.of_nat (1 + (nf tid)))%exp H.
        sep_lift_in H 1.
        cutrewrite (1 + nf tid = 1 * 1 + nf tid) in H; [|auto].
        cutrewrite (S (nf tid) = 1 * 1 + nf tid) in H; [|auto].
        rewrite_sep_r_in skip_arr_unfold' H; (omega || auto).
        find_enough_resource (ARR + Z.of_nat (0 * 1 + (nf tid)))%exp H.
        rewrite_sep_r_in skip_arr_unfold' H; (omega || auto).
        rewrite HP5 in HP6.
        assert (pure (fc' 0 = sum_of 0 (2 * ntrd) f) s emp_ph) by
            (unfold fc'; rewrite HP5; unfold_conn_all; simpl in *; omega).
        clear HP HP0 HP6 H0 H1.
        Hint Resolve emp_emp_ph.
        assert (pure (x = 1%Z) s emp_ph) by (unfold_conn; rewrite HP5 in HP4; auto).
        assert (pure (st = 1) s emp_ph) by (unfold_conn;  auto).
        sep_combine_in H.
        sep_normal_in H. ex_intro fc' H. simpl in H.
        apply H. } Unfocus.
        
      forward_barr.
      Focus 2.
      { simpl; rewrite MyVector.init_spec. 
        clear fc'.
        intros s h [fc' H]; sep_normal_in H; sep_split_in H.
        (* unfold_conn_in (HP4, HP5); simpl in *; subst; simpl in *. *)
        apply ex_lift_l; exists 0; apply ex_lift_l; exists fc'.
        simpl in *. do 2 (sep_normal; sep_split).
        - unfold_conn_in HP5; simpl in HP5; rewrite HP5 in HP3; apply HP3.
        - exact HP4.
        - simpl; rewrite nth_overflow; [sep_normal | rewrite distribute_length; omega].
          sep_combine_in H. 
          ex_intro fc' H.
          exact H. } Unfocus.

      intros s h H; unfold INV; clear fc'.
      Lemma ex_lift_r_in (T : Type) (P : assn) (Q : T -> assn) :
        (P ** Ex x, Q x) |= (Ex x : T, P ** Q x).
      Proof.
        unfold_conn. intros ? ? (? & ? & ? & [? ?] & ? & ?).
        repeat eexists; eauto.
      Qed.
      Lemma ex_lift_l_in (T : Type) (P : T -> assn) (Q : assn) :
        ((Ex x, P x) ** Q) |= (Ex x : T, P x ** Q).
      Proof.
        unfold_conn. intros ? ? (? & ? & [? ?] & ? & ? & ?).
        repeat eexists; eauto.
      Qed.
      apply ex_lift_r_in in H; destruct H as (? & H).
      apply ex_lift_l_in in H; destruct H as (s0 & H).
      apply ex_lift_l_in in H; destruct H as (fc' & H).
      sep_split_in H; sep_normal_in H; sep_split_in H.
      exists 0, 0, x0; simpl in *. 
      assert (s0 = 0) by (unfold_conn_all; subst; simpl in *; omega); subst.
      sep_split; try now unfold_conn; (auto || omega).
      * rewrite nth_overflow in H; [sep_normal | rewrite distribute_length; omega].
        sep_normal_in H. exact H.
    + eapply Hbackward. Focus 2.
      { intros s h H; sep_split_in H.
        assert ((T1 + T2 === (fc (nf (tid)) + fc (st + nf tid)%nat)%Z) s emp_ph) by
            (unfold_conn_all; simpl in *; omega).
        fold (2 ^ S (S e) / 2) in *.
        assert (Hst : st = 2 ^ (S (S e)) / 2) by (unfold_conn_in HP6; auto).
        cutrewrite (2 ^ (S (S e)) = 2 ^ (S e) * 2) in Hst; [|simpl; omega].
        rewrite Nat.div_mul in Hst; auto.
        rewrite_sep_in mps_eq2 H; [|exact H0].
        Hint Resolve Nat.pow_nonzero.
        assert (nf tid < st)
          by (unfold_conn_all; simpl in *; destruct (Z_lt_dec (s TID) x); (congruence||omega)).
        rewrite_sep_in (@nth_dist_change (nat_of_fin tid) ARR fc fc') H;
          try now (subst; auto || unfold_conn_all; simpl in *; omega).
        2 : rewrite <-!plus_n_O; intros; unfold fc'; destruct lt_dec; auto; omega.
        cutrewrite (st + (st + 0) = 2 * st) in H; [|omega].
        assert (((ARR + TID)%exp + x === ARR + Z.of_nat (1 * st + nf tid)) s emp_ph).
        { unfold_conn_all; simpl; rewrite !Nat2Z.inj_add, Z.add_0_r; simpl in*; omega. }
        rewrite_sep_in (@mps_eq1 ((ARR + TID)%exp + x)) H; [|exact H2].
        cutrewrite (fc (nf tid) + fc (st + nf tid)%nat = fc' (0 * st + nf tid)%nat)%Z in H; [|].
        2: unfold fc'; destruct lt_dec; unfold_conn_all; simpl in *; [f_equal; f_equal; omega| omega].
        cutrewrite (fc (st + nf tid)%nat = fc' (1 * st + nf tid)%nat)%Z in H; [|].
        2: unfold fc'; destruct lt_dec; unfold_conn_all; simpl in *; [omega|f_equal; omega].
        rewrite_sep_r_in skip_arr_unfold' H; (omega || auto).
        2: unfold_conn_in HP8; omega.
        assert (((ARR + TID)%exp === ARR + Z.of_nat (0 * st + nf tid)) s emp_ph).
        { unfold_conn_all; simpl in *. omega. }
        rewrite_sep_in mps_eq1 H; [|exact H3].
        rewrite_sep_r_in skip_arr_unfold' H; (omega || auto).
        clear HP0 HP1 HP2 H0.
        sep_combine_in H. exact H. } Unfocus.
      forward_barr. Focus 2.
      { cutrewrite (2 ^ (S (S e)) = 2 ^ e * 2 * 2); [|simpl; omega].
        rewrite Nat.div_mul; auto.
        remember (2 ^ e * 2) as n2Se.
        simpl; rewrite MyVector.init_spec. 
        intros s h H; sep_normal_in H; sep_split_in H.
        apply ex_lift_l; exists (2 ^ e); apply ex_lift_l; exists fc'.
        do 2 (sep_normal; sep_split).
        - unfold_conn_in (HP2, HP3); simpl in HP2, HP3; rewrite HP2, HP3, Heqn2Se in HP.
          unfold_conn_in HP; simpl in HP; rewrite Zdiv2_div,Nat2Z.inj_mul,Z.div_mul in HP; auto.
          omega.
        - Lemma arr_val_compat_n0 len g sum : len <> 0 ->
            (arr_val_compat len g sum <-> sum_of 0 len g = sum).
          Proof.
            destruct len; simpl; split; auto; omega.
          Qed.
          assert (2 ^ e <> 0) by (apply Nat.pow_nonzero; auto).
          unfold_conn; unfold_conn_in (HP3, HP4); apply arr_val_compat_n0; [omega|].
          apply arr_val_compat_n0 in HP4; [|omega].
          unfold fc'; rewrite HP3, Heqn2Se, <-plus_n_O in *.
          cutrewrite (2 ^ e + 2 ^ e = 2 ^ e * 2); [|omega].
          cutrewrite (2 ^ e * 2 + 2 ^ e * 2 = 2 ^ e * 2 * 2) in HP4; [|omega].
          rewrite <-HP4; unfold fc'; symmetry;  apply shift_arr0.
        - unfold_conn_in HP3; rewrite HP3, Heqn2Se, mult_comm in H.
          simpl in H.
          assert (pure (st = 2 ^ e * 2) s emp_ph) by (unfold_conn; congruence).
          clear HP1 HP6 HP7.
          sep_combine_in H.
          sep_cancel. exact H. } Unfocus.
      intros s h H; unfold INV; clear fc'.
      apply ex_lift_l_in in H; destruct H as (s0 & H).
      apply ex_lift_l_in in H; destruct H as (fc' & H); sep_split_in H.
      exists (2 ^ e), (S e), fc'.
      assert ((St === Z.of_nat (2 ^ e)) s emp_ph).
      { unfold_conn_all; simpl in *; rewrite Zdiv2_div, HP1, HP4 in HP.
        rewrite Nat2Z.inj_mul,Z.div_mul in HP; auto; omega. }
      assert (s0 = 2 ^ e).
        { unfold_conn_in (HP5, H0); rewrite HP5 in H0; simpl in H0.
          apply Nat2Z.inj in H0; auto. }
      sep_split; try now (unfold_conn_all; (auto || omega)).
      * cutrewrite (2 ^ S e = 2 ^e * 2); [|simpl; omega].
        rewrite Nat.div_mul; unfold_conn; auto.
      * rewrite H1 in HP6; simpl; auto.
      * assert (2 ^ e <> 0) by (apply Nat.pow_nonzero; omega).
        destruct Nat.eq_dec; try omega.
        rewrite <- H1; apply H.
  - eapply Hbackward.
    Focus 2.
    { intros s h H.
      sep_normal_in H; sep_split_in H.
      assert (st <= nf tid).
      { unfold_conn_all; simpl in *.
        destruct (Z_lt_dec (s TID)); simpl in *; try (congruence || omega). }
      assert (0 < st).
      { unfold_conn_all; simpl in *.
        destruct (Z_lt_dec); simpl; try (congruence || omega). }
      assert (emp s h).
      { destruct (Nat.eq_dec st 0); subst; simpl in H; [omega|].
        rewrite nth_overflow in H; [|rewrite distribute_length]; auto. }
      clear H.
      assert (pure (st <= nf tid) s emp_ph) by (unfold_conn; auto).
      sep_combine_in H2; sep_normal_in H2; exact H2. } Unfocus.
    eapply rule_seq; [hoare_forward|].
    { intros s h [v H].
      subA_normalize_in H. simpl in H. ex_intro v H. exact H. }
    forward_barr.
    Focus 2.
    { intros s h [s0 H]; simpl; rewrite MyVector.init_spec.
      fold (2 ^ e / 2) in H.
      sep_normal_in H; sep_split_in H.
      apply ex_lift_l; exists (st / 2).
      set (fc' := fun i => if lt_dec i st then (fc i + fc (i + st)%nat)%Z else fc i).
      apply ex_lift_l; exists fc'.
      do 2 (sep_normal; sep_split).
      - rewrite div_Zdiv; auto; simpl.
        unfold_conn_all; simpl in *; destruct H. 
        rewrite Zdiv2_div in H0; simpl in H0. congruence. 
      - unfold_conn; unfold_conn_in (HP0, HP3); simpl in HP0; destruct Z_lt_dec; try congruence.
        assert (0 < st).
        { unfold_conn_all; simpl in *; destruct st; simpl in *; omega. }
        destruct e as [|[|e]]; unfold_conn_in HP2; [simpl in HP2; try omega|..].
        + simpl in *; unfold fc'; rewrite HP2 in *; simpl in *; omega.
        + cutrewrite (2 ^ (S (S e)) = 2 * (2 * 2 ^ e)) in HP2; [|auto].
          cutrewrite (2 * (2 * 2 ^ e) = 2 ^ e * 2 * 2) in HP2; [|omega].
          rewrite Nat.div_mul in HP2; auto; rewrite HP2, Nat.div_mul; auto; rewrite <-plus_n_O in *.
          assert (2 ^ e <> 0) by (apply Nat.pow_nonzero; auto).
          apply arr_val_compat_n0; try omega.
          apply arr_val_compat_n0 in HP3; [|omega].
          rewrite <-HP3; symmetry; cutrewrite (st + st = st * 2); [|omega].
          cutrewrite (2 ^ e + 2 ^ e = st); [|omega].
          unfold fc'; apply shift_arr0.
      - rewrite <-plus_n_O.
        assert (2 * (st / 2) <= st) by (apply Nat.mul_div_le; auto).
        assert (st / 2 + st / 2 <= st) by omega.
        rewrite nth_overflow; [|rewrite distribute_length; unfold_conn_all; omega].
        sep_normal.
        sep_combine_in H. ex_intro s0 H. exact H. } Unfocus.
    instantiate (1 := INV (nf tid)); unfold INV; intros; apply ex_lift_l_in in H; destruct H as [s0 H].
    apply ex_lift_l_in in H; destruct H as [fc' H].
    apply ex_lift_r_in in H; destruct H as [v H]; sep_split_in H.
    destruct e.
    { simpl in HP3; unfold_conn_in HP3; subst.
      unfold_conn_in HP2; simpl in HP2; rewrite HP2 in HP1; simpl in HP1.
      unfold_conn_in HP1; simpl in HP1; congruence. }
    cutrewrite (2 ^ S e = 2 * 2 ^ e) in HP3; [|auto].
    cutrewrite (2 * 2  ^ e = 2 ^ e * 2) in HP3; [|omega].
    rewrite Nat.div_mul in HP3; unfold_conn_in HP3; auto.
    assert (s0 = st / 2).
    { unfold_conn_all. simpl in HP8, HP2, HP.
      rewrite HP, HP2, Zdiv2_div in HP8.
      apply Nat2Z.inj; rewrite div_Zdiv; auto. }
    exists s0, e, fc'.
    sep_split; try now (unfold_conn_all; simpl in *; auto).
    + rewrite H0, HP3; unfold_conn; auto.
    + unfold_conn; unfold_conn_in HP5.
      rewrite H0.
      assert (st <> 0) by (rewrite HP3; apply Nat.pow_nonzero; auto).
      assert (st / 2 < st) by (apply Nat.div_lt; omega); omega.
    + unfold_conn_in HP7.
      assert (s0 < st).
      { rewrite H0. apply Nat.div_lt; auto.
        cut (st <> 0); [omega|].
        rewrite HP3. apply Nat.pow_nonzero; auto. }
      rewrite nth_overflow in H; [|rewrite distribute_length; omega].
      rewrite nth_overflow; [|rewrite distribute_length; omega]; auto.
      rewrite nth_overflow; [|rewrite distribute_length; omega]; auto.
      destruct Nat.eq_dec; auto.
  - intros s h [|]; auto.
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
Qed.