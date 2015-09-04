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
Instance app_proper (s : stack) (h : pheap) : Proper (equiv_sep ==> iff) (fun P => P s h).
Proof.
  intros P Q H.
  specialize (H s h); auto.
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
  end; rewrite lem in H; cbv beta in H. 

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

Theorem fold_ker_correct (tid : Fin.t ntrd) : 
  CSL (fun i => match i with O => binv0 | _ => default ntrd end) tid
  (nth (nat_of_fin tid) (distribute ntrd ARR (2 * ntrd) f (nt_step ntrd) 0) emp **
   !(TID === Z_of_fin tid))
  (fold_ker (nat_of_fin tid))
  (Ex fc,
     nth (nat_of_fin tid) (distribute ntrd ARR (2 * ntrd) f (nt_step 1) 0) emp **
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

  eapply Hbackward.
  Focus 2.
  { unfold INV; intros s h H.
    sep_split_in H; destruct H as (st & e & fc & H).
    sep_combine_in H.
    ex_intro st H; ex_intro e H; ex_intro fc H; simpl in H.    
    exact H. } Unfocus.
  
  apply rule_ex; intros fc.
  apply rule_ex; intros e.
  apply rule_ex; intros st.
  
  eapply rule_seq.

  eapply rule_if_disj.
  { eapply Hbackward.
    Focus 2.
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
    
    eapply rule_seq.
    { repeat hoare_forward. 
      apply inde_distribute; repeat (constructor; auto).
      intros ? ? H; exact H. }
    
    eapply rule_seq.
    { cutrewrite (Z.of_nat (st + nat_of_fin tid) = Z.of_nat st + Z.of_nat (nat_of_fin tid))%Z; [|apply Nat2Z.inj_add].
      hoare_forward. 
      apply inde_distribute; repeat (constructor; auto).
      intros ? ? H; exact H. }
    
    { hoare_forward.
      intros ? ? H; exact H. } }
  
  apply rule_skip.

  eapply Hforward.
  eapply rule_disj.
  - eapply rule_seq; [hoare_forward|].
    { intros s h H.
      destruct H as [st' H].
      subA_normalize_in H. simpl in H.
      ex_intro st' H; exact H. }

    hoare_forward.
    set (fc' := fun i => if lt_dec i st then (fc i + fc (i + st)%nat)%Z else fc i).
    destruct e as [|[|e]].
    Ltac forward_barr := lazymatch goal with
      | [ |- CSL ?bspec ?tid ?P (Cbarrier ?i) ?Q] =>
        eapply Hbackward; [
            eapply Hforward; [
              eapply rule_frame; 
              [eapply rule_barrier | prove_inde] |
              autounfold; simpl; repeat rewrite MyVector.init_spec in *] | ] end.
    + forward_barr. Focus 2.
       { simpl; rewrite MyVector.init_spec.
         intros s h H; sep_normal_in H; sep_split_in H.
         unfold_conn_in (HP3, HP4, HP5); simpl in HP3, HP4, HP5.
         assert (FalseP s h) by (subst; simpl in HP3; congruence). 
         instantiate (1 := FalseP); destruct H0. } Unfocus.
       intros; unfold_conn; repeat destruct H; tauto.
    + forward_barr. Focus 2.
      { simpl; rewrite MyVector.init_spec. 
        intros s h H; sep_normal_in H; sep_split_in H.
        unfold_conn_in (HP4, HP5); simpl in *; subst; simpl in *.
        apply ex_lift_l; exists 0; apply ex_lift_l; exists fc'.
        repeat (sep_normal; sep_split).
        - unfold_conn_in HP8; unfold_conn; simpl; auto.
        - unfold_conn; simpl; rewrite <-plus_n_O in *.
          unfold fc'; simpl; unfold_conn_in HP6; omega.
        - simpl; rewrite nth_overflow; [sep_normal | rewrite distribute_length; omega].
          apply (sep_rewrite_var HP) in H; subA_normalize_in H. simpl in H.
          apply (sep_rewrite_var HP0) in H; subA_normalize_in H. simpl in H.
          apply (sep_rewrite_var HP2) in H; subA_normalize_in H. simpl in H.
          assert (nf tid = 0).
          { unfold_conn_in (HP2, HP1); simpl in HP1, HP2.
            destruct Z_lt_dec; try congruence; omega. } 
          rewrite_sep_in (@nth_dist_change (nat_of_fin tid) ARR fc fc') H; try (auto || omega).
          Focus 2.
          { unfold fc'; intros j Hj _.
            destruct lt_dec; try omega. } Unfocus.
          
          Lemma mapsto_equiv1 (E1 E2 E3 : exp) (p : Qc) (s : stack) (h : pheap) :
            (E1 === E2) s emp_ph -> (E1 -->p (p,  E3)) s h -> (E2 -->p (p,  E3)) s h.
          Proof.
          
  
          cutrewrite (fc (S (nf tid)) = fc' (S (nf tid))) in H.

          Ltac rewrite_sep_r_in lem H :=
            match type of H with
              | ?X _ _ => pattern X in H
            end; rewrite <-lem in H; cbv beta in H.
          Hint Resolve Nat2Z.inj_add : zarith.
          assert (s ARR + Z.of_nat (1 + (nf tid)) = s ARR + Z.of_nat (nf tid) + 1%Z)%Z by
              (rewrite Nat2Z.inj_add; cutrewrite (Z.of_nat 1 = 1%Z); [omega|auto]). 
          find_enough_resource (ARR + Z.of_nat (1 + (nf tid)))%exp H.
          sep_lift_in H 1.


          rewrite_sep_r_in skip_arr_unfold' H.

            
  find_enough_resource (ARR + TID + Enum' st)%exp H.
  sep_lift_in H 1.

  set (fc' := fun i => if lt_dec i st then (fc i + fc (i + st)%nat)%Z else fc i).

  Lemma ex_lift_l {T : Type} (P : T -> assn) (Q : assn) :
    (Ex x, P x ** Q) |= (Ex x, P x) ** Q.
  Proof.
    intros; unfold_conn; destruct H as (x & H & ? & ? & ? & ? & ?).
    repeat eexists; eauto.
  Qed.

  apply ex_lift_l; exists (st / 2); apply ex_lift_l; exists fc'.
  sep_normal; sep_split.
  { unfold_conn_in (HP8, HP4); simpl in HP8, HP4; unfold_conn; simpl.
    rewrite HP8, HP4, Zdiv2_div; fold (st / 2); rewrite div_Zdiv; auto. }
  sep_normal; sep_split.
  { unfold_conn.
    unfold_conn_in (HP3, HP4, HP5, HP6); simpl in HP3, HP4, HP5, HP6.
    fold (2 ^ e / 2) in HP5; destruct e as [| [|e]]; rewrite HP5 in HP4; rewrite HP4 in HP3.
    - simpl in HP3; congruence.
    - rewrite HP5; rewrite HP5 in HP6; simpl in HP3, HP6; simpl.
      unfold fc'; rewrite HP5; simpl; rewrite Z.add_0_r in HP6; auto. 
    - unfold fc'; rewrite HP5; rewrite HP5 in HP6;
      assert (Heq : 2 ^ S (S e) = 2 ^ e * 2 * 2) by (simpl; omega).
      rewrite Heq; rewrite Heq in HP6; repeat (rewrite Nat.div_mul in *; auto; rewrite <-plus_n_O in *); clear Heq.
      cutrewrite (2 ^ e * 2 + 2 ^ e * 2 = 2 * (2 ^ e + 2 ^ e)) in HP6; [|omega].
      assert (2 ^ e + 2 ^ e <> 0); [pose proof (Nat.pow_nonzero 2 e); omega|].
      unfold arr_val_compat; destruct (2 ^ e + 2 ^ e) eqn:Heq; [omega|rewrite <-Heq].
      cutrewrite (2 ^ e + 2 ^e = 2 ^ e * 2); [|omega]; rewrite <-shift_arr0.
      cutrewrite (2 ^e * 2 * 2 = 2 * S n0); [|omega].
      simpl in HP6; auto. }

  assert ((nth (nf tid)
               (distribute (st / 2 + (st / 2 + 0)) ARR (ntrd + (ntrd + 0)) fc'
                           (nt_step (st / 2 + (st / 2 + 0))) 0) emp) s h).
  { 
    
  Focus 2.
  intros s0 h0 Hp.
  






  assert (Heq : (fc (nf tid) + fc (st + nf tid) === Enum (fc (nf tid) + fc (st + (nf tid)))) s emp_ph).
  unfold eeq; simpl; auto.
  eapply scRw_stack in H; [|intros ? Ht; apply (mapsto_rewrite2 Heq) in Ht; exact Ht |intros ? Ht; exact Ht ].
  cutrewrite (fc (nf tid) + fc (st + (nf tid))%nat = fc' (nf tid))%Z in H;
    [|unfold fc'; destruct lt_dec;
      [auto|
       unfold_conn_all;simpl in *; repeat destruct Z_lt_dec;
       (congruence || omega)]].
  cutrewrite (fc (st + nf tid)%nat = fc' (st + nf tid)%nat)%Z in H;
    [|unfold fc'; destruct lt_dec; auto || omega].
  cutrewrite (ntrd + (ntrd + 0) = 2 * ntrd) in H; [|omega].
  cutrewrite (st + (st + 0) = st + st) in H; [|omega].


  eapply scRw; [|intros ? ? Hf; exact Hf |].
  intros ? ? Hf.
  exists (st / 2), fc'.
  exact Hf.
  sep_normal; sep_split.
  { rewrite div_Zdiv; auto.
    unfold_conn_all; simpl in *;rewrite Zdiv2_div in HP8; rewrite <-HP4; auto. }
  { sep_normal. sep_split.
    unfold_conn_all; simpl in *; unfold arr_val_compat.
    destruct (ntrd + (ntrd + 0)) as [|ntrd2] eqn:Hntrd; [omega|]; rewrite <-Hntrd.
    fold (2 ^ e / 2) in HP5.
    unfold bexp_to_assn in HP3; simpl in HP3; destruct (Z_lt_dec); [|congruence].
    destruct e as [| [|e]]; [simpl in HP5..|]; try omega .
    + unfold fc'; rewrite HP5 in *; simpl; simpl in HP6.
      ring_simplify in HP6; rewrite Hntrd; simpl; auto.
    + cutrewrite (2 ^ S (S e) / 2 = 2 * (2 * 2 ^ e) / 2) in HP5; [|f_equal; simpl; omega].
      rewrite mult_comm, Nat.div_mul in HP5; auto.
      fold (st / 2); rewrite HP5; rewrite mult_comm, Nat.div_mul; auto.
      destruct (2 ^ e) as [|e2] eqn:H2e; [destruct e; simpl in H2e; omega|].
      simpl.
      cutrewrite (ntrd + (ntrd + 0) = 2 * ntrd); [|omega].
      cutrewrite (fc' 0%nat + sum_of 1 (e2 + S (e2 + 0)) fc' = sum_of 0 (2 * S e2) fc')%Z; [|simpl; auto].
      repeat rewrite (mult_comm 2); unfold fc'. 
      rewrite mult_comm, <-HP5.
      rewrite <-shift_arr0.
      rewrite HP5 in HP6; simpl in HP6.
      rewrite <-!plus_n_O in HP6.
      cutrewrite (e2 + S e2 + S (e2 + S e2) = S (S (S (4 * e2))) ) in HP6; [|omega].
      cutrewrite (fc 0%nat + sum_of 1 (S (S (S (4 * e2)))) fc = sum_of 0 (S (S (S (S (4 * e2))))) fc)%Z
                 in HP6; [|auto].
      cutrewrite (S (S (S (S (4 * e2)))) = (2 * (S e2)) * 2) in HP6; [|omega].
      rewrite <-HP5 in HP6.
      cutrewrite (f 0 + sum_of 1 ntrd2 f = sum_of 0 (S ntrd2) f)%Z in HP6; [|auto].
      rewrite <-Hntrd in HP6; cutrewrite (ntrd + (ntrd + 0) = ntrd * 2) in HP6; [auto|omega].
    + Ltac rewrite_sep lem :=
      match goal with
        | [|- ?X _ _] => pattern X 
      end; rewrite lem; cbv beta. 
      repeat rewrite <-plus_n_O.
      assert (Heq' : 0 = 0 * (st / 2 + st / 2)) by auto; rewrite Heq' at 5; clear Heq'.
      eapply scRw; [intros ? ? H'| |].
      fold (2 ^ e / 2) in HP5.
      unfold_conn_in HP3; simpl in HP3; destruct Z_lt_dec; [|congruence].
      destruct e as [| [|e]]; [unfold_conn_in (HP4, HP5); simpl in HP4, HP5..|].
      * rewrite HP4, HP5 in l; simpl in l; omega.
      * rewrite HP5; simpl.
        rewrite nth_overflow; [|rewrite distribute_length; omega ].
        exact H'.
      *
      rewrite_sep (@skip_arr_unfold' (nf tid) ARR fc' (ntrd + ntrd) (st / 2 + st / 2)); auto.
      
      