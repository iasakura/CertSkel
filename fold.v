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
  Fix lt_wf (fun _ => nat -> Z) (skip_sum_body f skip Hskip) len s.

Example two_neq_0 : 2 <> 0. now auto. Qed.
Eval compute in skip_sum 2 two_neq_0 10 0 (fun i => Z.of_nat i).

Lemma Fix_eq_ok f skip (Hskip : skip <> 0) :
  forall (len : nat) (F G : forall len' : nat, len' < len -> nat -> Z),
  (forall (len' : nat) (p : len' < len), F len' p = G len' p) ->
  skip_sum_body f skip Hskip len F = skip_sum_body f skip Hskip len G.
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

Definition INV :=
  Ex (i s e : nat) (fc : nat -> Z),
    !(TID === Enum' i) **
    !(St === Enum' s) **
    !(pure (s = Div2.div2 (2 ^ e))) **
    !(pure (arr_val_compat (2 * s) fc (sum_of 0 (2 * ntrd) f))) **
    !(pure (s <= ntrd)) **
    (if Nat.eq_dec s 0 then
       nth i (distribute 1 ARR (2 * ntrd) fc (nt_step 1) 0) emp
     else
       nth i (distribute s ARR (2 * ntrd) fc (nt_step s) 0) emp).

Definition fold_ker :=
  St ::= Enum' ntrd ;;
  WhileI (INV) ( Enum' 0 < St ) (
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
     !(pure (arr_val_compat (2 * ntrd) fc (sum_of 0 (2 * ntrd) f))) **
       let tid := nat_of_fin i in
       nth tid (distribute (2 * s) ARR (2 * ntrd) fc (nt_step (2 * s)) 0) emp),
   MyVector.init (fun i => 
   let tid := nat_of_fin i in
   Ex s fc, 
     !(St === Enum' s) **
     !(pure (arr_val_compat (2 * ntrd) fc (sum_of 0 (2 * ntrd) f))) **
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
   sum_of s (len * 2) fc = sum_of s len (fun i => if lt_dec i (s + len) then fc i + fc (i + len)%nat else f i)%Z.
Proof.
  cutrewrite (len * 2 = len + len); [|omega].
  intros s; rewrite sum_of_concat.
  rewrite (plus_comm len s), shift_values.
  apply sum_of_eq; intros; destruct lt_dec; omega.
Qed.

Corollary shift_arr0 (len : nat) (fc : nat -> Z) : 
  sum_of 0 (len * 2) fc = sum_of 0 len (fun i => if lt_dec i len then fc i + fc (i + len)%nat else f i)%Z.
Proof.
  apply shift_arr.
Qed.
  
Theorem fold_ker_correct (tid : Fin.t ntrd) : 
  CSL (fun i => match i with O => binv0 | _ => default ntrd end) tid
  (nth (nat_of_fin tid) (distribute ntrd ARR (2 * ntrd) f (nt_step ntrd) 0) emp **
   !(TID === Z_of_fin tid))
  fold_ker
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
    exists (nat_of_fin tid), (ntrd), (S e), f.
    sep_split_in H; sep_split; auto.
    - rewrite Nat.pow_succ_r', Div2.div2_double; unfold_conn; auto.
    - apply arr_compat_same; omega.
    - red; auto.
    - destruct (Nat.eq_dec _ _); [omega | congruence]. } Unfocus.

  eapply Hbackward.
  Focus 2.
  { unfold INV; intros s h H.
    sep_split_in H; destruct H as (i & st & e & fc & H).
    sep_combine_in H.
    ex_intro i H; ex_intro st H; ex_intro e H; ex_intro fc H; simpl in H.    
    exact H. } Unfocus.
  
  apply rule_ex; intros fc.
  apply rule_ex; intros e.
  apply rule_ex; intros st.
  apply rule_ex; intros i.
  
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
    { cutrewrite (Z.of_nat (st + i) = Z.of_nat st + Z.of_nat i)%Z; [|apply Nat2Z.inj_add].
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
    lazymatch goal with
    | [ |- CSL ?bspec ?tid ?P (Cbarrier ?i) ?Q] =>
    eapply Hbackward; [
        eapply Hforward; [
          eapply rule_frame; 
          [eapply rule_barrier | prove_inde] |
           autounfold; simpl; repeat rewrite MyVector.init_spec in *] | 
        (*frame_analysis (Vector.nth (fst (bspec i)) tid)*)] end.
  Focus 2.
  simpl; rewrite MyVector.init_spec.
  intros s h H.
  sep_normal_in H; sep_split_in H.

    