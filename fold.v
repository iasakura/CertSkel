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
Notation OUT := (Var 8).

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
Notation f_ss' bid := (fun i => f_ss (i + bid * ntrd)). 

Definition INV2 i b arr out :=
  Ex (s e : nat) fc,
    !(ARR === arr) **
    !(OUT === out) **
    !(TID === Enum' i) **
    !(BID === Enum' b) **
    !(St === Enum' s) **
    !(pure (s = (2 ^ e / 2))) **
    !(pure (if lt_dec i (ceil2 s) then
              fc i = skip_sum (dbl s) 0 ntrd (f_ss' b) i /\
              fc (i + s) = skip_sum (dbl s) 0 ntrd (f_ss' b) (i + s)
            else True)) **
    !(pure (s <= ntrd / 2)) **
    (if Nat.eq_dec s 0 then
       nth i (distribute 1 (Sh SARR) ntrd fc (nt_step 1) 0) emp
     else
       nth i (distribute s (Sh SARR) ntrd fc (nt_step s) 0) emp).

Definition INV1 i b arr out :=
  Ex (ix : nat) (v : Z),
    !(ARR === arr) **
    !(OUT === out) **
    !(TID === Enum' i) **
    !(BID === Enum' b) **
    !(I === Enum' (ix * nt_gr + (i + b * ntrd))) **
    !(Apure (ix * nt_gr + (i + b * ntrd) < len + nt_gr)%nat) **
    !(T2 === skip_sum nt_gr 0 (ix * nt_gr) f (i + b * ntrd)) **
    skip_arr (Gl arr) 0 len nt_gr f (i + b * ntrd) **
    (Sh SARR +o Enum' i -->p (1%Qc, v)).

Open Scope bexp_scope.

Close Scope bexp_scope.
Definition fold_ker (i b : nat) (arr out : val) := (
  I ::= (TID +C BID *C Z.of_nat ntrd) ;;
  T2 ::= [ Gl ARR +o I ] ;;
  I ::= I +C Z.of_nat ntrd *C Z.of_nat nblk ;;
  WhileI (INV1 i b arr out) ( I <C Z.of_nat len ) (
    T1 ::= [ Gl ARR +o I ] ;;
    T2 ::= T1 +C T2 ;;
    I ::= Z.of_nat ntrd *C Z.of_nat nblk + I
  )%exp;;
  [ Sh SARR +o TID ] ::= T2 ;;
  Cbarrier 0;;
  St ::= Enum' ntrd >>1;;
  WhileI (INV2 i b arr out) ( Enum' 0 < St ) (
    If ( Evar TID <C St ) (
      T1 ::= [ Sh SARR +o TID ] ;;
      T2 ::= [ Sh SARR +o (TID + St) ] ;;
      [ Sh SARR +o TID ] ::= T1 + T2
    ) (SKIP) ;;
    St ::= St >>1 ;;
    Cbarrier 1
  );;
  If (TID == 0%Z) (
    T1 ::= [ Sh SARR +o 0%Z] ;;
    [ Gl OUT +o BID ] ::= T1
  ) SKIP)%exp.

Definition fold_ker' : cmd := fold_ker 0 0 0%Z 0%Z.

Definition binv0 (bid : Fin.t nblk) : Vector.t assn ntrd * Vector.t assn ntrd :=
  (MyVector.init (fun i : Fin.t ntrd =>
   let tid := nf i in 
   (Sh SARR +o Zn tid -->p (1%Qc, f_ss (tid + nf bid * ntrd)))),
   MyVector.init (fun i : Fin.t ntrd =>
   let tid := nf i in
   nth tid (distribute (ceil2 (ntrd /2)) (Sh SARR) ntrd (f_ss' (nf bid)) (nt_step (ceil2 (ntrd / 2))) 0) emp)).
   
Definition binv1 (b : Fin.t nblk) : Vector.t assn ntrd * Vector.t assn ntrd :=
  (MyVector.init (fun i : Fin.t ntrd =>
   let tid := nat_of_fin i in
   Ex s e fc,
     !(St === Enum' s) **
     !(pure (s = (2 ^ e / 2))) **
     let tid := nat_of_fin i in
     !(pure (if lt_dec tid (dbl s) then fc tid = skip_sum (dbl s) 0 ntrd (f_ss' (nf b)) tid else True)) **
     nth tid (distribute (dbl s) (Sh SARR) ntrd fc (nt_step (dbl s)) 0) emp **
     !(pure (s <= ntrd / 2)) **
     !(BID === Enum' (nf b))),
   MyVector.init (fun i => 
   let tid := nat_of_fin i in
   Ex s e fc, 
     !(St === Enum' s) **
     !(pure (s = (2 ^ e / 2))) **
     let tid := nat_of_fin i in
     !(pure (if lt_dec tid (ceil2 s) then
               fc tid = skip_sum (dbl s) 0 ntrd (f_ss' (nf b))  tid /\
               fc (tid + s) = skip_sum (dbl s) 0 ntrd (f_ss' (nf b)) (tid + s)
             else True)) **
     nth tid (distribute (ceil2 s) (Sh SARR) ntrd fc (nt_step (ceil2 s)) 0) emp **
     !(pure (s <= ntrd / 2)) **
     !(BID === Enum' (nf b)))).

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

Lemma rule_frame' (ntrd' : nat) (bspec : nat -> Vector.t assn ntrd' * Vector.t assn ntrd')
      (tid : Fin.t ntrd') (C : cmd) (P Q R : assn) :
  CSL bspec tid P C Q ->
  inde R (writes_var C) -> CSL bspec tid (R ** P) C (R ** Q).
Proof.
  intros.
  eapply Hbackward; [eapply Hforward|].
  apply rule_frame.
  apply H.
  apply H0.
  intros; repeat sep_cancel.
  intros; repeat sep_cancel.
Qed.

Definition binv bid i :=
  if Nat.eq_dec i 0 then binv0 bid else if Nat.eq_dec i 1 then binv1 bid else default ntrd.


Lemma skip_sum_app sk ix (f' : nat -> Z) i : 
  sk <> 0 -> i < sk -> forall st,
  skip_sum sk (st * sk) (sk + ix * sk) f' i =
  (f' (i + ix * sk + st * sk)%nat + skip_sum sk (st * sk) (ix * sk) f' i)%Z.
Proof.
  intros Hsk Hisk; induction ix; simpl; intros st.
  - rewrite <-!plus_n_O, Z.add_0_r.
    rewrite skip_sum_unfold; eauto.
    rewrite minus_diag; simpl; omega.
  - rewrite skip_sum_unfold; try nia.
    rewrite (skip_sum_unfold (len := sk + ix * sk)); try nia.
    cutrewrite (sk + (sk + ix * sk) - sk = sk + ix * sk); [|nia].
    rewrite IHix.
    ring_simplify.
    cutrewrite (i + (sk + ix * sk) + st * sk = i + ix * sk + S st * sk); [|nia].
    cutrewrite (sk + ix * sk - sk = ix * sk); [|nia]; eauto.
Qed.

Lemma skip_sum_app0 sk ix f' i :
  sk <> 0 -> i < sk ->
  skip_sum sk 0 (sk + ix * sk) f' i =
  (f' (i + ix * sk)%nat + skip_sum sk 0 (ix * sk) f' i)%Z.
Proof.
  intros; cutrewrite (0 = 0 * sk); eauto.
  rewrite skip_sum_app; try omega.
  simpl; rewrite <-plus_n_O; auto.
Qed.

Lemma skip_sum_nil' next sk len1 f1 i : forall st,
  (forall j, j < next -> (st + len1 + j) mod sk <> i) ->
  skip_sum sk st len1 f1 i =
  skip_sum sk st (len1 + next) f1 i.
Proof.
  induction len1; intros st Hst; simpl.
  - rewrite (@skip_sum_nil next).
    { rewrite minus_diag; eauto. }
    rewrite <-plus_n_O in Hst; eauto.
  - rewrite IHlen1; eauto.
    intros; cutrewrite (S st + len1 + j = st + S len1 + j); [|nia]; eauto.
Qed.
Lemma mod_lt n m a b : m <> 0 ->
  n * m <= a < b -> b < (S n) * m ->
  a mod m < b mod m.
Proof.
  intros Hm0 Ha Hb; destruct Ha.
  assert (a / m = n).
  { apply (Nat.div_le_mono _ _ m) in H; try omega.
    rewrite Nat.div_mul in H; try omega.
    assert (a < S n * m) by omega.
    rewrite mult_comm in H1; apply Nat.div_lt_upper_bound in H1; omega. }
  assert (b / m = n).
  { assert (n * m <= b) by omega.
    apply (Nat.div_le_mono _ _ m) in H2; try omega.
    rewrite Nat.div_mul in H2; try omega.
    rewrite mult_comm in Hb; apply Nat.div_lt_upper_bound in Hb; try omega. }
  rewrite (Nat.div_mod a m), (Nat.div_mod b m) in H0; try omega.
  rewrite H1, H2 in H0; omega.
Qed.
Lemma mod_le n m a b : m <> 0 ->
  n * m <= a <= b -> b < (S n) * m ->
  a mod m <= b mod m.
Proof.
  intros Hm0 Ha Hb; destruct Ha.
  assert (a / m = n).
  { apply (Nat.div_le_mono _ _ m) in H; try omega.
    rewrite Nat.div_mul in H; try omega.
    assert (a < S n * m) by omega.
    rewrite mult_comm in H1; apply Nat.div_lt_upper_bound in H1; omega. }
  assert (b / m = n).
  { assert (n * m <= b) by omega.
    apply (Nat.div_le_mono _ _ m) in H2; try omega.
    rewrite Nat.div_mul in H2; try omega.
    rewrite mult_comm in Hb; apply Nat.div_lt_upper_bound in Hb; try omega. }
  rewrite (Nat.div_mod a m), (Nat.div_mod b m) in H0; try omega.
  rewrite H1, H2 in H0; omega.
Qed.

Require Import LibTactics.

Lemma div_le a b: b <> 0 -> a / b <= a.
Proof.
  intros.
  lets: (Nat.div_le_compat_l a 1 b).
  rewrite Nat.div_1_r in H0.
  apply H0; omega.
Qed.

Theorem fold_ker_correct (tid : Fin.t ntrd) (bid : Fin.t nblk) (arr out : val) :
  nt_gr <= len ->
  CSL (binv bid) tid
  (Ex  (v1 v2 : Z),
     !(ARR === arr) **
     !(OUT === out) **
     (Sh SARR +o Z_of_fin tid -->p (1, v1)) **
     skip_arr (Gl arr) 0 len        nt_gr f  (nf tid + nf bid * ntrd) **
     (if Nat.eq_dec (nf tid) 0 then (Gl out +o Z_of_fin bid -->p (1, v2)) else emp) **
     !(TID === Z_of_fin tid) **
     !(BID === Z_of_fin bid))
  (fold_ker (nf tid) (nf bid) arr out)
  (Ex fc,
     skip_arr (Gl arr) 0 len nt_gr f (nf tid + nf bid * ntrd) **
     if Nat.eq_dec (nf tid) 0 then
       nth (nat_of_fin tid) (distribute 1 (Sh SARR) ntrd fc (nt_step 1) 0) emp **
       (Gl out +o Z_of_fin bid -->p (1, sum_of 0 ntrd (f_ss' (nf bid))))
     else emp).
Proof.
  intros Hnlen.
  unfold fold_ker, skip_arr, binv.
  pose proof (nf_lt tid) as nf_lt.
  assert (Hnt_gr : nf tid + nf bid * ntrd < nt_gr) by eauto.
  repeat hoare_forward.
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
      assert (Heq : (Gl arr +o Zn (0 * nt_gr + (nf tid + nf bid * ntrd)) ===l
                     Gl arr +o I) s (emp_ph loc)).
      { unfold_pures. unfold_conn; simpl; f_equal. nia. }
      sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
      sep_combine_in H; exact H. } Unfocus.
    hoare_forward. simpl. intros ? ? H; exact H. }

  eapply rule_seq.
  { hoare_forward. intros ? ? [v H]. subA_normalize_in H. simpl in H.
    ex_intro v H; exact H. }

  hoare_forward.
  eapply Hbackward.
  Focus 2. { intros ? ? H. sep_normal_in H. sep_lift_in H 9. exact H. } Unfocus.
  eapply rule_seq.
  apply rule_frame'.
  2: prove_inde.
  { repeat hoare_forward; unfold INV1, skip_arr.
    - { eapply Hbackward.
        Focus 2. {
        intros s h H.
        apply ex_lift_l_in in H; destruct H as [ix H].
        apply ex_lift_l_in in H; destruct H as [v H].
        sep_split_in H.
        change_in H.
        { unfold_pures.
          sep_rewrite_in (@skip_arr_nth' ix) H; [|first [now eauto | omega | nia]..].
          exact H. }
        assert (Heq : ((Gl arr +o Zn (ix * nt_gr + (nf tid + nf bid * ntrd))) ===l
                       (Gl arr +o I)) s (emp_ph loc)).
        { unfold_pures; unfold_conn; simpl; f_equal; nia. }
        sep_rewrite_in mps_eq1 H; [clear Heq|exact Heq].
        sep_combine_in H. ex_intro ix H. ex_intro v H. exact H. } Unfocus.
      repeat hoare_forward.
      eapply rule_seq.
      { hoare_forward; intros ? ? H; exact H. }
      eapply rule_seq.
      { hoare_forward; intros ? ? [v H]. subA_normalize_in H. simpl in H. ex_intro v H; exact H. }
      repeat hoare_forward. intros ? ? [v H].
      subA_normalize_in H. simpl in H.
      sep_normal_in H. sep_split_in H.
      unfold_pures. subst v.
      exists (S x3) x2.
      sep_split; eauto.
      - unfold_conn; simpl; nia.
      - unfold_conn; simpl. nia.
      - unfold_conn; simpl.
        subst. rewrite skip_sum_app0; try omega; eauto.
        cutrewrite (nf tid + nf bid * ntrd + x3 * nt_gr = x3 * nt_gr + (nf tid + nf bid * ntrd));
          [|ring].
        nia.
      - sep_rewrite (@skip_arr_nth' x3); [|first [now eauto | omega | nia]..].
        sep_normal; sep_normal_in H.
        repeat sep_cancel. }
    - intros ? ? H; exact H.
    - intros s h H; sep_normal_in H; sep_split_in H; unfold_pures. subst x1.
      exists 1 x.
      sep_split; eauto.
      + unfold_conn; simpl. nia.
      + unfold_conn; simpl. nia.
      + unfold_conn; simpl.
        rewrite <-plus_n_O.
        cutrewrite (0 = 0 * nt_gr); eauto; rewrite skip_sum_unfold; try omega; eauto.
        autorewrite with sep; eauto.
      + assert (Heq : 0 = 0 * nt_gr) by auto; rewrite Heq; clear Heq.
        sep_rewrite skip_arr_unfold'; try nia.
        simpl.
        rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
        sep_normal. repeat sep_cancel. }

  eapply rule_seq.
  { eapply Hbackward.
    Focus 2. {
    intros ? ? H.
    sep_split_in H.
    apply ex_lift_r_in in H; destruct H as [ix H].
    apply ex_lift_r_in in H; destruct H as [v H].
    sep_normal_in H.
    sep_combine_in H.
    ex_intro v H. ex_intro ix H. simpl in H. exact H. } Unfocus.
    repeat hoare_forward.
    intros ? ? H. ex_intro x2 H. exact H. }

  hoare_forward.
  eapply rule_seq.
  { forward_barr.
    intros s h H; exact H.
    intros s h H. simpl. rewrite MyVector.init_spec.
    sep_split_in H.
    assert (Heq : skip_sum nt_gr 0 (x2 * nt_gr) f (nf tid + nf bid * ntrd) =
                  f_ss (nf tid + nf bid * ntrd)).
    { unfold_pures.
      assert (len <= x2 * nt_gr + (nf tid + nf bid * ntrd)) by nia.


      assert (len < x2 * nt_gr \/ x2 * nt_gr <= len) as [Hl | Hl ] by omega.
      - rewrite (@skip_sum_nil' (x2 * nt_gr - len) _ len).
        cutrewrite (len + (x2 * nt_gr - len) = x2 * nt_gr); [|nia]; eauto.
        intros j Hj; simpl.
        assert (len <= len + j < x2 * nt_gr) by omega.
        assert ((x2 - 1) * nt_gr + (nf tid + nf bid * ntrd) < len) by nia.
        assert (len mod nt_gr <= (len + j) mod nt_gr).
        { apply (@mod_le (x2 - 1)); eauto; try omega; nia. }
        assert (((x2 - 1) * nt_gr + (nf tid + nf bid * ntrd)) mod nt_gr < len mod nt_gr).
        { apply (@mod_lt (x2 - 1)); eauto; try omega; nia. }
        rewrite plus_comm, Nat.mod_add, Nat.mod_small in H4; omega.
      - rewrite (@skip_sum_nil' (len - x2 * nt_gr) _ (x2 * nt_gr)).
        cutrewrite (x2 * nt_gr + (len - x2 * nt_gr) = len); [|omega]; auto.
        intros j Hj; simpl.
        assert (nf tid + nf bid * ntrd < nt_gr) by eauto.
        assert (len < S x2 * nt_gr) by nia.
        assert (x2 *nt_gr + j < len) by nia.
        assert ((x2 * nt_gr + j) mod nt_gr < len mod nt_gr).
        { apply (@mod_lt x2); eauto; try omega; nia. }
        assert (len mod nt_gr <= (x2 * nt_gr + (nf tid + nf bid * ntrd)) mod nt_gr).
        { apply (@mod_le x2); eauto; try omega; nia. }
        rewrite plus_comm, Nat.mod_add, (Nat.mod_small (nf tid + nf bid * ntrd)) in H5; try omega.
    }
    rewrite Heq in *.
    change_in H.
    { clear HP HP4 HP5 HP6; 
      sep_combine_in H. exact H. }
    sep_cancel. }
    
  (* introduction *)
  (* assert (Htid : nat_of_fin tid < ntrd) by (destruct (Fin.to_nat tid); simpl in *; try omega). *)
  (* remember (ntrd * 2) eqn:Hntrd2. *)

  (* exec the 1st command *)
  eapply rule_seq.
  { hoare_forward.
    simpl; intros ? ? [v H].
    eapply scRw in H; [|intros ? ? H'; subA_normalize_in H'; exact H' | intros ? ? H'; exact H'].
    simpl in H; exact H. }

  (* frame out irrelevant resources *)
  eapply rule_seq.
  eapply Hbackward.
  Focus 2. {
    intros ? ? H. sep_normal_in H.
    sep_lift_in H 5.
    exact H.
  } Unfocus.
  apply rule_frame'.
  2: prove_inde.

  eapply Hbackward.
  Focus 2. {
    intros ? ? H. sep_normal_in H.
    sep_lift_in H 5.
    exact H.
  } Unfocus.
  apply rule_frame'.
  2: prove_inde.  

  (* the loop invariant holds before the loop *)
  hoare_forward.
  Focus 3.
  { unfold INV2; intros s h H.
    destruct ntrd_is_p2 as [e Hntrd].
    exists (ntrd / 2) e (f_ss' (nf bid)).
    sep_split_in H; unfold_pures; sep_split; autorewrite with sep in *; auto.
    - unfold_conn; simpl; subst; eauto.
    - destruct (lt_dec (nf tid) (ceil2 (ntrd / 2))); [|unfold_conn; auto].
      unfold dbl in *; destruct Nat.eq_dec; try omega.
      + assert (ntrd = 1).
        { destruct ntrd as [|[|?]]; try omega.
          cutrewrite (S (S n) = n + 1 * 2) in e0; [|omega].
          rewrite Nat.div_add in e0; omega. }
        clear Hntrd; subst ntrd.
        rewrite !skip_sum1; try omega; split; eauto.
      + cutrewrite (ntrd / 2 * 2 = ntrd).
        rewrite !skip_sum1; try omega.
        split; eauto.
        unfold ceil2 in l. destruct Nat.eq_dec; try omega.
        assert (ntrd / 2 * 2 <= ntrd) by (apply div_mult; omega).
        omega.
        lets (_ & Heq): (>>Nat.div_exact ntrd 2); try omega.
        destruct e; [subst; cbv in n; omega|].
        rewrite Heq at 2; try ring.
        rewrite Hntrd.
        cutrewrite (2 ^ S e = 2 ^ e * 2); [|simpl; omega].
        rewrite Nat.mod_mul; eauto.
    - red; auto.
    - unfold ceil2 in *. destruct (Nat.eq_dec _ _); eauto. } Unfocus.

  (* make the precondition normal form *)
  eapply Hbackward.
  Focus 2.
  { unfold INV2; intros s h H.
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
    { unfold INV2; intros s h H.
      sep_split_in H.
      change_in H.
      { unfold_pures.
        destruct Nat.eq_dec; [omega|].
        cutrewrite (0 = 0 * st) in H; [|auto].
        apply skip_arr_unfold' in H; simpl; try omega; simpl in H.
        cutrewrite (st + 0 = 1 * st) in H; [|omega].
        sep_rewrite_in skip_arr_unfold' H; try first [omega].
        rewrite mult_1_l in H; exact H.
        assert (st + st <= ntrd / 2 + ntrd / 2) by omega.
        assert (ntrd / 2 + ntrd / 2 <= ntrd).
        { pose proof (@div_mult ntrd 2); omega. }
        assert (nf tid < st) by nia.
        omega. }
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
    instantiate (1 := INV2 (nf tid) (nf bid) arr out).
    set (fc' := (fun i => if Nat.eq_dec i (nf tid) then (fc i + fc (i + st)%nat)%Z else fc i)).
    destruct e as [|e].

    + (* crush the case (e=0) *)
      forward_barr. Focus 2.
      { simpl; rewrite MyVector.init_spec.
        intros s h H; sep_normal_in H; sep_split_in H.
        unfold_pures; unfold div in *; simpl in *.
        assert (FalseP s h) by omega.
        instantiate (1 := FalseP). destruct H0. } Unfocus.
      intros; unfold_conn; repeat destruct H; tauto.

    + (* fold skip array *)
      forward_barr.
      Focus 2.
      { rewrite pow_divS; eauto. simpl; rewrite MyVector.init_spec.
        intros s h H.
        apply ex_lift_l. exists (st / 2).
        apply ex_lift_l. exists e.
        apply ex_lift_l. exists fc'.
        instantiate (1 := !(TID === Zn (nf tid)) ** !(ARR === arr) ** !(OUT === out)).
        sep_normal; sep_split_in H; sep_split; eauto.
        - unfold_pures.
          autorewrite with sep in *; eauto. unfold_conn; simpl. congruence.
        - unfold_pures. 
        - unfold_pures; unfold fc'; unfold_conn; simpl; subst st.
          autorewrite with sep in *.
          destruct lt_dec; eauto.
          destruct Nat.eq_dec; try congruence.
          destruct HP10 as [Heq Heq']; rewrite Heq, Heq'; clear Heq Heq'.
          cutrewrite (2 ^ S e = 2 ^ e * 2); [|simpl; omega].
          lets Heq: (>>skip_sum_double (2 ^ e) (nf tid) ntrd 0); eauto.
        - unfold_pures; unfold fc'; unfold_conn; simpl; subst st.
          lets: (>>div_le (2 ^ e) 2); omega.
        (* - unfold_pures; unfold fc'; unfold_conn; simpl; subst st. *)
        (*   autorewrite with sep in *; eauto. *)
        - unfold_pures.
          assert (Heq : dbl (st / 2) = st).
          { unfold_pures; unfold fc'; unfold_conn; simpl; subst st; autorewrite with sep; auto. }
          rewrite Heq.
          assert (st <> 0).
          { unfold_pures; subst st; eauto. }
          assert (nf tid < st).
          { unfold_pures; subst. nia. }
          cutrewrite (0 = 0 * st); eauto.
          sep_rewrite skip_arr_unfold'; try omega.
          sep_rewrite skip_arr_unfold'; try first [omega].
          sep_normal.
          unfold fc'.
          destruct Nat.eq_dec; try omega.
          destruct Nat.eq_dec; try omega. 
          sep_cancel.
          cutrewrite (0 * st + nf tid + st = st + nf tid); [|ring].
          sep_cancel.
          rewrite !Nat2Z.inj_add, Nat2Z.inj_mul.
          cutrewrite (1 * st + nf tid = st + nf tid); [|ring].
          cutrewrite (Zn 1 * Zn st = Zn st)%Z; [|ring].
          sep_cancel.
          sep_rewrite (nth_dist_change); try omega; eauto.
          intros j Hj Hlt.
          destruct Nat.eq_dec; try omega.
          cut (nf tid + st < ntrd); [omega|].
          assert (ntrd / 2 + ntrd / 2 <= ntrd).
          { lets: (@div_mult ntrd 2); try omega. }
          omega. } Unfocus.

      intros ? ? H.
      apply ex_lift_l_in in H as [st' H].
      apply ex_lift_l_in in H as [e' H].
      apply ex_lift_l_in in H as [fc0 H].
      sep_normal_in H; sep_split_in H; unfold_pures; unfold INV2.
      exists st' e' fc0; sep_split; eauto.
      unfold ceil2 in *.
      destruct Nat.eq_dec; eauto.

      (* eapply Hbackward. Focus 2. *)
      (* { intros s h H; sep_split_in H. *)
      (*   assert ((T1 + T2 === (fc (nf (tid)) + fc (st + nf tid)%nat)%Z) s (emp_ph loc)) by *)
      (*       (unfold_conn_all; simpl in *; omega). *)
        
      (*   fold (2 ^ S (S e) / 2) in *. *)
      (*   assert (Hst : st = 2 ^ (S e) / 2) by (unfold_conn_in HP6; auto). *)
      (*   cutrewrite (2 ^ (S e) = 2 ^ e * 2) in Hst; [|simpl; omega]. *)
      (*   rewrite Nat.div_mul in Hst; auto. *)
      (*   sep_rewrite_in mps_eq2 H; [|exact H0]. *)

      (*   assert (nf tid < st) *)
      (*     by (unfold_conn_all; simpl in *; destruct (Z_lt_dec (s TID) x); (congruence||omega)). *)
      (*   sep_rewrite_in (@nth_dist_change (nat_of_fin tid) (Gl ARR) fc fc') H; *)
      (*     try now (subst; auto || unfold_conn_all; simpl in *; omega). *)
      (*   2 : rewrite <-!plus_n_O; intros; unfold fc'; destruct Nat.eq_dec; auto; omega. *)
      (*   cutrewrite (st + (st + 0) = 2 * st) in H; [|omega]. *)
      (*   assert ((Gl ARR +o (TID + x) ===l Gl ARR +o Z.of_nat (1 * st + nf tid))%exp s (emp_ph loc)). *)
      (*   { unfold_conn_all; simpl; simplify_loc; rewrite !Nat2Z.inj_add, Z.add_0_r; simpl in*; omega. } *)
      (*   sep_rewrite_in (@mps_eq1 (Gl ARR +o (TID + x))%exp ) H; [|exact H2]. *)
      (*   cutrewrite (fc (nf tid) + fc (st + nf tid)%nat = fc' (0 * st + nf tid)%nat)%Z in H; [|]. *)
      (*   2: unfold fc'; destruct Nat.eq_dec; unfold_conn_all; simpl in *; [f_equal; f_equal; omega| omega]. *)
      (*   cutrewrite (fc (st + nf tid)%nat = fc' (1 * st + nf tid)%nat)%Z in H; [|]. *)
      (*   2: unfold fc'; destruct Nat.eq_dec; unfold_conn_all; simpl in *; [omega|f_equal; omega]. *)
      (*   sep_rewrite_in_r skip_arr_unfold' H; (omega || auto). *)
      (*   2: unfold_conn_in HP8; omega. *)
      (*   assert ((Gl (ARR + TID)%exp ===l Gl ARR +o Z.of_nat (0 * st + nf tid)) s (emp_ph loc)). *)
      (*   { unfold_conn_all; simpl in *; simplify_loc; omega. } *)
      (*   sep_rewrite_in mps_eq1 H; [|exact H3]. *)
      (*   sep_rewrite_in_r skip_arr_unfold' H; (omega || auto). *)
      (*   clear HP0 HP1 HP2 H0. *)
      (*   sep_combine_in H. exact H. } Unfocus. *)

      (* (* barrier pre holds at barrier (then) *) *)
      (* forward_barr. Focus 2. *)
      (* { autorewrite with sep; auto. *)
      (*   simpl; rewrite MyVector.init_spec.  *)
      (*   intros s h H; sep_normal_in H; sep_split_in H. *)
      (*   apply ex_lift_l; exists (2 ^ e / 2); apply ex_lift_l; exists fc'. *)
      (*   do 3 (sep_normal; sep_split). *)
      (*   - unfold_pures. autorewrite with sep in *; auto; simpl.  *)
      (*     unfold_conn; simpl; congruence. *)
      (*   - unfold_pures; unfold_conn; autorewrite with sep in *. *)
      (*     unfold fc' in *; clear fc'; subst st; rewrite ceil2_pow in HP4. *)
      (*     destruct Nat.eq_dec; try omega; destruct (lt_dec); auto. *)
      (*     destruct HP4 as [Heq1 Heq2]; rewrite Heq1, Heq2; autorewrite with sep. *)
      (*     cutrewrite (2 ^ S e = 2^e*2); [|simpl; omega]. *)
      (*     cutrewrite (0 = 0 * 2 * (2^e * 2)); [|omega]; apply (skip_sum_double) ; omega. *)
      (*   - rewrite dbl_inv. *)
      (*     unfold_conn_all; simpl in *; omega. *)
      (*   - sep_normal.  *)
      (*     rewrite dbl_inv. *)
      (*     cutrewrite (2 ^ e = st); [|unfold_conn_all; congruence]. *)
      (*     sep_combine_in H; sep_cancel. exact H. } Unfocus. *)
      
      (* (* loop invariant is preserved *) *)
      (* intros s h H; unfold INV; clear fc'. *)
      (* apply ex_lift_l_in in H; destruct H as (s0 & H). *)
      (* apply ex_lift_l_in in H; destruct H as (fc' & H); sep_split_in H. *)
      (* exists (2 ^ e / 2), e, fc'. *)
      (* assert ((St === Z.of_nat (2 ^ e / 2)) s (emp_ph loc)). *)
      (* { unfold_conn_in (HP, HP2, HP3); simpl in HP2, HP3; rewrite HP2, HP3 in HP; simpl in HP. *)
      (*   rewrite Zdiv2_div in HP. rewrite div_Zdiv; auto. } *)
      (* assert (s0 = 2 ^ e / 2). *)
      (*   { unfold_conn_in (HP8, H0); rewrite HP8 in H0; simpl in H0. *)
      (*     apply Nat2Z.inj in H0; auto. } *)
      (* sep_split; try now (unfold_conn_all; (auto || omega)). *)
      (* * unfold_conn_in (HP8, H0); rewrite HP8 in H0; simpl in H0; apply Nat2Z.inj in H0; *)
      (*   rewrite H0 in HP9. *)
      (*   apply HP9. *)
      (* * unfold_conn_in (HP5, HP3); simpl in HP5, HP3; unfold_conn. *)
      (*   assert (2 ^ e <> 0) by (apply Nat.pow_nonzero; auto). *)
      (*   assert (2 ^ e / 2 < 2 ^ e) by (apply Nat.div_lt; omega). *)
      (*   omega. *)
      (* * unfold ceil2 in H; destruct Nat.eq_dec; subst; destruct Nat.eq_dec; (omega || auto). *)
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
      assert ((2 ^ e) / 2 = 2 ^ (e - 1)).
      { unfold_pures; destruct e; [simpl in *; omega|].
        cutrewrite (S e - 1 = e); [|omega].
        autorewrite with sep; eauto. }
      apply ex_lift_l; exists (2 ^ (e - 1) / 2).
      apply ex_lift_l; exists (e - 1).
      apply ex_lift_l; exists fc.
      sep_rewrite_in_r emp_unit_r H; sep_split_in H.
      instantiate (1 := !(TID === Zn (nf tid)) ** !(ARR === arr) ** !(OUT === out)).
      sep_normal; sep_split;
      try now (unfold_conn_all; simpl in *; autorewrite with sep in *; auto).
      - rewrite <-H0; unfold_pures; autorewrite with sep in *; auto.
      - unfold_pures.
        rewrite H0 in *; autorewrite with sep in *.
        destruct lt_dec; try omega; eauto.
        (* unfold_pures; destruct (lt_dec (nf tid) (dbl _)); unfold_conn; auto. *)
        (* rewrite HP1 in *; rewrite <-Nat2Z.inj_lt in n0. *)
        (* destruct e as [|e]; [cbv in l; inversion l|]. *)
        (* autorewrite with sep in l0; autorewrite with sep in n0; auto; omega. *)
      - unfold_pures; unfold_conn.
        lets: (>>div_le (2 ^ (e - 1)) 2).
        omega.
      (* - unfold_pures; unfold_conn. *)
      (*   destruct e as [|e]; [cbv in l; inversion l|]. *)
      (*   autorewrite with sep; auto. autorewrite with sep in HP4; auto. *)
      - unfold_pures.
        autorewrite with sep.
        rewrite H0 in HP.
        rewrite nth_overflow; eauto.
        rewrite distribute_length; auto.
        (* destruct e as [|e]; [unfold_pures; cbv in HP2; inversion HP2|].   *)
        (* change_; [intros Hf|]. *)
        (* { autorewrite with sep in HP5; auto; unfold_pures. *)
        (*   rewrite HP1 in n0; rewrite <-Nat2Z.inj_lt in n0. *)
        (*   rewrite nth_overflow; [|rewrite distribute_length; autorewrite with sep in *; omega]. *)
        (*   exact Hf. } *)
        (* sep_combine_in H; sep_cancel; exact H. *) } Unfocus.

    (* loop invariant is preserved *)
    instantiate (1 := INV2 (nf tid) (nf bid) arr out); unfold INV2; intros; apply ex_lift_l_in in H; destruct H as [s0 H].
    apply ex_lift_l_in in H; destruct H as [e0 H].
    apply ex_lift_l_in in H; destruct H as [fc' H].
    sep_split_in H.
    unfold_pures.
    (* destruct e; [cbv in l; congruence|]. *)
    exists s0 e0 fc'.
    sep_split; eauto.
    unfold ceil2 in H; destruct Nat.eq_dec; eauto.
    (* autorewrite with sep in *; auto.  clear HP3 HP7. *)
    (* exists (2 ^ e / 2), e, fc'; sep_split; try now simpl; first [eauto | omega | congruence]; *)
    (* autorewrite with sep; auto. *)
    (* + rewrite HP1 in n0; rewrite <-Nat2Z.inj_lt in n0; unfold_conn. *)
    (*   destruct e as [|e]; [destruct (lt_dec _ (ceil2 (_/_))) as [Hlt | ?]; unfold_conn; auto |]. *)
    (*   unfold ceil2 in Hlt; simpl in n0, Hlt; omega. *)

    (*   autorewrite with sep; auto; simpl in *. *)
    (*   destruct lt_dec; [omega | unfold_conn; auto]. *)
    (* + unfold_conn; destruct e; [cbv; omega|autorewrite with sep; auto]. *)
    (*   simpl in HP4; omega. *)
    (* + cutrewrite (2%Z = Z.of_nat 2) in HP0; [|auto]; rewrite <-div_Zdiv in HP0; auto. simpl in HP0. *)
    (*   rewrite HP6 in HP0; apply Nat2Z.inj in HP0; subst. *)
    (*   destruct e; [unfold div, ceil2 in *; simpl in *; auto|]. *)
    (*   autorewrite with sep in *; auto. *)
    (*   destruct Nat.eq_dec; [apply Nat.pow_nonzero in e0; auto; destruct e0|]. *)
    (*   apply H. *)
  - unfold_conn; intros; tauto.
  - intros; eauto.
  - eapply Hforward.
    + eapply rule_if_disj.
      * eapply Hbackward.
        Focus 2.
        { intros s h H; unfold INV2 in *.
          sep_split_in H.
          sep_lift_in H 3.
          apply ex_lift_l_in in H; destruct H as [s0 H].
          apply ex_lift_l_in in H; destruct H as [e H].
          apply ex_lift_l_in in H; destruct H as [fc' H].
          sep_normal_in H; sep_split_in H.
          assert (s0 = 0); [|subst s0].
          { unfold_pures. nia. }
          unfold dbl in *; simpl in *.
          assert (Heq : nf tid = 0); [|rewrite Heq in *].
          { unfold_pures; nia. }
          unfold ceil2 in *; simpl in *.
          rewrite skip_sum_sum in HP7.
          lets unf: (>>(@skip_arr_unfold') 0 ntrd 1 0); eauto.
          simpl in unf.
          sep_rewrite_in unf H; eauto; clear unf.
          destruct HP7 as [Heq' _]; rewrite Heq' in H.
          assert (pure (nf tid = 0) s (emp_ph loc)) by (unfold_conn; auto).
          assert (pure (fc' 0 = sum_of 0 ntrd (f_ss' (nf bid))) s (emp_ph loc)) by (unfold_conn; auto).
          clear HP5 HP6 HP8; sep_combine_in H.
          ex_intro fc' H; exact H. } Unfocus.
        repeat hoare_forward.
        eapply rule_seq.
        hoare_forward; [intros ? ? H; exact H|..].
        hoare_forward.
        intros ? ? H. ex_intro x3 H; exact H.
      * apply rule_skip.
    + intros s h [H|H].
      * destruct H as [fc' H].
        exists fc'; sep_split_in H; sep_split; unfold_pures.
        destruct Nat.eq_dec; try omega.
        rewrite e0 in *; simpl.
        repeat sep_cancel.
        lets unf: (>>(@skip_arr_unfold') 0 ntrd 1 0); eauto.
        simpl in unf.
        sep_rewrite unf; eauto; clear unf.
        rewrite HP7.
        sep_normal; repeat sep_cancel.
      * unfold INV2 in *; sep_split_in H.
        sep_lift_in H 3.
        apply ex_lift_l_in in H; destruct H as [s0 H].
        apply ex_lift_l_in in H; destruct H as [e H].
        apply ex_lift_l_in in H; destruct H as [fc' H].
        sep_normal_in H; sep_split_in H; unfold_pures.
        exists fc'.
        sep_cancel.
        assert (s0 = 0) by nia.
        rewrite H1 in *; simpl in H0.
        assert (nf tid <> 0) by nia.
        destruct (Nat.eq_dec (nf tid)); try omega.
        rewrite nth_overflow in H0; sep_normal_in H0; eauto.
        rewrite distribute_length; nia.
Qed.
Import ListNotations.
Definition hi_list := TID :: I :: T1 :: T2 :: nil.
  
Definition ty_env_fold (v : var) := if in_dec var_eq_dec v hi_list then Hi else Lo.

Hint Constructors typing_cmd typing_exp typing_lexp typing_bexp.

Lemma typing_fold : typing_cmd ty_env_fold fold_ker' Lo.
Proof.
  unfold fold_ker', fold_ker.
  (repeat econstructor); try reflexivity.
  repeat instantiate (1 := Lo); reflexivity.
  repeat instantiate (1 := Lo); reflexivity.
  repeat instantiate (1 := Lo); reflexivity.
  constructor.
  repeat instantiate (1 := Hi); reflexivity.
  Grab Existential Variables.
  apply Lo.
  apply Lo.
  apply Lo.
Qed.

Lemma conj_xs_var (va : var) n (vs : nat -> nat) stk : forall st,
  conj_xs (ls_init st n (fun i => va === Zn (vs i))) stk (emp_ph loc) ->
  forall i, i < n -> vs (st + i) = Z.to_nat (stk va).
Proof.
  induction n; simpl; intros st Hsat i Hi; try omega.
  destruct Hsat as (? & ? & Hsat1 & Hsat2 & ? & ?); unfold_conn_in Hsat1; simpl in Hsat1.
  destruct i.
  - rewrite <-plus_n_O; eauto.
    rewrite Hsat1, Nat2Z.id; eauto.
  - apply phplus_emp in H0; destruct H0; subst.
    rewrite <-Nat.add_succ_comm; apply IHn; eauto; omega.
Qed.

Lemma distribute_correct' nt m e l fs dist s:
  m <> 0 ->
  m <= nt ->
  (forall i, dist i < m) ->
  forall stk, 
  stk ||= conj_xs (ls_init 0 nt (fun i => nth i (distribute m e l (fs i) dist s) emp)) <=>
          is_array e l (fun i => (fs (dist i) i)) s.
Proof.
  intros Hm0 Hmnt Hdis stk.
  rewrite <-(firstn_skipn m (ls_init _ _ _)).
  rewrite firstn_init, skipn_init.
  rewrite Nat.min_l, <-plus_n_O; auto.

  rewrite conj_xs_app.
  lazymatch goal with
  | [|- context [((_ ** conj_xs (ls_init ?b ?n ?P)))] ] =>
    evar (fc : nat -> assn); 
    sep_rewrite (@ls_init_eq' _ P fc n b); unfold fc in *
  end.
  2: intros i Hi; simpl; rewrite nth_overflow; [|rewrite distribute_length; omega].
  2: instantiate (1 := fun _ => emp); reflexivity.

  rewrite (init_emp_emp (nt - m) m), emp_unit_r.

  (* erewrite ls_init_eq0. *)
  (* 2: intros i Hi; rewrite nth_nseq; destruct (leb ntrd i) eqn:Heq; *)
  (* try ((apply leb_iff in Heq || apply leb_iff_conv in Heq); omega). *)
  (* 2: reflexivity. *)

  rewrite equiv_from_nth.
  symmetry. apply distribute_correct; auto.
  rewrite init_length, distribute_length; reflexivity.
  rewrite init_length; intros i Hi stc; rewrite ls_init_spec.
  destruct (lt_dec i m); try omega.
  simpl.
  rewrite nth_dist_change; [reflexivity|auto..].
  intros j Hj <-; auto. 
Qed.

Lemma barrier_wf bid : Bdiv.Aistar_v (fst (binv bid 1)) |= Bdiv.Aistar_v (snd (binv bid 1)).
Proof.
  simpl; intros s h H.

  istar_simplify_in H.
  istar_simplify.
  sep_rewrite (@ls_exists0 _ 0); exists vs; sep_split; eauto.
  sep_rewrite (@ls_exists0 _ 0); exists vs0; sep_split; eauto.

  lets Hst: (conj_xs_var HP2).
  set (fcc := fun i : nat => (nth (i mod (dbl (Z.to_nat (s St)))) vs1 (fun _:nat=>0%Z)) i).
  sep_rewrite (@ls_exists0 _ (fun _ : nat=> 0%Z)).
  exists (nseq ntrd fcc); sep_split; [rewrite length_nseq; reflexivity|].
  
  repeat sep_rewrite (@ls_star); repeat sep_rewrite (@ls_pure); sep_split; eauto.
  - apply ls_emp'; rewrite init_length; intros i Hi.
    rewrite ls_init_spec; destruct lt_dec; [|omega].
    lets H': (>>(@ls_emp) i HP4).
    rewrite ls_init_spec in H'; destruct lt_dec; [|omega].
    simpl in *.
    rewrite Hst in *; try omega.
    destruct (Z.to_nat (s St)); unfold dbl, ceil2 in *; [simpl in *|].
    destruct lt_dec; try tauto.
    + unfold fcc; rewrite nth_nseq.
      destruct (leb ntrd i) eqn:Heq; [apply leb_iff in Heq; omega|].
      rewrite <-plus_n_O.
      assert (i = 0) by omega; subst; eauto.
      split; eauto.
    + remember (S n) as n'.
      destruct Nat.eq_dec; try omega.
      unfold fcc; rewrite nth_nseq.
      destruct (leb ntrd i) eqn:Heq; [apply leb_iff in Heq; omega|].
      destruct (lt_dec i n'); [|unfold_conn; eauto].
      rewrite !Nat.mod_small; try omega.
      split.
      * destruct lt_dec; try omega.
        apply H'.
      * lets Hstl: (>>ls_emp i HP5); rewrite ls_init_spec in Hstl; destruct (lt_dec i ntrd); try omega.
        rewrite Hst in Hstl; try omega.
        assert (n' + n' <= ntrd).
        { pose proof (@div_mult ntrd 2).
          unfold_pures; nia. }
        lets H'': (>>ls_emp (i + n') HP4); rewrite ls_init_spec in H''; try omega.
        rewrite Hst in H''; try omega.
        destruct (lt_dec (i + n') ntrd); try omega.
        simpl in H''; destruct Nat.eq_dec; try omega.
        destruct (lt_dec (i + n') (n' * 2)); try omega.
        apply H''. 
  - 
    simpl in Hst.
    rewrite_body Hst omega.
    rewrite_body_in Hst omega H.
    


  (* erewrite ls_init_eq0 in H. *)
  (* Focus 2. *)
  (* { intros i iH. *)
  (*   destruct (Fin.of_nat i ntrd) as [|Hex] eqn:Heq; [|destruct Hex; omega]. *)
  (*   rewrite (Fin_nat_inv Heq). reflexivity. } Unfocus. *)
  (* apply sc_v2l. *)
  (* rewrite (vec_to_list_init0 _ emp). *)
  (* erewrite ls_init_eq0. *)
  (* Focus 2. *)
  (* { intros i iH. *)
  (*   destruct (Fin.of_nat i ntrd) as [|Hex] eqn:Heq; [|destruct Hex; omega]. *)
  (*   rewrite (Fin_nat_inv Heq). reflexivity. } Unfocus. *)

  (* sep_rewrite_in (ls_exists0 0 (n := ntrd)) H; auto; destruct H as [vs H]. *)
  (* sep_split_in H. *)
  (* sep_rewrite_in (ls_exists0 (fun _ : nat => 0%Z) (n:=ntrd)) H; auto; destruct H as [fs H]. *)
  (* sep_split_in H. *)

  (* repeat sep_rewrite_in (@ls_star ntrd) H. *)

  (* repeat sep_rewrite_in (@ls_pure ntrd) H; sep_split_in H. *)
  
  (* assert (exists s0, forall i, i < ntrd -> nth i vs 0 = s0) as [s0 Hs0]. *)
  (* { destruct vs as [|s0 vs]; [cbv in HP; omega|]. *)
  (*   exists s0; intros i. *)
  (*   destruct i; simpl; auto. *)
  (*   pose proof (@ls_emp _ _ 0 HP1); rewrite ls_init_spec in H0; destruct lt_dec; try omega. *)
  (*   pose proof (@ls_emp _ _ (S i) HP1); rewrite ls_init_spec in H1; destruct lt_dec; try omega. *)
  (*   unfold_conn_all; simpl in *. *)
  (*   assert (Z.of_nat s0 = Z.of_nat (nth i vs 0)) by congruence. *)
  (*   apply Nat2Z.inj in H2; congruence. } *)
  (* pose proof (@ls_emp _ _ 0 HP3) as Hs0ntrd; rewrite ls_init_spec in Hs0ntrd; *)
  (* destruct lt_dec; unfold_conn_in Hs0ntrd; try omega. *)
  (* rewrite Hs0 in Hs0ntrd; try omega. *)
  
  (* erewrite ls_init_eq0 in H; [|intros; rewrite Hs0; auto; reflexivity]. *)
  (* erewrite ls_init_eq0 in HP2; [|intros; rewrite Hs0; auto; reflexivity]. *)
  (* erewrite ls_init_eq0 in HP3; [|intros; rewrite Hs0; auto; reflexivity]. *)
  (* sep_rewrite (ls_exists0 0 (n:= ntrd)); auto; exists vs. *)
  (* sep_split; auto. *)
  (* sep_rewrite (ls_exists0 (fun _:nat => 0%Z) (n:=ntrd)); auto. *)
  (* set (fcc := fun i : nat => *)
  (*        (nth (i mod (dbl s0)) fs (fun _:nat=>0%Z)) i). *)
  (* exists (nseq ntrd fcc); sep_split; [rewrite length_nseq; reflexivity|]. *)
  (* (repeat sep_rewrite (@ls_star ntrd)).  *)
  (* repeat sep_rewrite (@ls_pure ntrd). *)
  (* repeat sep_split; auto. *)

  (* apply ls_emp'; intros i Hi; rewrite init_length in Hi. *)
  (* rewrite ls_init_spec; destruct lt_dec; try omega; simpl. *)
  (* rewrite Hs0; auto; destruct lt_dec; [|cbv; auto]. *)
  (* rewrite nth_nseq; destruct (leb ntrd i) eqn:Heq; try (apply leb_iff in Heq; omega). *)
  (* unfold fcc. *)

  (* pose proof (ceil2_dbl s0). *)
  (* repeat (rewrite Nat.mod_small; [|omega]). *)
  (* split. *)
  (* pose proof (@ls_emp _ _ i HP2); rewrite ls_init_spec in H1. *)
  (* destruct (lt_dec i ntrd); try omega. *)
  (* destruct (lt_dec (0 + i) (dbl s0)); try omega. *)
  (* apply H1. *)
  (* pose proof (@ls_emp _ _ 0 HP3); rewrite ls_init_spec in H1; destruct lt_dec; unfold_conn_in H1; try omega. *)
  (* pose proof (@ls_emp _ _ (i + s0) HP2); rewrite ls_init_spec in H2. *)
  (* destruct (lt_dec (i + s0) ntrd); try omega. *)
  (* destruct (lt_dec (0 + (i + s0)) (dbl s0)); try omega. *)
  (* apply H2. *)
  (* erewrite ls_init_eq0; [|intros; rewrite Hs0; auto; reflexivity]; auto. *)


  assert (dbl (Z.to_nat (s St)) <= ntrd).
  { rewrite <-(Hst 0); unfold dbl; try omega.
    destruct (Nat.eq_dec (nth 0 vs 0) 0); try omega.
    lets Hst': (>>ls_emp 0 HP5); rewrite ls_init_spec in Hst'; destruct lt_dec; try omega; simpl in Hst'.
    lets: (@div_mult ntrd 2); unfold_pures; try omega. }

  assert (ceil2 (Z.to_nat (s St)) <= ntrd).
  { lets: (ceil2_dbl (Z.to_nat (s St))); omega. }
  
  apply distribute_correct' in H; auto.
  apply distribute_correct'; auto.

  sep_rewrite is_array_change; eauto.
  intros i Hi; unfold fcc; rewrite <-plus_n_O.
  rewrite nth_nseq.
  destruct (leb _ _) eqn:Heq.
  apply leb_iff in Heq.
  assert (nt_step (ceil2 (Z.to_nat (s St))) i < ceil2 (Z.to_nat (s St))) by auto.
  omega.
  auto.
Qed.  

Lemma is_array_distr e n (f' : nat -> Z) :
  forall s stk,
    stk ||= conj_xs (ls_init s n (fun i => e +o Zn i -->p (1, f' i))) <=>
        is_array e n f' s.
Proof.
  induction n; intros s stk; simpl.
  - reflexivity.
  - rewrite IHn; reflexivity.
Qed.

Lemma barrier_wf0 bid : Bdiv.Aistar_v (fst (binv bid 0)) |= Bdiv.Aistar_v (snd (binv bid 0)).
Proof.
  simpl; intros s h H.
  istar_simplify_in H.
  istar_simplify.
  apply distribute_correct'; eauto.
  { unfold ceil2; destruct Nat.eq_dec; try omega.
    lets: (>>div_mult ntrd 2); omega. }
  
  apply is_array_distr in H; auto.
Qed.

Require Import MyVector. 
Import VectorNotations.
Lemma precise_binv0_pre bid tid : precise ((fst (binv0 bid))[@tid]).
Proof.
  unfold binv0; simpl; rewrite MyVector.init_spec.
  unfold precise; intros.
  eapply mps_precise; eauto.
Qed.

Lemma precise_pts e1 e2 q :
  precise (e1 -->p (q, e2)).
Proof.
  unfold precise; intros; simpl in *.
  unfold_conn_all; simpl.
  destruct h1 as [h1 ?], h1' as [h1' ?]; apply pheap_eq.
  extensionality l; simpl in *; rewrite H, H0.
  auto.
Qed.

Lemma precise_sat (P Q : assn) :
  (Q |= P) -> precise P -> precise Q.
Proof.
  unfold precise; simpl; intros Hsat HprecP; introv.
  intros HsatQ HsatQ' ? ? ?.
  eapply HprecP; eauto.
Qed.
Hint Rewrite add_nth_length distribute_length.

Lemma distribute_precise d e n dist i : forall s,
  precise (Ex f', List.nth i (distribute d e n f' dist s) emp).
Proof.
  induction n; simpl; intros.
  - rewrite nth_nseq; destruct leb; apply (@precise_sat emp); auto using precise_emp;
    intros ? ? [? ?]; auto.
  - assert (d <= i \/ i < d) as [? | ?] by omega.
    + apply (@precise_sat emp); auto.
      intros ? ? [v H'].
      rewrite nth_overflow in H'; autorewrite with core; eauto using precise_emp.
    + assert (d <= dist s \/ dist s < d) as [? | ?] by omega.
      * eapply precise_sat; [intros stk h [f' Hsat]|].
        { rewrite add_nth_overflow in Hsat; autorewrite with core; auto.
          ex_intro f' Hsat; apply Hsat. }
        auto.
      * eapply precise_sat; [intros stk h [f' Hsat]|].
        { rewrite nth_add_nth in Hsat; autorewrite with core; auto. 
          ex_intro f' Hsat; apply Hsat. }
        destruct beq_nat; auto.
        apply precise_ex_star, precise_star; auto.
        eapply precise_sat; [intros stk h [f' Hsat]|].
        { ex_intro (f' s) Hsat; apply Hsat. }
        apply GCSL.precise_pts.
Qed.

Lemma precise_binv0_snd bid tid : precise ((snd (binv0 bid))[@tid]).
Proof.
  unfold binv0; simpl; rewrite MyVector.init_spec.
  eapply precise_sat; [intros stk h Hsat| ].
  { ex_intro (f_ss' (nf bid)) Hsat; apply Hsat. }
  apply distribute_precise.
Qed.

Lemma distribute_rewrite1 d e e' n f' dist stk i:
  (e ===l e') stk (emp_ph loc) ->
  forall s,
    stk ||= List.nth i (distribute d e n f' dist s) emp <=>
            List.nth i (distribute d e' n f' dist s) emp.
Proof.
  intros Heq; induction n; intros s; simpl.
  - reflexivity.
  - assert (d <= i \/ i < d) as [?|?] by omega.
    + rewrite !nth_overflow; autorewrite with core; auto.
      reflexivity.
    + assert (d <= dist s \/ dist s < d) as [?|?] by omega.
      * rewrite !add_nth_overflow; autorewrite with core; auto.
      * rewrite !nth_add_nth; autorewrite with core; auto.
        destruct beq_nat; auto.
        assert ((e +o Zn s ===l e' +o Zn s) stk (emp_ph loc)).
        { unfold_pures; unfold_conn; simpl; rewrite Heq; auto. }
        lets Heq': (>>mps_eq1 H1); rewrite Heq'.
        rewrite IHn; reflexivity.
Qed.

Lemma precise_ex_var (P : val -> assn) E :
  (forall v, precise (P v)) ->
  precise (Ex v, !(E === Enum v) ** P v).
Proof.
  unfold precise; simpl; intros Hprec; introv Hsat1 Hsat2 ? ?.
  eapply Hprec; eauto;
  destruct Hsat1 as [v1 Hsat1], Hsat2 as [v2 Hsat2];
  sep_split_in Hsat1; sep_split_in Hsat2.
  cutrewrite (v1 = edenot E s) in Hsat1; [|unfold_pures; auto]; eauto.
  cutrewrite (v2 = edenot E s) in Hsat2; [|unfold_pures; auto]; eauto.
Qed.

Lemma precise_binv1_fst bid tid : precise ((fst (binv1 bid))[@tid]).
Proof.
  unfold binv1; simpl; rewrite MyVector.init_spec.
  eapply precise_sat; [intros stk h (s & e & fc & Hsat)|].
  { sep_split_in Hsat.
    clear HP0 HP1 HP2 HP3.
    rewrite <-(Nat2Z.id s) in Hsat.
    ex_intro fc Hsat.
    sep_combine_in Hsat.
    apply scC in Hsat.
    ex_intro (Zn s) Hsat.
    exact Hsat. }
  simpl.
  apply precise_ex_var.
  intros; apply distribute_precise.
Qed.

Lemma precise_binv1_snd bid tid : precise ((snd (binv1 bid))[@tid]).
Proof.
  unfold binv1; simpl; rewrite MyVector.init_spec.
  eapply precise_sat; [intros stk h (s & e & fc & Hsat)|].
  { sep_split_in Hsat.
    clear HP0 HP1 HP2 HP3.
    rewrite <-(Nat2Z.id s) in Hsat.
    ex_intro fc Hsat.
    sep_combine_in Hsat.
    apply scC in Hsat.
    ex_intro (Zn s) Hsat.
    exact Hsat. }
  simpl.
  apply precise_ex_var.
  intros; apply distribute_precise.
Qed.
Import ListNotations.

Definition tid_pre (arr out : Z) (bid : Fin.t nblk) (tid : Fin.t ntrd) :=
  (Ex v1 v2 : Z,
   !(ARR === arr) **
   !(OUT === out) **
   (Sh SARR +o Zn (nf tid) -->p (1,  v1)) **
   skip_arr (Gl arr) 0 len nt_gr f (nf tid + nf bid * ntrd) **
   (if Nat.eq_dec (nf tid) 0
    then Gl out +o Zn (nf bid) -->p (1,  v2)
    else emp) ** !(BID === Zn (nf bid))).

Definition tid_post (arr out : Z) (bid : Fin.t nblk) (tid : Fin.t ntrd) :=
  (Ex fc : nat -> Z,
   skip_arr (Gl arr) 0 len nt_gr f (nf tid + nf bid * ntrd) **
   (if Nat.eq_dec (nf tid) 0
    then
     List.nth (nf tid) (distribute 1 (Sh SARR) ntrd fc (nt_step 1) 0) emp **
     (Gl out +o Zn (nf bid) -->p (1,  sum_of 0 ntrd (f_ss' (nf bid))))
    else emp)).

Lemma is_array_conj_xs e len' f' : forall s stk,
  stk ||= is_array e len' f' s <=> conj_xs (ls_init s len' (fun i => e +o Zn i -->p (1, f' i))).
Proof.
  induction len'; introv; simpl.
  - reflexivity.
  - split; intros; sep_cancel; apply IHlen'; auto.
Qed.

Lemma fold_correct_b (bid : Fin.t nblk) (arr out : val) :
  nt_gr <= len ->
  CSLp ntrd ty_env_fold
  (Ex v2 : Z,
   !(ARR === arr) ** !(OUT === out) ** sh_spec ((SARR, ntrd) :: List.nil) ** !(BID === Zn (nf bid)) **
   conj_xs (ls_init 0 ntrd (fun i => skip_arr (Gl arr) 0 len nt_gr f (i + nf bid * ntrd))) **
   (Gl out +o Zn (nf bid) -->p (1, v2)))
  fold_ker'
  (sh_spec ((SARR, ntrd) :: List.nil) ** 
   conj_xs (ls_init 0 ntrd (fun i => skip_arr (Gl arr) 0 len nt_gr f (i + nf bid * ntrd))) **
   (Gl out +o Zn (nf bid) -->p (1, sum_of 0 ntrd (f_ss' (nf bid))))).
Proof.
  intros Hlen.
  applys (>>rule_par (binv bid) (MyVector.init (tid_pre arr out bid))
            (MyVector.init (tid_post arr out bid))).
  - exists (ntrd - 1); try omega.
  - unfold tid_pre, tid_post, binv, binv0, binv1.
    destruct i.
    { split; intros;
      destruct Nat.eq_dec; try congruence; simpl; rewrite MyVector.init_spec.
      unfold ty_env_fold, hi_list, low_assn.
      prove_low_assn; repeat econstructor.
      applys_eq ty_offset 1; repeat econstructor; repeat reflexivity. 
      instantiate (1 := Lo).
      reflexivity.

      apply low_assn_skip_arr.
      repeat econstructor; repeat reflexivity. }
    destruct i.
    { split; intros; destruct Nat.eq_dec; try congruence; simpl; rewrite MyVector.init_spec;
      unfold low_assn.
      repeat prove_low_assn; try now (repeat econstructor; repeat reflexivity).
      apply low_assn_skip_arr; repeat econstructor; repeat reflexivity.
      repeat prove_low_assn; try now (repeat econstructor; repeat reflexivity).
      apply low_assn_skip_arr; repeat econstructor; repeat reflexivity. }
    split; intros; destruct Nat.eq_dec; try congruence; simpl; rewrite MyVector.init_spec;
    unfold low_assn; prove_low_assn.
  - intros [|[|?]] [s h]; simpl.
    apply barrier_wf0.
    apply barrier_wf.
    eauto.
  - intros [|[|?]] tid; split.
    apply precise_binv0_pre.
    apply precise_binv0_snd.
    apply precise_binv1_fst.
    apply precise_binv1_snd.
    simpl; rewrite MyVector.init_spec.
    unfold precise; intros; destruct H.
    simpl; rewrite MyVector.init_spec.
    unfold precise; intros; destruct H.
  - simpl; intros s h [v2 H].
    sep_split_in H.
    unfold tid_pre.
    istar_simplify.
    sep_rewrite_in emp_unit_r H.
    apply ex_lift_l_in in H; destruct H as [fsh H].
    sep_rewrite (@ls_exists0 _ 0%Z); exists (ls_init 0 ntrd fsh); sep_split; eauto.
    rewrite init_length; reflexivity.
    sep_rewrite (@ls_exists0 _ 0%Z); exists (nseq ntrd v2). sep_split; eauto.
    rewrite length_nseq; reflexivity.
    repeat sep_rewrite (@ls_star); repeat sep_rewrite (@ls_pure); sep_split.
    + apply ls_emp'; intros i Hi; rewrite init_length in Hi; rewrite ls_init_spec;
      destruct lt_dec; eauto; omega.
    + apply ls_emp'; intros i Hi; rewrite init_length in Hi; rewrite ls_init_spec;
      destruct lt_dec; eauto; omega.
    + apply ls_emp'; intros i Hi; rewrite init_length in Hi; rewrite ls_init_spec;
      destruct lt_dec; eauto; omega.
    + sep_cancel.
      sep_rewrite (@ls_init_eq0).
      Focus 2.
      intros i Hi; rewrite ls_init_spec; destruct lt_dec; try omega; simpl; reflexivity.
      
      sep_rewrite_in is_array_conj_xs H0.
      sep_cancel.
      rewrite <-(firstn_skipn 1 (ls_init _ _ _)).
      rewrite firstn_init, skipn_init.
      rewrite Nat.min_l, <-plus_n_O; try omega.
      simpl.
      rewrite nth_nseq.
      destruct (leb ntrd 0) eqn:Heq; [rewrite leb_iff in Heq; try omega|].
      sep_cancel.
      sep_rewrite (@ls_init_eq).
      Focus 2.
      intros i Hi.
      destruct Nat.eq_dec; try omega.
      cutrewrite (emp = id (fun i => emp) (0 + 1 + i)).
      reflexivity.
      reflexivity.
      unfold id.
      apply init_emp_emp; auto.
  - simpl; intros s h H.
    unfold tid_post in H;  istar_simplify_in H.
    sep_rewrite emp_unit_r.
    apply ex_lift_l; exists (List.nth 0 vs (fun _ => 0%Z)).
    repeat sep_cancel.
    rewrite <-(firstn_skipn 1 (ls_init _ _ _)) in H0.
    rewrite firstn_init, skipn_init in H0.
    rewrite Nat.min_l, <-plus_n_O in H0; try omega.
    sep_rewrite_in (@ls_init_eq0) H0.
    Focus 2.
    intros i Hi.
    destruct Nat.eq_dec; try omega.
    reflexivity.
    sep_rewrite_in conj_xs_app H0.
    sep_rewrite_in (@ls_star) H0.
    sep_rewrite_in distribute_correct' H0; try omega; eauto.
    simpl in H0.
    sep_normal_in H0.
    sep_rewrite (is_array_change ntrd nblk); try omega.
    sep_cancel.
    2: intros; eauto.
    sep_rewrite_in (@ls_init_eq) H0.
    Focus 2.
    intros i Hi.
    destruct Nat.eq_dec; try omega.
    cutrewrite (emp = id (fun i => emp) (0 + 1 + i)).
    reflexivity.
    reflexivity.
    unfold id in H0.
    sep_rewrite_in init_emp_emp H0; auto.
    sep_normal_in H0.
    auto.
  - intros; unfold tid_pre; rewrite MyVector.init_spec.
    unfold low_assn.
    repeat prove_low_assn; eauto using low_assn_skip_arr.
    applys_eq ty_offset 1; eauto.
    instantiate (1:=Lo); reflexivity.
    applys_eq ty_offset 1; eauto.
    instantiate (1:=Lo); instantiate (1:=Lo); reflexivity.
  - intros; unfold tid_post; rewrite MyVector.init_spec.
    unfold low_assn.
    repeat prove_low_assn; eauto using low_assn_skip_arr.
    applys_eq ty_offset 1; eauto.
    instantiate (1:=Lo); instantiate (1:=Lo); reflexivity.
  - apply typing_fold.
  - intros tid; unfold tid_pre, tid_post; rewrite !init_spec.
    eapply Hbackward.
    eapply Hforward.
    apply fold_ker_correct; eauto.
    intros s h [fc ?]; exists fc; repeat sep_cancel; eauto.
    intros s h H.
    repeat (apply ex_lift_l_in in H; destruct H as [? ?]).
    exists x x0; sep_normal; sep_normal_in H.
    repeat sep_cancel.
Qed.

Definition bid_pre (arr out : Z) (bid : Fin.t nblk) :=
  Ex v2 : Z,
   !(ARR === arr) **
   !(OUT === out) **
   conj_xs
     (ls_init 0 ntrd
        (fun i : nat => skip_arr (Gl arr) 0 len nt_gr f (i + nf bid * ntrd))) **
   (Gl out +o Zn (nf bid) -->p (1,  v2)).

Definition bid_post (arr out : Z) (bid : Fin.t nblk) :=
  (conj_xs
     (ls_init 0 ntrd
        (fun i : nat => skip_arr (Gl arr) 0 len nt_gr f (i + nf bid * ntrd))) **
   (Gl out +o Zn (nf bid) -->p (1,  sum_of 0 ntrd (f_ss' (nf bid))))).

Theorem fold_ker_correct_g (arr out : val) :
  nt_gr <= len ->
  CSLg ntrd nblk ntrd_neq_0 nblk_neq_0
  (Ex fout, 
   !(ARR === arr) ** !(OUT === out) **
   is_array (Gl arr) len f 0 ** is_array (Gl out) nblk fout 0)
  (Pr ((SARR, ntrd) :: List.nil) fold_ker') 
  (is_array (Gl arr) len f 0 ** is_array (Gl out) nblk (fun b => (sum_of 0 ntrd (f_ss' b))) 0).
Proof.
  intros Hlen.
  applys (>>rule_grid ty_env_fold (MyVector.init (bid_pre arr out)) (MyVector.init (bid_post arr out))).
  - intros s h [fout H].
    unfold bid_pre; istar_simplify.
    sep_split_in H.
    sep_rewrite (@ls_exists0 _ 0%Z); exists (ls_init 0 nblk fout); sep_split; eauto.
    rewrite init_length; reflexivity.
    repeat sep_rewrite (@ls_star); repeat sep_rewrite (@ls_pure); sep_split.
    + apply ls_emp'; rewrite init_length; intros; rewrite ls_init_spec; destruct lt_dec; eauto; omega.
    + apply ls_emp'; rewrite init_length; intros; rewrite ls_init_spec; destruct lt_dec; eauto; omega.
    + sep_rewrite_in (@is_array_skip_arr (Gl arr) nblk ntrd) H; try omega.
      sep_cancel.
      sep_rewrite is_array_distr; try omega.
      sep_rewrite is_array_change; eauto.
      intros; rewrite ls_init_spec; destruct lt_dec; eauto; try omega.
  - intros bid.
    unfold bid_pre, bid_post; simpl.
    rewrite @MyVector.init_spec.
    eapply CSLp_backward.
    eapply CSLp_forward.
    apply fold_correct_b; eauto.
    + simpl; intros s h H.
      rewrite MyVector.init_spec.
      repeat sep_cancel.
    + simpl; intros s h H.
      apply ex_lift_l_in in H; destruct H as [v H].
      exists v. repeat sep_cancel.
  - unfold bid_post; intros s h H.
    istar_simplify_in H.
    sep_rewrite (@is_array_skip_arr (Gl arr) nblk ntrd); try omega.
    sep_cancel.
    sep_rewrite_in is_array_distr H; try omega.
    sep_rewrite is_array_change; eauto.
  - simpl.
    prove_inde.
    Lemma inde_ex {T : Type} (P : T -> assn) vs :
      (forall x, inde (P x) vs) ->
      inde (Ex x, P x) vs.
    Proof.
      unfold inde.
      intros; simpl in *.
      split; intros [t ?]; exists t; simpl in *.
      rewrite <-H; auto.
      rewrite H; eauto.
    Qed.
    apply inde_ex; intros.
    prove_inde.
  - intros bid; unfold bid_pre.
    rewrite init_spec.
    apply inde_ex; intros.
    Require Import pmap.
    repeat prove_inde.
    apply (inde_conj_xs); try omega; intros.
    rewrite init_length in H.
    rewrite ls_init_spec; destruct lt_dec; try omega.
    unfold skip_arr.
    prove_inde.
  - unfold bid_pre; intros.
    rewrite MyVector.init_spec.
    repeat prove_low_assn; eauto using low_assn_skip_arr, low_assn_conj_xs.
    apply low_assn_conj_xs; rewrite init_length; intros.
    rewrite ls_init_spec; repeat prove_low_assn.
    eauto using low_assn_skip_arr.
    applys_eq ty_offset 1; eauto.
    instantiate (1:=Lo); instantiate (1:=Lo); reflexivity.
  - intros bid.
    unfold bid_post; rewrite MyVector.init_spec.
    repeat has_no_vars_assn.
    apply has_no_vars_conj_xs.
    rewrite init_length; intros; rewrite ls_init_spec.
    repeat has_no_vars_assn.
    apply has_no_vars_skip_arr; cbv; auto.
  - simpl; intros v [? | [ ] ].
    subst; cbv; auto.
  - auto.
  - auto.
  - cbv; destruct 1; try congruence.
  - cbv; destruct 1; try congruence.
  - cbv; eauto.
Qed.
End Fold.