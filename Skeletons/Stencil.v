Require Import GPUCSL.
Require Import scan_lib.
Require Import LibTactics Psatz.

Section Stencil.
Coercion Var : string >-> var.
Variable ntrd nblk : nat.
Hypothesis ntrd_neq_0 : ntrd <> 0.
Hypothesis nblk_neq_0 : nblk <> 0.
Open Scope string_scope.
Local Notation gid := ("tid" +C "bid" *C Zn ntrd).

Definition stencil :=
  "t0" ::= [Gl "arr" +o gid] ;;
  [Sh "smem" +o ("tid" +C 1%Z)] ::= "t0" ;;
  Cif ("tid" == 0%Z) (
    Cif ("bid" == 0%Z) ([Sh "smem" +o 0%Z] ::= 0%Z)
    ( "t0" ::= [Gl "arr" +o (gid -C 1%Z)];; [Sh "smem" +o 0%Z] ::= "t0" )
  ) (Cskip
  ) ;;
  Cif ("tid" == Zn ntrd -C 1%Z) (
    Cif ("bid" == Zn nblk -C 1%Z) ([Sh "smem" +o (Zn ntrd +C 1%Z)] ::= 0%Z)
    ( "t0" ::= [Gl "arr" +o (gid +C 1%Z)];; [Sh "smem" +o (Zn ntrd +C 1%Z)] ::= "t0" )
  ) (Cskip
  ) ;;
  Cbarrier 0 ;;
  "t0" ::= [Sh "smem" +o "tid"] ;;
  "t1" ::= [Sh "smem" +o ("tid" +C 1%Z)] ;;
  "t2" ::= [Sh "smem" +o ("tid" +C 2%Z)] ;;
  [Gl "out" +o gid] ::= "t0" +C "t1" +C "t2".

Variable aloc : Z.
Variable sloc : Z.
Variable oloc : Z.
Local Notation nt_gr := (nblk * ntrd).
Notation perm_n n := (1 / injZ (Zn n))%Qc.
Variable f : nat -> Z.
Variable f_out : nat -> Z.

Definition f' k := if Sumbool.sumbool_or _ _ _ _ (le_dec k 0) (lt_dec nt_gr k) then 0%Z else f (k - 1).

Notation gi i j := (nf i + nf j * ntrd).

Definition BS0 (j : Fin.t nblk)  : (Vector.t assn ntrd * Vector.t assn ntrd) := 
  (MyVector.init (fun i =>
    (Sh "smem" +o Zn (nf i + 1) -->p (1, f' (gi i j + 1))) **
    (if Nat.eq_dec (nf i) 0 then Sh "smem" -->p (1, f' ((nf j) * ntrd)) else emp) **
    (if Nat.eq_dec (nf i) (ntrd - 1) then Sh "smem" +o Zn (ntrd + 1) -->p (1, f' ((nf j + 1) * ntrd + 1)) else emp)),
   MyVector.init (fun i =>
    is_array_p (Sh "smem") (ntrd + 2) (fun k => f' (k + nf j * ntrd)) 0 (perm_n ntrd))).

Definition BS (j : Fin.t nblk) (n : nat) :=
  if Nat.eq_dec n 0 then BS0 j else default ntrd.

Lemma stencil_ok_th (f_sm : nat -> Z) (j : Fin.t nblk) (i : Fin.t ntrd) :
  CSL (BS j) i 
    (!("tid" === Zn (nf i)) **
     !("bid" === Zn (nf j)) **
     !("arr" === aloc) **
     !("out" === oloc) **
     !("smem" === sloc ) **
     is_array_p (Gl aloc) nt_gr f 0 (perm_n nt_gr) **
     (Gl oloc +o Zn (nf i + nf j * ntrd) -->p (1, f_out (nf i + nf j * ntrd))) **
     (Sh "smem" +o Zn (nf i + 1) -->p (1, f_sm (nf i + 1))) **
     (if Nat.eq_dec (nf i) 0 then Sh "smem" -->p (1, f_sm 0) else emp) **
     (if Nat.eq_dec (nf i) (ntrd - 1) then Sh "smem" +o Zn (ntrd + 1) -->p (1, f_sm (ntrd + 1)) else emp))
    stencil 
    (is_array_p (Gl aloc) nt_gr f 0 (perm_n nt_gr) **
     (Gl oloc +o Zn (gi i j) -->p (1, (f' (gi i j) + f' (gi i j + 1) + f' (gi i j + 2)))%Z) **
     is_array_p (Sh "smem") (ntrd + 2) (fun k => f' (k + nf j * ntrd)) 0 (perm_n ntrd)).
Proof.
  assert (Hgi_nt: gi i j < nt_gr) by eauto.
  unfold stencil.
  eapply Hbackward.
  Focus 2. {
    intros s h H.
    sep_rewrite_in (@is_array_unfold (Gl aloc) (gi i j)) H; [|eauto].
    autorewrite with sep in H; sep_normal_in H.
    assert (Heq : (Gl aloc +o (Zn (gi i j)) ===l Gl "arr" +o gid) s (emp_ph loc)).
    { sep_split_in H; unfold_conn; simpl; f_equal; unfold_pures; clear H; nia. }
    sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
    assert (Heq : (Sh "smem" +o (Zn (nf i + 1)) ===l Sh "smem" +o ("tid" +C 1%Z)) s (emp_ph loc)).
    { sep_split_in H; unfold_conn; simpl; f_equal; unfold_pures; clear H; nia. }
    sep_lift_in H 9.
    sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
    apply H.
  } Unfocus.
  eapply rule_seq; [hoare_forward; eauto|].
  eapply rule_seq; [hoare_forward; eauto|].
  eapply rule_seq.
  hoare_forward; eauto using rule_skip.
  { hoare_forward; eauto.
    { eapply Hbackward.
      Focus 2. {
        intros s h H; sep_split_in H.
        change_in H.
        { unfold_pures; destruct Nat.eq_dec; try omega.
          assert (Heq : (Sh "smem" ===l Sh "smem" +o 0%Z) s (emp_ph loc)).
          { sep_split_in H; unfold_conn; simpl; f_equal; unfold_pures; clear H; nia. }
          sep_lift_in H 5.
          sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
          apply H. }
        sep_combine_in H; apply H. } Unfocus.
      hoare_forward; eauto. }
    { eapply Hbackward.
      Focus 2. {
        intros s h H; sep_split_in H.
        change_in H.
        { unfold_pures; destruct Nat.eq_dec; try omega.
          assert (Heq : (Sh "smem" ===l Sh "smem" +o 0%Z) s (emp_ph loc)).
          { sep_split_in H; unfold_conn; simpl; f_equal; unfold_pures; clear H; nia. }
          sep_lift_in H 5.
          sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
          sep_rewrite_in (@is_array_unfold (Gl aloc) (gi i j - 1)) H; [|eauto; clear H; nia].
          sep_normal_in H.
          assert (Heq : (Gl aloc +o (Zn (gi i j - 1 + 0)) ===l Gl "arr" +o (gid -C 1%Z) ) s (emp_ph loc)).
          { sep_split_in H; unfold_conn; simpl; f_equal; unfold_pures; clear H; nia. }
          sep_lift_in H 4.
          sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
          assert (Heq : ("t0" === f (gi i j)) s (emp_ph loc)).
          { unfold_pures; unfold_conn; eauto. }
          sep_lift_in H 2.
          sep_rewrite_in mps_eq2 H; [|exact Heq].
          apply H. }
        clear HP1.
        sep_combine_in H; apply H. } Unfocus. 
      eapply rule_seq; [hoare_forward; eauto|].
      hoare_forward; eauto. } }
  eapply Hbackward.
  Focus 2. {
    instantiate (1 :=
     !("tid" === Zn (nf i)) **
     !("bid" === Zn (nf j)) **
     !("arr" === aloc) **
     !("out" === oloc) **
     !("smem" === sloc ) **
     is_array_p (Gl aloc) nt_gr f 0 (perm_n nt_gr) **
     (Gl oloc +o Zn (nf i + nf j * ntrd) -->p (1, f_out (nf i + nf j * ntrd))) **
     (Sh "smem" +o ("tid" +C 1%Z) -->p (1, f' (gi i j + 1))) **
     (if Nat.eq_dec (nf i) 0 then Sh "smem" -->p (1, f' (nf j * ntrd)) else emp) **
     (if Nat.eq_dec (nf i) (ntrd - 1) then Sh "smem" +o Zn (ntrd + 1) -->p (1, f_sm (ntrd + 1)) else emp)).
    intros s h H; sep_rewrite (@is_array_unfold (Gl aloc) (gi i j)); [|eauto].
    sep_normal; sep_cancel.
    destruct H as [[H | H] | H]; sep_split_in H; sep_split; eauto; sep_cancel.
    { unfold_pures.
      destruct (Nat.eq_dec (nf i) 0);  [|clear H H0; nia].
      assert (Heq : (Gl aloc +o (Zn (gi i j + 0)) ===l Gl "arr" +o gid) s (emp_ph loc)).
      { sep_split_in H; unfold_conn; simpl; f_equal; unfold_pures; clear H H0; nia. }
      sep_rewrite mps_eq1; [|exact Heq]; clear Heq.
      rewrite <-plus_n_O.
      repeat sep_cancel.
      unfold f'; lazymatch goal with [|- context [if ?X then _ else _]] => destruct X end; try nia.
      lazymatch goal with [|- context [if ?X then _ else _]] => destruct X end; try nia.
      assert (Heq : ("t0" === f (gi i j)) s (emp_ph loc)).
      { unfold_pures; unfold_conn; eauto. }
      rewrite Nat.add_sub.
      sep_lift_in H3 1.
      sep_rewrite_in mps_eq2 H3; [|exact Heq].
      repeat sep_cancel. }
    { unfold_pures.
      destruct (Nat.eq_dec (nf i) 0); [|clear H H0; nia].
      assert (Heq : (Gl aloc +o (Zn (gi i j + 0)) ===l Gl "arr" +o gid) s (emp_ph loc)).
      { sep_split_in H; unfold_conn; simpl; f_equal; unfold_pures; clear H H0; nia. }
      sep_rewrite mps_eq1; [|exact Heq]; clear Heq.
      rewrite <-plus_n_O.
      repeat sep_cancel.
      sep_rewrite (@is_array_unfold (Gl aloc) (gi i j - 1)); [|eauto; clear H H0 H1 H2; nia].
      sep_normal.
      assert (Heq : (Gl aloc +o (Zn (gi i j - 1 + 0)) ===l Gl "arr" +o ("tid" +C "bid" *C Zn ntrd -C 1%Z)) s (emp_ph loc)).
      { sep_split_in H; unfold_conn; simpl; f_equal; unfold_pures; clear H H0 H1 H2; nia. }
      sep_rewrite mps_eq1; [|exact Heq]; clear Heq.
      repeat sep_cancel.
      unfold f'; lazymatch goal with [|- context [if ?X then _ else _]] => destruct X end;
        [clear H H0 H1 H2 H3 H4 H5; nia|].
      lazymatch goal with [|- context [if ?X then _ else _]] => destruct X end;
        [clear H H0 H1 H2 H3 H4 H5; nia|].
      rewrite Nat.add_sub.
      assert (Heq : ("t0" === f (gi i j - 1 + 0)) s (emp_ph loc)).
      { unfold_pures; unfold_conn; eauto. }
      sep_rewrite_in mps_eq2 H5; [|exact Heq].
      cutrewrite (nf j * ntrd - 1 = gi i j - 1 + 0); [|clear H H0 H1 H2 H3 H4 H5; nia].
      repeat sep_cancel. }
    { unfold_pures.
      destruct (Nat.eq_dec (nf i) 0); [clear H H0; nia|].
      sep_rewrite emp_unit_l; sep_rewrite_in emp_unit_l H0.
      assert (Heq : (Gl aloc +o (Zn (gi i j + 0)) ===l Gl "arr" +o gid) s (emp_ph loc)).
      { sep_split_in H; unfold_conn; simpl; f_equal; unfold_pures; clear H H0; nia. }
      sep_rewrite mps_eq1; [|exact Heq]; clear Heq.
      rewrite <-plus_n_O.
      repeat sep_cancel.
      assert (Heq : ("t0" === f (gi i j)) s (emp_ph loc)).
      { unfold_pures; unfold_conn; eauto. }
      sep_rewrite_in mps_eq2 H3; [|exact Heq].
      unfold f'; lazymatch goal with [|- context [if ?X then _ else _]] => destruct X end;
        [clear H H0 H1 H2 H3; nia|].
      rewrite Nat.add_sub.
      sep_cancel. } } Unfocus.
  eapply rule_seq.
  hoare_forward; eauto using rule_skip.
  { eapply Hbackward.
    Focus 2. {
        intros s h H; sep_split_in H.
        change_in H.
        { unfold_pures; destruct (Nat.eq_dec _ (ntrd - 1)); [|clear H; false; nia].
          assert (Heq : (Sh "smem" +o Zn (ntrd + 1) ===l Sh "smem" +o (Zn ntrd +C 1%Z)) s (emp_ph loc)).
          { sep_split_in H; unfold_conn; simpl; f_equal; unfold_pures; clear H; nia. }
          sep_lift_in H 5.
          sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
          apply H. }
        sep_combine_in H; apply H. } Unfocus.
    hoare_forward; eauto.
    hoare_forward; eauto.
    { eapply Hbackward.
      Focus 2. {
        intros s h H; sep_split_in H.
        change_in H.
        { unfold_pures.
          sep_rewrite_in (@is_array_unfold (Gl aloc) (gi i j + 1)) H; [|eauto; clear H; nia].
          sep_normal_in H.
          assert (Heq : (Gl aloc +o (Zn (gi i j + 1 + 0)) ===l Gl "arr" +o (gid +C 1%Z) ) s (emp_ph loc)).
          { sep_split_in H; unfold_conn; simpl; f_equal; unfold_pures; clear H; nia. }
          sep_lift_in H 2.
          sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
          apply H. }
        sep_combine_in H; apply H. } Unfocus. 
      eapply rule_seq; [hoare_forward; eauto|].
      hoare_forward; eauto. } }

  eapply Hbackward.
  Focus 2. {
    instantiate (1 :=
     !("tid" === Zn (nf i)) **
     !("bid" === Zn (nf j)) **
     !("arr" === aloc) **
     !("out" === oloc) **
     !("smem" === sloc ) **
     is_array_p (Gl aloc) nt_gr f 0 (perm_n nt_gr) **
     (Gl oloc +o Zn (nf i + nf j * ntrd) -->p (1, f_out (nf i + nf j * ntrd))) **
     (Sh "smem" +o ("tid" +C 1%Z) -->p (1, f' (gi i j + 1))) **
     (if Nat.eq_dec (nf i) 0 then Sh "smem" -->p (1, f' (nf j * ntrd)) else emp) **
     (if Nat.eq_dec (nf i) (ntrd - 1) then Sh "smem" +o Zn (ntrd + 1) -->p (1, f' ((nf j + 1) * ntrd + 1)) else emp)).
    intros s h H; sep_normal.
    destruct H as [[H | H] | H]; sep_split_in H; sep_split; eauto; repeat sep_cancel.
    { unfold_pures.
      destruct (Nat.eq_dec _ (ntrd - 1)); [|clear H H0 H1 H2; false; nia].
      assert (Heq : (Sh "smem" +o (Zn ntrd +C 1%Z) ===l Sh "smem" +o Zn (ntrd + 1)) s (emp_ph loc)).
      { sep_split_in H; unfold_conn; simpl; f_equal; unfold_pures; clear H H0 H1 H2 H3; nia. }
      sep_rewrite_in mps_eq1 H3; [|exact Heq]; clear Heq.
      unfold f'; lazymatch goal with [|- context [if ?X then _ else _]] => destruct X end; try (false; nia).
      apply H3. }
    { unfold_pures.
      sep_rewrite (@is_array_unfold (Gl aloc) (gi i j + 1)); [|eauto; clear H H0 H1 H2; nia].
      sep_normal.
      assert (Heq : (Gl aloc +o (Zn (gi i j + 1 + 0)) ===l Gl "arr" +o (gid +C 1%Z) ) s (emp_ph loc)).
      { sep_split_in H; unfold_conn; simpl; f_equal; unfold_pures; clear H; nia. }
      sep_lift 1.
      sep_rewrite mps_eq1; [|exact Heq]; clear Heq.
      repeat sep_cancel.
      destruct (Nat.eq_dec _ (ntrd - 1)); [|clear H0 H1 H2 H3 H4 H5; nia].
      unfold f'; lazymatch goal with [|- context [if ?X then _ else _]] => destruct X end; try (false; nia).
      rewrite Nat.add_sub.
      assert (Heq : ("t0" === f ((nf j + 1) * ntrd)) s (emp_ph loc)).
      { unfold_pures; unfold_conn; simpl; rewrite HP; f_equal; nia. }
      sep_rewrite_in mps_eq2 H5; [|exact Heq]; clear Heq.
      assert (Heq : (Sh "smem" +o (Zn ntrd +C 1%Z) ===l Sh "smem" +o Zn (ntrd + 1)) s (emp_ph loc)).
      { sep_split_in H; unfold_conn; simpl; f_equal; unfold_pures; clear H H0 H1 H2 H3 H4 H5; nia. }
      sep_rewrite_in mps_eq1 H5; [|exact Heq]; clear Heq.
      apply H5. }
    { unfold_pures.
      destruct (Nat.eq_dec _ (ntrd - 1)); [clear H H0 H1 H2 H3; nia|]; eauto.  } } Unfocus.
  eapply rule_seq.
  (* The following tactics cannot be replaced with hoare_forward
  because of a buggy behavior of tauto used by hoare_forward. tauto
  removes useless hypothesis for proving the goal, and when the goal
  contains some unification variables, it can't look removed
  hypothesis. *)
  idtac "called"; eapply Hforward;
         [ eapply Hbackward;
            [ eapply rule_frame; [ apply rule_barrier | split; simpl in *; destruct H]
            | autounfold ; simpl; repeat rewrite MyVector.init_spec in * ]
         | idtac ]; eauto.
  { intros s h H.

    sep_split_in H.
    sep_normal.
    change_in H.    
    { unfold_pures.
      assert (Heq : (Sh "smem" +o ("tid" +C 1%Z) ===l Sh "smem" +o (Zn (nf i + 1)) ) s (emp_ph loc)).
      { unfold_conn; simpl; f_equal; clear H; unfold lt; nia. }
      sep_lift_in H 2.
      sep_rewrite_in mps_eq1 H; [|apply Heq]; clear Heq.
      (* assert (Heq : s ||= (if Nat.eq_dec (nf i) 0 then Sh "smem" -->p (1,  f' (nf j * ntrd)) else emp) <=> *)
      (*                     (if Nat.eq_dec (nf i) 0 then Sh "smem" -->p (1,  f' (nf j * ntrd)) else emp)). *)
      (* { destruct (Nat.eq_dec _ 0); try reflexivity.  *)
      (* sep_rewrite_in Heq H; clear Heq. *)
      (* assert (Heq : s ||= *)
      (*   (if Nat.eq_dec (nf i) (ntrd - 1) then Sh "smem" +o Zn (ntrd + 1) -->p (1,  f' ((nf j + 1) * ntrd + 1)) else emp) *)
      (*   <=> *)
      (*   (if Nat.eq_dec (nf i) (ntrd - 1) then Sh sloc +o Zn (ntrd + 1) -->p (1,  f' ((nf j + 1) * ntrd + 1)) else emp)). *)
      (* { destruct (Nat.eq_dec _ (ntrd - 1)); try reflexivity. *)
      (*   apply mps_eq1; unfold_conn; simpl; f_equal; nia. } *)
      (* sep_rewrite_in Heq H; clear Heq. *)
      apply H. }
    sep_normal_in H0; do 2 sep_cancel.
    sep_lift_in H 2; revert H; apply scRw_stack; [intros ? H'; apply H'| intros ? ?].
    sep_lift_in H 2; revert H; apply scRw_stack; [intros ? H'; apply H'| intros ? ?].
    sep_combine_in H. apply H. }
  unfold BS at 2, BS0; simpl; rewrite MyVector.init_spec.
  eapply Hbackward.
  Focus 2. { 
    intros s h H.
    sep_split_in H.
    sep_rewrite_in (@is_array_unfold (Sh "smem") (nf i)) H; [|destruct (Fin.to_nat i); clear H; simpl; omega].
    sep_normal_in H.
    sep_lift_in H 2; sep_rewrite_in (@is_array_unfold (Sh "smem") 0) H; [|destruct (Fin.to_nat i); clear H; simpl; omega].
    sep_normal_in H.
    sep_lift_in H 2; sep_rewrite_in (@is_array_unfold (Sh "smem") 0) H; [|destruct (Fin.to_nat i); clear H; simpl; omega].
    sep_normal_in H.
    change_in H.
    { unfold_pures.
      assert (Heq : (Sh "smem" +o Zn (0 + S (0 + S (nf i + 0))) ===l Sh "smem" +o ("tid" +C 2%Z)) s (emp_ph loc)).
      { rewrite !plus_O_n, <-plus_n_O, !Nat2Z.inj_succ, <-!Z.add_1_r.
        unfold_conn; simpl; f_equal; clear H; unfold lt; omega. }
      sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
      assert (Heq : (Sh "smem" +o Zn (0 + S (nf i + 0)) ===l Sh "smem" +o ("tid" +C 1%Z)) s (emp_ph loc)).
      { rewrite !plus_O_n, <-plus_n_O, !Nat2Z.inj_succ, <-!Z.add_1_r.
        unfold_conn; simpl; f_equal; clear H; unfold lt; omega. }
      sep_lift_in H 4; sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
      assert (Heq : (Sh "smem" +o Zn (nf i + 0) ===l Sh "smem" +o "tid") s (emp_ph loc)).
      { unfold_conn; simpl; f_equal; clear H; unfold lt in *; nia. }
      sep_lift_in H 6; sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
      assert (Heq : (Gl oloc +o Zn (gi i j) ===l Gl "out" +o gid) s (emp_ph loc)).
      { unfold_conn; simpl; f_equal; clear H; unfold lt in *; nia. }
      sep_lift_in H 8; sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
      apply H. } 
    sep_combine_in H; apply H. } Unfocus.
  repeat (eapply rule_seq; [hoare_forward; eauto|]).
  eapply Hforward; [hoare_forward; eauto|].
  intros s h H.
  sep_split_in H; sep_cancel.
  unfold_pures.
  sep_rewrite (@is_array_unfold (Sh "smem") (nf i)); [|destruct (Fin.to_nat i); clear H; simpl; omega].
  sep_normal.
  sep_lift 3; sep_rewrite (@is_array_unfold (Sh "smem") 0); [|destruct (Fin.to_nat i); clear H; simpl; omega].
  sep_normal.
  sep_lift 2. sep_rewrite (@is_array_unfold (Sh "smem") 0). 2: destruct (Fin.to_nat i). 2: clear H H0. 2: simpl.
  2: generalize dependent x. 2: clear. 2: intros. 2: omega.
  sep_normal_in H0. clear H. sep_normal.
  assert (Heq : (Sh "smem" +o Zn (0 + S (0 + S (nf i + 0))) ===l Sh "smem" +o ("tid" +C 2%Z)) s (emp_ph loc)).
  { rewrite !plus_O_n, <-plus_n_O, !Nat2Z.inj_succ, <-!Z.add_1_r.
    unfold_conn; simpl; f_equal; unfold lt; omega. }
  sep_rewrite mps_eq1; [|exact Heq]; clear Heq.
  assert (Heq : (Sh "smem" +o Zn (0 + S (nf i + 0)) ===l Sh "smem" +o ("tid" +C 1%Z)) s (emp_ph loc)).
  { rewrite !plus_O_n, <-plus_n_O, !Nat2Z.inj_succ, <-!Z.add_1_r.
    unfold_conn; simpl; f_equal; unfold lt; omega. }
  sep_lift 4; sep_rewrite mps_eq1; [|exact Heq]; clear Heq.
  assert (Heq : (Sh "smem" +o Zn (nf i + 0) ===l Sh "smem" +o "tid") s (emp_ph loc)).
  { unfold_conn; simpl; f_equal; clear H0; unfold lt in *. nia. }
  sep_lift 7; sep_rewrite mps_eq1; [|exact Heq]; clear Heq.
  assert (Heq : (Gl oloc +o Zn (gi i j) ===l Gl "out" +o gid) s (emp_ph loc)).
  { unfold_conn; simpl; f_equal; clear H0; unfold lt in *; nia. }
  sep_lift 6; sep_rewrite mps_eq1; [|exact Heq]; clear Heq.
  assert (Heq : ((f' (gi i j) + f' (gi i j + 1))%Z +C f' (gi i j + 2) ===
                 "t0" +C "t1" +C "t2") s (emp_ph loc)).
  { unfold_conn; simpl.
    do 2 f_equal; try rewrite HP; try rewrite HP0; try rewrite HP1; f_equal; try omega. }
  sep_rewrite mps_eq2; [|exact Heq]; clear Heq.
  repeat sep_cancel.
Qed.

Require Import Bdiv.

Lemma is_array_distr e n (f' : nat -> Z) :
  forall m s stk,
    stk ||= conj_xs (ls_init m n (fun i => e +o Zn (i + s) -->p (1, f' (i + s)))) <=>
        is_array e n f' (m + s).
Proof.
  induction n; intros m s stk; simpl.
  - reflexivity.
  - rewrite IHn; reflexivity.
Qed.

Lemma is_array_distr0 e n (f' : nat -> Z) :
  forall s stk,
    stk ||= conj_xs (ls_init 0 n (fun i => e +o Zn (i + s) -->p (1, f' (i + s)))) <=>
        is_array e n f' s.
Proof.
  lets: (is_array_distr e n f' 0); simpl in *; eauto.
Qed.

Lemma is_array_distr00 e n (f' : nat -> Z) :
  forall stk,
    stk ||= conj_xs (ls_init 0 n (fun i => e +o Zn i -->p (1, f' i))) <=>
        is_array e n f' 0.
Proof.
  lets: (is_array_distr0 e n f' 0); simpl in *.
  erewrite ls_init_eq0 in H.
  2: intros; rewrite <-plus_n_O; reflexivity.
  eauto.
Qed.

Lemma is_array_change (e : loc_exp) (f1 f2 : nat -> Z) n :
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

Lemma is_array_concat e f' len1 len2 : forall s stc,
    (* (forall off, off < len1 + len2 -> *)
    (*  f' (s + off) = if lt_dec off len1 then f1 (s + off) else f2 (s + off)) -> *)
    stc||=
       is_array e (len1 + len2) f' s <=>
       is_array e len1 f' s ** is_array e len2 f' (s + len1).
Proof.
  induction len1; simpl; intros s stc.
  - rewrite emp_unit_l, <-plus_n_O.
    rewrite is_array_change; [reflexivity|..].
    intros; rewrite plus_comm; eauto.
  - intros. rewrite <-Nat.add_succ_comm, <-sep_assoc, IHlen1.
    reflexivity.
Qed.

Ltac istar_simplify_eq :=
  rewrite sc_v2l; rewrite (vec_to_list_init0 _ emp); erewrite ls_init_eq0;
   [ idtac
   | let i := fresh "i" in
     let Hi := fresh in
     let Hex := fresh in
     let Heq := fresh in
     intros i Hi;
      lazymatch goal with
      | |- match ?X with
           | inleft _ => _
           | inright _ => _
           end = _ => destruct X as [| Hex] eqn:Heq; [ idtac | destruct Hex; omega ]
      end; rewrite (Fin_nat_inv Heq); reflexivity ]; 
   match goal with
   | _ => idtac
   end.

Lemma dist_for_stencil l (f' : nat -> Z) stk : 
  stk ||= Aistar_v (MyVector.init
             (fun (i : Fin.t ntrd) => (Sh l +o Zn (nf i + 1) -->p (1,  f' (nf i + 1))) **
               (if Nat.eq_dec (nf i) 0 then Sh l -->p (1, f' 0) else emp) **
               (if Nat.eq_dec (nf i) (ntrd - 1) then (Sh l +o Zn (ntrd + 1)) -->p (1, f' (ntrd + 1)) else emp))) <=>
      is_array (Sh l) (ntrd + 2) f' 0.
Proof.
  istar_simplify_eq.
  cutrewrite (ntrd + 2 = 1 + ntrd + 1); [|ring].
  repeat rewrite is_array_concat.
  cutrewrite (0 + (1 + ntrd) = ntrd + 1); [|ring]; simpl.
  rewrite !emp_unit_r, <-!sep_assoc, !ls_star.
  rewrite is_array_distr0.

  rewrite <-(firstn_skipn 1 (ls_init _ _ _)), firstn_init, skipn_init, conj_xs_app.
  rewrite min_l; try omega.
  erewrite ls_init_eq'.
  2: intros; destruct Nat.eq_dec; try omega.
  2: lazymatch goal with [|- ?X = _ ?i] => cutrewrite (X = id (fun _ : nat => X) i); eauto end.
  unfold id; simpl; rewrite emp_unit_r.
  erewrite ls_init_eq'.
  2: intros; destruct Nat.eq_dec; try omega.
  2: lazymatch goal with [|- ?X = _ ?i] => cutrewrite (X = id (fun _ : nat => X) i); eauto end.
  rewrite init_emp_emp, emp_unit_r.

  rewrite <-(firstn_skipn (ntrd - 1) (ls_init _ _ _)), firstn_init, skipn_init, conj_xs_app.
  rewrite min_l; try omega.
  erewrite ls_init_eq'.
  2: intros; destruct Nat.eq_dec; try omega.
  2: lazymatch goal with [|- ?X = _ ?i] => cutrewrite (X = id (fun _ : nat => X) i); eauto end.
  cutrewrite (ntrd - (ntrd - 1) = 1); [|omega]; simpl.
  unfold id; simpl; rewrite init_emp_emp, !emp_unit_l, !emp_unit_r.
  destruct Nat.eq_dec; try omega.
  split; intros; repeat sep_cancel.
Qed.  

Lemma BS_ok j n: Aistar_v (fst (BS j n)) |= Aistar_v (snd (BS j n)).
Proof.
  unfold BS, BS0; destruct n; simpl; eauto.
  intros s h H.
  apply sc_v2l; rewrite (vec_to_list_init0 _ emp); erewrite ls_init_eq0.
  2: intros i Hi; destruct Fin.of_nat as [|[? ?]]; try omega.
  2: lazymatch goal with [|- ?X = _ ?i] => cutrewrite (X = id (fun _ : nat => X) i); eauto end.
  unfold id.
  sep_rewrite_r is_array_is_array_p_1; eauto.
  apply dist_for_stencil; eauto; simpl.
  istar_simplify.
  istar_simplify_in H.
  repeat sep_rewrite (@ls_star ntrd).
  repeat sep_cancel.
  erewrite ls_init_eq0; [apply scC; erewrite ls_init_eq0; [apply scC|]|]; eauto.
  intros; destruct Nat.eq_dec; do 3 f_equal; eauto; nia.
  intros; simpl; do 3 f_equal; omega.
Qed.

Lemma precise_pts : forall (e1 : loc_exp) (e2 : exp) (q : Qc), precise (e1 -->p (q,  e2)).
Proof.
  intros; unfold precise; simpl; intros; unfold_conn_all.
  destruct h1, h1'; apply pheap_eq; extensionality x; simpl in *.
  rewrite H, H0; destruct (eq_dec _ _); eauto.
Qed.

Lemma precise_is_array_p e len s f' p : precise (is_array_p e len f' s p).
Proof.
  revert s; induction len; simpl; intros; eauto using precise_emp, precise_star, precise_pts.
Qed.  

Lemma precise_BS b j i :
  precise (Vector.nth (fst (BS j b)) i) /\
  precise (Vector.nth (snd (BS j b)) i).
Proof.
  split; unfold BS, BS0; destruct b; simpl; rewrite MyVector.init_spec;
    try now idtac.
  - repeat destruct Nat.eq_dec; repeat apply precise_star; eauto using precise_pts, precise_emp, precise_is_array_p.
  - repeat destruct Nat.eq_dec; repeat apply precise_star; eauto using precise_pts, precise_emp, precise_is_array_p.
Qed.

Definition Pre_ij (f_sm : nat -> Z)  (j : Fin.t nblk)  (i : Fin.t ntrd) :=
  !("bid" === Zn (nf j)) **
  !("arr" === aloc) **
  !("out" === oloc) **
  !("smem" === sloc ) **
  is_array_p (Gl aloc) nt_gr f 0 (perm_n nt_gr) **
  (Gl oloc +o Zn (nf i + nf j * ntrd) -->p (1, f_out (nf i + nf j * ntrd))) **
  (Sh "smem" +o Zn (nf i + 1) -->p (1, f_sm (nf i + 1))) **
  (if Nat.eq_dec (nf i) 0 then Sh "smem" -->p (1, f_sm 0) else emp) **
  (if Nat.eq_dec (nf i) (ntrd - 1) then Sh "smem" +o Zn (ntrd + 1) -->p (1, f_sm (ntrd + 1)) else emp).

Definition Post_ij (j : Fin.t nblk) (i : Fin.t ntrd) :=
  (is_array_p (Gl aloc) nt_gr f 0 (perm_n nt_gr) **
  (Gl oloc +o Zn (gi i j) -->p (1, (f' (gi i j) + f' (gi i j + 1) + f' (gi i j + 2)))%Z) **
  is_array_p (Sh "smem") (ntrd + 2) (fun k => f' (k + nf j * ntrd)) 0 (perm_n ntrd)).

Definition Pre_j (j : Fin.t nblk) :=
  !("arr" === aloc) **
  !("out" === oloc) **
  !("smem" === sloc ) **
  conj_xs (ls_init 0 ntrd (fun (i : nat) => is_array_p (Gl aloc) nt_gr f 0 (perm_n nt_gr))) **
  conj_xs (ls_init 0 ntrd (fun (i : nat) =>
                             (Gl oloc +o Zn (i + nf j * ntrd) -->p (1, f_out (i + nf j * ntrd))))).

Close Scope exp_scope.

Definition Post_j (j : Fin.t nblk) :=
  conj_xs (ls_init 0 ntrd (fun i : nat => (is_array_p (Gl aloc) nt_gr f 0 (perm_n nt_gr)))) **
  conj_xs (ls_init 0 ntrd (fun i : nat =>
    (Gl oloc +o Zn (i + nf j * ntrd) -->p (1, (f' (i + nf j * ntrd) + f' (i + nf j * ntrd + 1) + f' (i + nf j * ntrd + 2))%Z)))).

Definition E (v : var) :=
  if var_eq_dec v "tid" then Hi
  else if var_eq_dec v "t0" then Hi
  else if var_eq_dec v "t1" then Hi
  else if var_eq_dec v "t2" then Hi
  else Lo.

Lemma stencil_ok_bl (f_sm : nat -> Z) (j : Fin.t nblk) :
  CSLp ntrd E
       (!("bid" === Zn (nf j)) ** is_array (Sh "smem") (ntrd + 2) f_sm 0 ** Pre_j j)
       stencil
       (is_array (Sh "smem") (ntrd + 2) (fun k => f' (k + nf j * ntrd)) 0 ** Post_j j).
Proof.
  applys (>>(@rule_par) (BS j) (MyVector.init (Pre_ij f_sm j)) (MyVector.init (Post_ij j))).
  - destruct ntrd; eexists; try omega; eauto.
  - unfold BS, BS0; intros n; split; intros; destruct n; simpl; rewrite MyVector.init_spec; simpl; unfold CSL.low_assn;
      repeat prove_low_assn; repeat econstructor; [equates 1; [repeat econstructor|]..].
    repeat instantiate (1 := Lo); eauto.
    repeat instantiate (1 := Lo); eauto.
  - eauto using BS_ok.
  - eauto using precise_BS.
  - unfold Pre_j, Pre_ij; intros s h H; istar_simplify.
    repeat first [sep_rewrite (@ls_star ntrd) | sep_rewrite (@ls_pure ntrd)].
    sep_split_in H; sep_split;
      try (apply ls_emp'; rewrite init_length; intros; rewrite ls_init_spec; destruct lt_dec; try omega; eauto).
    repeat sep_cancel.
    apply dist_for_stencil in H1; istar_simplify_in H1; eauto.
  - unfold Post_j, Post_ij; intros s h H; istar_simplify_in H.
    repeat sep_cancel.
    sep_rewrite_in_r is_array_is_array_p_1 H0; repeat sep_cancel.
  - intros; unfold CSL.low_assn, Pre_ij; rewrite MyVector.init_spec; repeat prove_low_assn; repeat econstructor;
      [equates 1; [repeat econstructor|]..].
    repeat (instantiate (1 := Lo)); eauto.
    repeat (instantiate (1 := Lo)); eauto.
    repeat (instantiate (1 := Lo)); eauto.
  - intros; unfold CSL.low_assn, Post_ij; rewrite MyVector.init_spec; repeat prove_low_assn; repeat econstructor;
      [equates 1; [repeat econstructor|]..].
    repeat (instantiate (1 := Lo)); eauto.
    repeat (instantiate (1 := Lo)); eauto.
  - unfold E, stencil.
    instantiate (1 := Lo).
    repeat econstructor; simpl; repeat (repeat instantiate (1 := Hi); auto).
    repeat instantiate (1 := Hi); auto.    
    repeat instantiate (1 := Hi); auto.
    repeat instantiate (1 := Hi); auto.
    repeat instantiate (1 := Hi); auto.
  - intros; eapply rule_conseq; eauto using stencil_ok_th;
    unfold Pre_ij, Post_ij; rewrite MyVector.init_spec; intros; sep_normal_in H; sep_normal; repeat sep_cancel; eauto.
    Grab Existential Variables.
    exact 0.
Qed.

Lemma low_eq_trans E x y z : low_eq E x y -> low_eq E y z -> low_eq E x z.
Proof.
  unfold low_eq; intros; intuition.
  rewrite H, H0; eauto.
Qed.
  
Lemma rule_ex_p n T E P C Q :
  n <> 0 ->
  (forall x, low_assn E (P x)) ->
  (forall x : T, CSLp n E (P x) C Q) ->
  CSLp n E (Ex x : T, P x) C Q.
Proof.
  unfold CSLp; intros.
  unfold sat_k in H4.
  destruct low_eq_repr; destruct H4 as [t H4].
  forwards: (H1 t); eauto.
  unfold sat_k; destruct low_eq_repr.
  unfold low_assn, indeP in H0.
  erewrite H0; eauto.
  destruct n; try omega.
  specialize (l Fin.F1); specialize (l0 Fin.F1).
  apply low_eq_sym in l0.
  eapply low_eq_trans; eauto.
  Grab Existential Variables.
  eauto.
Qed.

Lemma stencil_ok_gr :
  CSLg ntrd nblk
       (!("arr" === aloc) **
        !("out" === oloc) **
        !("smem" === sloc ) **
        is_array (Gl aloc) nt_gr f 0 **
        is_array (Gl oloc) nt_gr f_out 0)
       {| get_sh_decl := (Var "smem", ntrd+2) :: nil; get_cmd := stencil |}
       (is_array (Gl aloc) nt_gr f 0 **
        is_array (Gl oloc) nt_gr (fun i => (f' i + f' (i + 1) + f' (i + 2))%Z) 0).
Proof.
  applys (>>rule_grid E (MyVector.init Pre_j) (MyVector.init Post_j)); try now (simpl; eauto).
  - unfold Pre_j; intros.
    istar_simplify.
    repeat first [sep_rewrite (@ls_star nblk) | sep_rewrite (@ls_pure nblk)].
    sep_split_in H; sep_split;
      try (apply ls_emp'; rewrite init_length; intros; rewrite ls_init_spec; destruct lt_dec; try omega; eauto).
    sep_rewrite (conj_xs_init_flatten0 nblk ntrd (fun v => Gl oloc +o Zn v -->p (1, f_out v))).
    sep_rewrite (conj_xs_init_flatten0 nblk ntrd (fun v => is_array_p (Gl aloc) nt_gr f 0 (perm_n nt_gr))).
    sep_rewrite_r is_array_is_array_p_1; try nia.
    sep_rewrite is_array_distr00; try nia.
    eauto.
  - simpl; intros.
    eapply CSLp_backward.
    Focus 2. {
      intros; sep_lift_in H 1.
      sep_rewrite_in emp_unit_r H.
      apply ex_lift_l_in in H. eauto. } Unfocus.
    apply rule_ex_p; eauto.
    intros; unfold Pre_j.
    rewrite MyVector.init_spec.
    unfold E; repeat prove_low_assn;
      lazymatch goal with
        [|- context [typing_exp _ _ _ ]] => repeat econstructor
      | [|- context [typing_lexp _ _ _ ]] => repeat econstructor
      | _ => idtac end;
    apply low_assn_conj_xs; intros;
    rewrite init_length in H;
    rewrite ls_init_spec; destruct lt_dec; try omega;
    repeat prove_low_assn;       lazymatch goal with
        [|- context [typing_exp _ _ _ ]] => repeat econstructor
      | [|- context [typing_lexp _ _ _ ]] => repeat econstructor
      | _ => idtac end.
    equates 1; [repeat econstructor|].
    repeat instantiate (1 := Lo); auto.
    intros f_sm.
    eapply CSLp_backward; [eapply CSLp_forward; [apply stencil_ok_bl|]|];
    unfold Pre_j, Post_j; try rewrite MyVector.init_spec; intros s h H.
    + sep_rewrite emp_unit_r; apply ex_lift_l; eexists.
      repeat sep_cancel; eauto.
    + repeat sep_cancel; eauto.
  - unfold Post_j; intros.
    istar_simplify_in H.
    sep_rewrite_in (conj_xs_init_flatten0 nblk ntrd (fun v => is_array_p (Gl aloc) nt_gr f 0 (perm_n nt_gr))) H.
    sep_rewrite_in_r is_array_is_array_p_1 H; try nia.
    sep_rewrite_in (conj_xs_init_flatten0 nblk ntrd (fun v =>
               Gl oloc +o Zn v -->p (1, (f' v + f' (v + 1))%Z +C f' (v + 2)))) H.
    sep_rewrite_in (is_array_distr00 (Gl oloc) nt_gr (fun i => (f' i + f' (i + 1) + f' (i + 2))%Z)) H; try nia.
    eauto.
  - unfold stencil; simpl.
    repeat prove_inde.
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
    apply inde_ex; intros; prove_inde.
  - intros; unfold Pre_j; rewrite MyVector.init_spec; prove_inde; apply inde_conj_xs;
    intros i; rewrite init_length, ls_init_spec; destruct lt_dec; try omega; intros; prove_inde.
  - unfold E; intros; unfold Pre_j; rewrite MyVector.init_spec; repeat prove_low_assn;
      lazymatch goal with
        [|- context [typing_exp _ _ _ ]] => repeat econstructor
      | [|- context [typing_lexp _ _ _ ]] => repeat econstructor
      | _ => idtac end;
    apply low_assn_conj_xs; intros;
    rewrite init_length in H;
    rewrite ls_init_spec; destruct lt_dec; try omega;
    repeat prove_low_assn;       lazymatch goal with
        [|- context [typing_exp _ _ _ ]] => repeat econstructor
      | [|- context [typing_lexp _ _ _ ]] => repeat econstructor
      | _ => idtac end.
    equates 1; [repeat econstructor|].
    repeat instantiate (1 := Lo); auto.
  - unfold Post_j; intros; rewrite MyVector.init_spec.
    repeat has_no_vars_assn;
    apply has_no_vars_conj_xs; intros i; rewrite init_length; intros; rewrite ls_init_spec; destruct lt_dec; try omega;
      repeat has_no_vars_assn.
    apply has_no_vars_is_array_p; cbv; auto.
  - simpl; intros; destruct H; try tauto; subst; eauto.
  - simpl; intros [?|[]]; congruence.
  - simpl; intros [?|[]]; congruence.
Qed.    
End Stencil.