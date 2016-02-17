Require Import GPUCSL.
Require Import scan_lib.
Require Import LibTactics Psatz.

Section Stencil_seq.
Coercion Var : string >-> var.
(* Local Notation smem := (Var "smem"). *)
(* Local Notation arr := (Var "arr"). *)
(* Local Notation out := (Var "out"). *)
(* Local Notation t0 := (Var "t0"). *)
(* Local Notation t1 := (Var "t1"). *)
(* Local Notation t2 := (Var "t2"). *)
(* Local Notation tid := (Var "tid"). *)
(* Local Notation bid := (Var "bid"). *)

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
Variable f_sm : nat -> Z.
Variable f_out : nat -> Z.

Definition f' k := if Sumbool.sumbool_or _ _ _ _ (le_dec k 0) (lt_dec nt_gr k) then 0%Z else f (k - 1).

Notation gi i j := (nf i + nf j * ntrd).

Definition BS0 (j : Fin.t nblk)  : (Vector.t assn ntrd * Vector.t assn ntrd) := 
  (MyVector.init (fun i =>
    (Sh sloc +o Zn (nf i + 1) -->p (1, f' (gi i j + 1))) **
    (if Nat.eq_dec (nf i) 0 then Sh sloc -->p (1, f' ((nf j) * ntrd)) else emp) **
    (if Nat.eq_dec (nf i) (ntrd - 1) then Sh sloc +o Zn (ntrd + 1) -->p (1, f' ((nf j + 1) * ntrd + 1)) else emp)),
   MyVector.init (fun i =>
    is_array_p (Sh sloc) (ntrd + 2) (fun k => f' (k + nf j * ntrd)) 0 (perm_n ntrd))).

Definition BS (j : Fin.t nblk) (n : nat) :=
  if Nat.eq_dec n 0 then BS0 j else default ntrd.

Lemma stencil_ok_th (j : Fin.t nblk) (i : Fin.t ntrd) :
  CSL (BS j) i 
    (!("tid" === Zn (nf i)) **
     !("bid" === Zn (nf j)) **
     !("arr" === aloc) **
     !("out" === oloc) **
     !("smem" === sloc ) **
     is_array_p (Gl aloc) nt_gr f 0 (perm_n nt_gr) **
     (Gl oloc +o Zn (nf i + nf j * ntrd) -->p (1, f_out (nf i + nf j * ntrd))) **
     (Sh sloc +o Zn (nf i + 1) -->p (1, f_sm (nf i + 1))) **
     (if Nat.eq_dec (nf i) 0 then Sh sloc -->p (1, f_sm 0) else emp) **
     (if Nat.eq_dec (nf i) (ntrd - 1) then Sh sloc +o Zn (ntrd + 1) -->p (1, f_sm (ntrd + 1)) else emp))
    stencil 
    (is_array_p (Gl aloc) nt_gr f 0 (perm_n nt_gr) **
     (Gl oloc +o Zn (gi i j) -->p (1, (f' (gi i j) + f' (gi i j + 1) + f' (gi i j + 2)))%Z) **
     is_array_p (Sh sloc) (ntrd + 2) (fun k => f' (k + nf j * ntrd)) 0 (perm_n ntrd)).
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
    assert (Heq : (Sh sloc +o (Zn (nf i + 1)) ===l Sh "smem" +o ("tid" +C 1%Z)) s (emp_ph loc)).
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
          assert (Heq : (Sh sloc ===l Sh "smem" +o 0%Z) s (emp_ph loc)).
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
          assert (Heq : (Sh sloc ===l Sh "smem" +o 0%Z) s (emp_ph loc)).
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
     (if Nat.eq_dec (nf i) (ntrd - 1) then Sh sloc +o Zn (ntrd + 1) -->p (1, f_sm (ntrd + 1)) else emp)).
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
          assert (Heq : (Sh sloc +o Zn (ntrd + 1) ===l Sh "smem" +o (Zn ntrd +C 1%Z)) s (emp_ph loc)).
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
      assert (Heq : (Sh "smem" +o ("tid" +C 1%Z) ===l Sh sloc +o (Zn (nf i + 1)) ) s (emp_ph loc)).
      { unfold_conn; simpl; f_equal; clear H; unfold lt; nia. }
      sep_lift_in H 2.
      sep_rewrite_in mps_eq1 H; [|apply Heq]; clear Heq.
      assert (Heq : s ||= (if Nat.eq_dec (nf i) 0 then Sh "smem" -->p (1,  f' (nf j * ntrd)) else emp) <=>
                          (if Nat.eq_dec (nf i) 0 then Sh sloc -->p (1,  f' (nf j * ntrd)) else emp)).
      { destruct (Nat.eq_dec _ 0); try reflexivity.
        apply mps_eq1; unfold_conn; simpl; f_equal; nia. }
      sep_rewrite_in Heq H; clear Heq.
      assert (Heq : s ||=
        (if Nat.eq_dec (nf i) (ntrd - 1) then Sh "smem" +o Zn (ntrd + 1) -->p (1,  f' ((nf j + 1) * ntrd + 1)) else emp)
        <=>
        (if Nat.eq_dec (nf i) (ntrd - 1) then Sh sloc +o Zn (ntrd + 1) -->p (1,  f' ((nf j + 1) * ntrd + 1)) else emp)).
      { destruct (Nat.eq_dec _ (ntrd - 1)); try reflexivity.
        apply mps_eq1; unfold_conn; simpl; f_equal; nia. }
      sep_rewrite_in Heq H; clear Heq.
      apply H. }
    sep_normal_in H0; do 2 sep_cancel.
    sep_combine_in H1; apply H1. }
  unfold BS at 2, BS0; simpl; rewrite MyVector.init_spec.
  eapply Hbackward.
  Focus 2. { 
    intros s h H.
    sep_split_in H.
    sep_rewrite_in (@is_array_unfold (Sh sloc) (nf i)) H; [|destruct (Fin.to_nat i); clear H; simpl; omega].
    sep_normal_in H.
    sep_lift_in H 2; sep_rewrite_in (@is_array_unfold (Sh sloc) 0) H; [|destruct (Fin.to_nat i); clear H; simpl; omega].
    sep_normal_in H.
    sep_lift_in H 2; sep_rewrite_in (@is_array_unfold (Sh sloc) 0) H; [|destruct (Fin.to_nat i); clear H; simpl; omega].
    sep_normal_in H.
    change_in H.
    { unfold_pures.
      assert (Heq : (Sh sloc +o Zn (0 + S (0 + S (nf i + 0))) ===l Sh sloc +o ("tid" +C 2%Z)) s (emp_ph loc)).
      { rewrite !plus_O_n, <-plus_n_O, !Nat2Z.inj_succ, <-!Z.add_1_r.
        unfold_conn; simpl; f_equal; clear H; unfold lt; omega. }
      sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
      assert (Heq : (Sh sloc +o Zn (0 + S (nf i + 0)) ===l Sh sloc +o ("tid" +C 1%Z)) s (emp_ph loc)).
      { rewrite !plus_O_n, <-plus_n_O, !Nat2Z.inj_succ, <-!Z.add_1_r.
        unfold_conn; simpl; f_equal; clear H; unfold lt; omega. }
      sep_lift_in H 4; sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
      assert (Heq : (Sh sloc +o Zn (nf i + 0) ===l Sh sloc +o "tid") s (emp_ph loc)).
      { unfold_conn; simpl; f_equal; clear H; unfold lt in *; nia. }
      sep_lift_in H 6; sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
      assert (Heq : (Gl oloc +o Zn (gi i j) ===l Gl oloc +o gid) s (emp_ph loc)).
      { unfold_conn; simpl; f_equal; clear H; unfold lt in *; nia. }
      sep_lift_in H 8; sep_rewrite_in mps_eq1 H; [|exact Heq]; clear Heq.
      apply H. } 
    sep_combine_in H; apply H. } Unfocus.
  repeat (eapply rule_seq; [hoare_forward; eauto|]).
  eapply Hforward; [hoare_forward; eauto|].
  intros s h H.
  sep_split_in H; sep_cancel.
  unfold_pures.
  sep_rewrite (@is_array_unfold (Sh sloc) (nf i)); [|destruct (Fin.to_nat i); clear H; simpl; omega].
  sep_normal.
  sep_lift 3; sep_rewrite (@is_array_unfold (Sh sloc) 0); [|destruct (Fin.to_nat i); clear H; simpl; omega].
  sep_normal.
  sep_lift 2. sep_rewrite (@is_array_unfold (Sh sloc) 0). 2: destruct (Fin.to_nat i). 2: clear H H0. 2: simpl.
  2: generalize dependent x. 2: clear. 2: intros. 2: omega.
  sep_normal_in H0. clear H. sep_normal.
  assert (Heq : (Sh sloc +o Zn (0 + S (0 + S (nf i + 0))) ===l Sh "smem" +o ("tid" +C 2%Z)) s (emp_ph loc)).
  { rewrite !plus_O_n, <-plus_n_O, !Nat2Z.inj_succ, <-!Z.add_1_r.
    unfold_conn; simpl; f_equal; unfold lt; omega. }
  sep_rewrite mps_eq1; [|exact Heq]; clear Heq.
  assert (Heq : (Sh sloc +o Zn (0 + S (nf i + 0)) ===l Sh "smem" +o ("tid" +C 1%Z)) s (emp_ph loc)).
  { rewrite !plus_O_n, <-plus_n_O, !Nat2Z.inj_succ, <-!Z.add_1_r.
    unfold_conn; simpl; f_equal; unfold lt; omega. }
  sep_lift 4; sep_rewrite mps_eq1; [|exact Heq]; clear Heq.
  assert (Heq : (Sh sloc +o Zn (nf i + 0) ===l Sh "smem" +o "tid") s (emp_ph loc)).
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
Section Stencil_seq.