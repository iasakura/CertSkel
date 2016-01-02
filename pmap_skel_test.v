Require Import GPUCSL.
Require Import pmap_skel.
Require Import Skel_lemma.
Require Import scan_lib.
Require Import LibTactics.
Require Import Psatz.

Section verification_example.
  Variable ntrd : nat.
  Variable nblk : nat.
  
  Hypothesis ntrd_neq_0 : ntrd <> 0.
  Hypothesis nblk_neq_0 : nblk <> 0.

  Open Scope list.
  Open Scope string.
  Close Scope exp.
  Eval compute in names_of_arg (grpOfInt 0) 1.
  (* length of the array: shInO, the top address of the array: arrInOO *)
  Definition env := (0, 2) :: nil.
  Notation t0 := (Var "lv10").

  Notation arr0 := (Var "arrInOO").
  Notation arr1 := (Var "arrInSOO").

  Variable len : nat.
  Hypothesis len_neq_0 : len <> 0.
  Variable arr0_ptr : Z.
  Variable arr1_ptr : Z.
  Variable arr0_elms : nat -> Z.
  Variable arr1_elms : nat -> Z.
  Variable out_ptr : Z.
  Variable out_elms : nat -> Z.
  Import ListNotations.
  Open Scope list_scope.
  Definition arr0_elms' i := arr0_elms i :: nil.
  Definition arr1_elms' i := arr1_elms i :: nil.
  Definition out_elms' i := out_elms i :: nil.
  
  Definition env_den := (arr0_ptr :: nil, len, arr0_elms') ::
                        (arr1_ptr :: nil, len, arr1_elms') :: nil.
  Definition out_ptr' := out_ptr :: nil.
  
  Definition default_var := Var "".

  Definition inDim := 2.
  Definition get (x : var) :=
    ( t0 ::= x ;; t1 ::= [Gl arr0 +o x], Evar t0 :: Evar t1 :: nil).

  Definition get_den val := val :: (arr0_elms (Z.to_nat val)) :: nil.

  Definition func (xs : list var) :=
    let in0 := nth 0 xs default_var in
    let in1 := nth 1 xs default_var in
    ( t1 ::= [Gl arr1 +o in0 ], (in1 +C t1) :: nil).

  Definition default_val := 0%Z.

  Definition func_den (vals : list val) :=
    let v0 := nth 0 vals default_val in
    let v1 := nth 1 vals default_val in
    (v1 + arr1_elms (Z.to_nat v0))%Z :: nil.

  Definition outDim := 1.

  Lemma pure_emp stk : stk ||= !(emp) <=> emp.
  Proof.
    split.
    - intros; destruct H; eauto.
    - intros; split; eauto.
  Qed.

  Theorem gen_code_correct :
    CSLg ntrd nblk ntrd_neq_0 nblk_neq_0 
    (!(Outs outDim ==t out_ptr :: nil) **
     !(Len outDim === Zn len) **
     input_spec env env_den 1 **
     is_tuple_array_p (es2gls (vs2es out_ptr')) len out_elms' 0 1)
    {| get_sh_decl := nil;
       get_cmd := map' ntrd nblk inDim outDim get func |}
    (input_spec' env_den 1 **
     is_tuple_array_p (es2gls (vs2es out_ptr')) len (fun v : nat => func_den (get_den (Zn v))) 0 1).
  Proof.
    apply map_correct_g; eauto.
    - cbv; intros.
      repeat split; eauto; intros [? | [? | []]]; congruence.
    - simpl.
      intros ? ? [? | [? | []]]; subst; auto.
    - simpl.
      intros ? ? [? | [? | []]]; subst; auto.
    - simpl.
      intros ? ? ? [? | [? | []]]; subst; simpl; intros [?|[]]; subst; simpl; eauto.
    - intros x nt tid ix Hneq. simpl in *.
      assert (Ht0x : t0 <> x) by eauto.
      assert (Ht1x : t1 <> x) by eauto.
      eapply rule_seq.
      { apply rule_frame.
        hoare_forward.
        - intros s h [v H].
          remember t0.
          subA_normalize_in H with (fun H =>  H).
          assert ((!(t0 === ix) ** !(x === ix)) s h).
          { sep_rewrite_in_r emp_unit_l H; sep_split_in H; sep_split; eauto.
            unfold_conn_all; simpl in *.
            destruct var_eq_dec; try congruence; eauto.
            unfold_conn_all; simpl in *.
            destruct var_eq_dec; simpl in *; try congruence. }
          exact H0.
        - repeat prove_inde. }
      eapply Hbackward.
      Focus 2. { 
        intros s h H.
        sep_split_in H.
        sep_normal_in HP1.
        change_in H.
        { unfold_pures.
          sep_rewrite_in (@is_array_unfold (Gl arr0_ptr) (Z.to_nat ix)) H.
          rewrite <-plus_n_O in H.
          2: zify; rewrite Z2Nat.id; nia.
          rewrite Z2Nat.id in H; [|nia].
          assert ((Gl arr0_ptr +o ix ===l Gl arr0 +o ix) s h).
          { unfold_conn_all; simpl in *; f_equal; omega. }
          sep_rewrite_in mps_eq1 H; [|exact H0].
          sep_normal_in H; exact H. }
        sep_combine_in H.
        exact H. } Unfocus.
      eapply Hforward.
      { hoare_forward; try (destruct var_eq_dec; congruence).
        eauto. }
      intros s h H.
      repeat (try sep_rewrite_r sep_assoc; try sep_rewrite pure_star; try sep_rewrite pure_pure).
      sep_rewrite pure_emp; sep_normal.
      repeat (try sep_rewrite_in_r sep_assoc H; try sep_rewrite_in pure_star H;
              try sep_rewrite_in pure_pure H).
      sep_rewrite_in pure_emp H; sep_normal_in H.
      unfold arr0_elms', fst_of_vals in *; simpl in H.
      sep_normal_in H.
      sep_split; sep_split_in H; eauto.
      unfold_pures.
      sep_rewrite (@is_array_unfold (Gl arr0_ptr) (Z.to_nat ix)); simpl.
      2: zify; rewrite Z2Nat.id; nia.
      sep_normal; sep_cancel.
      rewrite <-plus_n_O, Z2Nat.id; [|nia].
      assert ((Gl arr0_ptr +o ix ===l Gl arr0 +o ix) s h).
      { unfold_conn_all; simpl in *; f_equal; omega. }
      sep_rewrite mps_eq1; [|exact H1].
      repeat sep_cancel.
    - intros; simpl; repeat split; intros [? | ?]; eauto; congruence.
    - simpl; intros u v [? | []]; subst; simpl; eauto.
    - simpl; intros u v [? | []]; subst; simpl; eauto.
    - simpl; intros u v [? | []]; subst; simpl; eauto.
    - simpl; introv Hlen Hdis.
      apply disjoint_comm in Hdis; simpl in Hdis; destruct Hdis as [Hdis _].
      unfold inDim in *.
      destruct var as [|v0 [|v1 [|? ?]]]; simpl in Hlen; try congruence.
      simpl in Hdis.
      assert (Hv0t1 : v0 <> t1) by eauto.
      assert (Hv1t1 : v1 <> t1) by eauto.
      simpl.
      eapply Hbackward.
      Focus 2. {
        intros s h H.
        repeat (try sep_rewrite_in_r sep_assoc H; try sep_rewrite_in pure_star H;
                try sep_rewrite_in pure_pure H);
        repeat sep_rewrite_in pure_emp H; sep_normal_in H.
        exact H. } Unfocus.
      eapply Hforward.
      Focus 2. {
        intros s h H.
        repeat (try sep_rewrite_r sep_assoc; try sep_rewrite pure_star; try sep_rewrite pure_pure);
          sep_rewrite pure_emp; sep_normal.
        exact H. } Unfocus.
      eapply Hbackward.
      Focus 2. { 
        intros s h H.
        sep_split_in H.
        change_in H. {
          unfold_pures.
          sep_rewrite_in (@is_array_unfold (Gl arr1_ptr) (Z.to_nat val)) H; simpl. 
          2: zify; rewrite Z2Nat.id; nia.
          rewrite <-plus_n_O, Z2Nat.id in H; [|nia].
          assert ((Gl arr1_ptr +o val ===l Gl arr1 +o val) s (emp_ph loc)).
          { unfold_conn; simpl; f_equal; congruence. }
          sep_rewrite_in mps_eq1 H; [|exact H0].
          sep_normal_in H; exact H. }
        sep_combine_in H; exact H. } Unfocus.
      eapply Hforward.
      { hoare_forward; simpl in Hdis; [destruct var_eq_dec; try congruence..|].
        intros s h H; sep_normal_in H; eauto. }
      intros s h H; sep_split_in H; sep_split; eauto.
      + unfold_pures; unfold_conn; simpl; eauto.
        unfold fst_of_vals, arr1_elms' in *; simpl in *; congruence.
      + sep_cancel.
        unfold_pures.
        sep_rewrite (@is_array_unfold (Gl arr1_ptr) (Z.to_nat val)); simpl. 
        2: zify; rewrite Z2Nat.id; nia.
        rewrite <-plus_n_O, Z2Nat.id; [|nia].
        assert ((Gl arr1_ptr +o val ===l Gl arr1 +o val) s (emp_ph loc)).
        { unfold_conn; simpl; f_equal; congruence. }
        sep_rewrite mps_eq1; [|exact H1].
        sep_normal; repeat sep_cancel.
  Qed.

  Goal False.
  Proof.
    let t := type of gen_code_correct in pose t.
    simpl in P.
    unfold map', map_ker, WhileI, get, func in P; simpl in P.
  Abort.
End verification_example.

